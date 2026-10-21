{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings   #-}

-- |
-- A content-addressed, append-only log for spilled proof state.
--
--   > ["tamarin-store-v5\n"]
--   > [kind : 1B][key : 32B][len : 8B BE][payload]
--
-- Values hash their payload. Method edges and lemma roots hash the subject
-- used to look them up. Method edges are scoped by lemma, so lemmas that reach
-- the same system do not share proof steps. The kind is included in both hashes.
--
-- One MVar serializes writes. Readers use pread and do not take the lock.
-- The index is published only after a complete record was written.
--
-- On startup we scan the log and truncate an incomplete tail. We do not
-- provide power-loss durability or continue after a write error.
--
-- The store is global because the prover does not expose an IO handle.
module Theory.Constraint.Solver.Store
  ( Ref
  , refText
  , Kind(..)
  , initStore
  , closeStore
  , isStoreOpen
  , storeSystem
  , readSystemLive
  , readSystemLiveMaybe
  , StoredRecord(..)
  , readStoreRecords
  , writeStoreJSON
  , decodeStoredRecord
  , valueRef
  , MethodEdge(..)
  , searchContextForDepth
  , searchKey
  , storeProofStep
  , readProofStepMaybe
  , SearchStart(..)
  , recordSearchStart
  , readSearchStartAfter
  , LemmaRoot(..)
  , recordLemmaRoot
  , readLemmaRootMaybe
  , ProofNode(..)
  , ProofHead(..)
  , storeProofNode
  , readProofNode
  , recordProofHead
  , readMatchingProofRootMaybe
  , restoreStoredProof
  , fileProofRef
  , setTheoryContext
  ) where

import           Theory.Constraint.System
import           Theory.Model
import           Theory.Constraint.Solver.JSON ()   -- ToJSON for the System closure
import           Theory.Constraint.Solver.ProofMethod (ProofMethod(..), CaseName)
import           Control.DeepSeq         (NFData (rnf))
import qualified Data.Label              as L

import           Control.Concurrent.MVar (MVar, modifyMVarMasked, newMVar)
import           Control.Exception       (evaluate, onException)
import           Control.Monad           (unless, when)
import           Crypto.Hash             (Digest, SHA256, hashlazy)
import           Data.Aeson              (ToJSON, object, (.=))
import qualified Data.Aeson              as A
import qualified Data.Binary             as Bin
import           Data.Binary.Get         (getByteString)
import           Data.Binary.Put         (putByteString)
import qualified Data.ByteArray          as BA
import qualified Data.ByteString         as BS
import qualified Data.ByteString.Builder as BB
import qualified Data.ByteString.Lazy    as BL
import           Data.IORef              (IORef, atomicWriteIORef, newIORef,
                                          readIORef, writeIORef)
import           Data.Word               (Word64)
import           GHC.Generics            (Generic)
import           GHC.IO.Handle.Lock      (LockMode (ExclusiveLock), hTryLock)
import qualified Data.Map                as M
import qualified Data.Set                as S
import qualified Data.Text               as T
import qualified Data.Text.Encoding      as TE
import           System.Directory        (createDirectoryIfMissing)
import           System.FilePath         ((</>))
import           System.IO               (Handle, IOMode (ReadWriteMode),
                                          SeekMode (AbsoluteSeek), hClose,
                                          hFileSize, hFlush, hSeek,
                                          hSetFileSize, openFile)
import           System.IO.Unsafe        (unsafePerformIO)
import           System.Posix.Files      (setFdSize)
import           System.Posix.IO         (closeFd, handleToFd)
import           System.Posix.IO.ByteString.Ext (fdPread, fdPwrite)
import           System.Posix.Types      (ByteCount, Fd, FileOffset)

-- | A raw SHA-256 key. 'refText' renders it as hex.
newtype Ref = Ref BS.ByteString
  deriving (Eq, Ord)

instance Show Ref where show = T.unpack . refText

-- | Render a ref as hex.
refText :: Ref -> T.Text
refText (Ref keyBytes) =
    TE.decodeUtf8 (BL.toStrict (BB.toLazyByteString (BB.byteStringHex keyBytes)))

instance ToJSON Ref where toJSON = A.toJSON . refText

instance NFData Ref where rnf (Ref keyBytes) = rnf keyBytes

-- Refs use their raw 32 bytes in binary payloads.
instance Bin.Binary Ref where
  put (Ref keyBytes) = putByteString keyBytes
  get = Ref <$> getByteString refByteCount

refByteCount :: Int
refByteCount = 32

-- | Record type. The kind is also included in the key hash.
data Kind
  = KNode          -- ^ one element of '_sNodes' (a rule instance)
  | KGoal          -- ^ one key of '_sGoals'
  | KEdge          -- ^ one element of '_sEdges'
  | KLessAtom      -- ^ one element of '_sLessAtoms'
  | KFormulas      -- ^ a whole formula set ('_sFormulas' etc.)
  | KSubtermStore  -- ^ the whole '_sSubtermStore'
  | KEqStore       -- ^ the whole '_sEqStore'
  | KShell         -- ^ a spilled system (heavy fields as refs)
  | KMethodEdge    -- ^ applied method + case refs, keyed by search context and parent system
  | KLemmaRoot     -- ^ lemma name -> root system and metadata, keyed by the name
  | KTheoryContext  -- ^ the theory context every tree in this store was built against
  | KProofNode     -- ^ one step of a stored proof tree, with its children's node refs
  | KProofHead     -- ^ lemma name -> root node of its latest stored proof, keyed by the name
  | KSearchStart   -- ^ lemma name and start system -> key of the search's first step
  deriving (Eq, Ord, Show, Enum, Bounded)

kindTag :: Kind -> T.Text
kindTag KNode         = "node"
kindTag KGoal         = "goal"
kindTag KEdge         = "edge"
kindTag KLessAtom     = "lessAtom"
kindTag KFormulas     = "formulas"
kindTag KSubtermStore = "subtermStore"
kindTag KEqStore      = "eqStore"
kindTag KShell        = "shell"
kindTag KMethodEdge   = "methodEdge"
kindTag KLemmaRoot    = "lemmaRoot"
kindTag KTheoryContext = "theoryContext"
kindTag KProofNode    = "proofNode"
kindTag KProofHead    = "proofHead"
kindTag KSearchStart  = "searchStart"

theoryContextKey :: Ref
theoryContextKey = keyOf KTheoryContext (Bin.encode ("theory-context" :: String))

setTheoryContext :: Ref -> IO Bool
setTheoryContext fingerprint = do
  existing <- readKeyedMaybe theoryContextKey
  case existing of
    -- Check if the provided theory context matches the existing one
    Just storedFingerprint -> pure (storedFingerprint == fingerprint)
    Nothing                -> do
      -- Only a fresh store can safely adopt a context. Older batch stores may
      -- contain unscoped method edges without a context record; accepting one
      -- of those would allow stale proof steps to be replayed.
      store <- requireStore
      index <- readIORef store.storeIndex
      if M.null index
        then do
          writeKeyed KTheoryContext theoryContextKey fingerprint
          pure True
        else
          pure False

-- | Hash bytes in a kind-specific namespace.
keyOf :: Kind -> BL.ByteString -> Ref
keyOf kind bytes =
    Ref (BA.convert (hashlazy (Bin.encode (kindTag kind) <> bytes) :: Digest SHA256))

-- | Compute the content-addressed key used for a stored value.
valueRef :: Bin.Binary a => Kind -> a -> Ref
valueRef kind = keyOf kind . Bin.encode

-- | Offset and size of a complete record, including its header.
data RecordLocation = RecordLocation
  { recordOffset :: !Word64
  , recordSize   :: !Word64
  }

-- | Parsed record header, shared by recovery and JSON export.
data RecordHeader = RecordHeader
  { headerKind          :: !Kind
  , headerKey           :: !Ref
  , headerPayloadLength :: !Word64
  }

-- | The MVar serializes writes and owns the append offset. Readers access
-- the immutable index snapshot and use positional reads.
data Store = Store
  { storeFd           :: !Fd
  , storeAppendOffset :: !(MVar Word64)
  , storeIndex        :: !(IORef (M.Map Ref RecordLocation))
  }

-- | Path to the binary log.
storePath :: FilePath -> FilePath
storePath dir = dir </> "store.bin"

-- | Identifies the binary layout before any records are read.
storeVersionHeader :: BS.ByteString
storeVersionHeader = "tamarin-store-v5\n"

storeVersionHeaderSize :: Word64
storeVersionHeaderSize = fromIntegral (BS.length storeVersionHeader)

-- | Process-global store, initialized by the CLI.
{-# NOINLINE globalStore #-}
globalStore :: IORef (Maybe Store)
globalStore = unsafePerformIO (newIORef Nothing)

-- | Open the log, rebuild the index, and truncate a torn tail.
initStore :: FilePath -> IO ()
initStore dir = do
    existing <- readIORef globalStore
    case existing of
      Just _  -> error "initStore: store already initialized"
      Nothing -> do
        createDirectoryIfMissing True dir
        fileHandle <- openFile (storePath dir) ReadWriteMode
        gotLock <- hTryLock fileHandle ExclusiveLock
        unless gotLock $ do
          hClose fileHandle
          ioError (userError ("initStore: " ++ storePath dir
                              ++ " is in use by another tamarin process"))
        originalFileEnd <- fromIntegral <$> hFileSize fileHandle
        fileEnd <- if originalFileEnd == 0
          then do
            BS.hPut fileHandle storeVersionHeader
            hFlush fileHandle
            pure storeVersionHeaderSize
          else do
            validateStoreHeader fileHandle originalFileEnd
            pure originalFileEnd
        (index, validEnd) <- scanIndex fileHandle fileEnd

        -- Remove bytes left by an incomplete / unrecoverable record
        when (validEnd < fileEnd) $ hSetFileSize fileHandle (fromIntegral validEnd)
        fd <- handleToFd fileHandle   -- consumes the Handle; the fd keeps the lock
        appendOffsetVar <- newMVar validEnd
        indexRef        <- newIORef index
        writeIORef globalStore (Just (Store fd appendOffsetVar indexRef))

-- | Reject stores written with another binary layout without modifying them.
validateStoreHeader :: Handle -> Word64 -> IO ()
validateStoreHeader fileHandle fileSize = do
    hSeek fileHandle AbsoluteSeek 0
    actualHeader <- BS.hGet fileHandle (BS.length storeVersionHeader)
    unless (fileSize >= storeVersionHeaderSize
            && actualHeader == storeVersionHeader) $ do
      hClose fileHandle
      ioError (userError ("initStore: incompatible store.bin; expected "
                          ++ show storeVersionHeader))

-- | Rebuild the index from record headers. Stop at the first incomplete
-- record and return the end of the valid prefix.
scanIndex :: Handle -> Word64 -> IO (M.Map Ref RecordLocation, Word64)
scanIndex fileHandle fileSize = scanFromOffset storeVersionHeaderSize M.empty
  where
    -- Walk complete records from left to right. The offset returned here is
    -- where the next append should start.
    scanFromOffset :: Word64
                   -> M.Map Ref RecordLocation
                   -> IO (M.Map Ref RecordLocation, Word64)
    scanFromOffset currentOffset indexSoFar
      | currentOffset + recordHeaderSize64 > fileSize =
          pure (indexSoFar, currentOffset)
      | otherwise = do
          hSeek fileHandle AbsoluteSeek (fromIntegral currentOffset)
          headerBytes <- BS.hGet fileHandle recordHeaderSize
          case decodeRecordHeader headerBytes of
            Nothing ->
              pure (indexSoFar, currentOffset)
            Just header -> do
              let payloadLength = header.headerPayloadLength
                  payloadBytesAvailable =
                    fileSize - currentOffset - recordHeaderSize64
              if payloadLength > payloadBytesAvailable
                then pure (indexSoFar, currentOffset)
                else do
                  let completeRecordSize = recordHeaderSize64 + payloadLength
                      nextOffset = currentOffset + completeRecordSize
                      location = RecordLocation currentOffset completeRecordSize
                      updatedIndex =
                        M.insert header.headerKey location indexSoFar
                  scanFromOffset nextOffset updatedIndex

-- | Close the store. Only call this after all store operations finished.
closeStore :: IO ()
closeStore = do
    existing <- readIORef globalStore
    case existing of
      Nothing    -> pure ()
      Just store -> do
        writeIORef globalStore Nothing
        closeFd store.storeFd

-- | Check whether this process has initialized a store.
isStoreOpen :: IO Bool
isStoreOpen = do
    existing <- readIORef globalStore
    pure $ case existing of
      Nothing -> False
      Just _  -> True

-- | Get the open store.
requireStore :: IO Store
requireStore = do
    existing <- readIORef globalStore
    case existing of
      Nothing    -> error "store not initialized (did you pass --persist-proof-state?)"
      Just store -> pure store

-- | Store a value once, keyed by its content hash.
writeOnce :: Bin.Binary a => Kind -> a -> IO Ref
writeOnce kind value = do
    let payload = Bin.encode value
        ref     = keyOf kind payload

    -- Force the hash before taking the writer lock.
    _ <- evaluate ref

    store <- requireStore
    modifyMVarMasked store.storeAppendOffset $ \appendOffset -> do
      index <- readIORef store.storeIndex
      -- Check again under the lock in case another thread wrote it first.
      if M.member ref index
        then pure (appendOffset, ref)
        else do
          location <- appendRecord store index appendOffset kind ref payload
          pure (appendOffset + location.recordSize, ref)

-- | Store a subject-addressed record
writeKeyed :: Bin.Binary a => Kind -> Ref -> a -> IO ()
writeKeyed kind key value = do
    let payload = Bin.encode value

    -- Force computations before we take the lock
    _ <- evaluate key
    _ <- evaluate (BL.length payload)
    store <- requireStore

    -- Lock: storeAppendOffset
    modifyMVarMasked store.storeAppendOffset $ \appendOffset -> do
      index <- readIORef store.storeIndex
      location <- appendRecord store index appendOffset kind key payload
      pure (appendOffset + location.recordSize, ())

-- | Append one record and publish it after the complete write.
appendRecord :: Store
             -> M.Map Ref RecordLocation
             -> Word64
             -> Kind
             -> Ref
             -> BL.ByteString
             -> IO RecordLocation
appendRecord store index appendOffset kind key payload = do
    let framedRecord = encodeRecord kind key payload
        location     = RecordLocation appendOffset
                                       (fromIntegral (BL.length framedRecord))
    writeToFile store.storeFd (fromIntegral appendOffset) framedRecord
      `onException` setFdSize store.storeFd (fromIntegral appendOffset)
    atomicWriteIORef store.storeIndex $! M.insert key location index
    pure location

-- | Encode one @[kind][key][length][payload]@ record.
encodeRecord :: Kind -> Ref -> BL.ByteString -> BL.ByteString
encodeRecord kind (Ref keyBytes) payload = BL.concat
    [ BL.singleton (fromIntegral (fromEnum kind))
    , BL.fromStrict keyBytes
    , Bin.encode (fromIntegral (BL.length payload) :: Word64)
    , payload
    ]

-- Fixed header layout.
kindByteCount, payloadLengthByteCount, recordHeaderSize :: Int
kindByteCount          = 1
payloadLengthByteCount = 8
recordHeaderSize       = kindByteCount + refByteCount + payloadLengthByteCount

recordHeaderSize64 :: Word64
recordHeaderSize64 = fromIntegral recordHeaderSize

keyFieldOffset, payloadLengthFieldOffset :: Int
keyFieldOffset           = kindByteCount
payloadLengthFieldOffset = kindByteCount + refByteCount

-- | Decode the fixed-width header.
decodeRecordHeader :: BS.ByteString -> Maybe RecordHeader
decodeRecordHeader bytes
  | BS.length bytes /= recordHeaderSize = Nothing
  | kindNumber > fromEnum (maxBound :: Kind) = Nothing
  | otherwise = Just RecordHeader
      { headerKind          = toEnum kindNumber
      , headerKey           = Ref keyBytes
      , headerPayloadLength = payloadLength
      }
  where
    kindNumber = fromIntegral (BS.head bytes)
    keyBytes = BS.take refByteCount (BS.drop keyFieldOffset bytes)
    payloadLength = Bin.decode
                  $ BL.fromStrict
                  $ BS.drop payloadLengthFieldOffset bytes

-- | Write the complete lazy ByteString, retrying any short writes.
writeToFile :: Fd -> FileOffset -> BL.ByteString -> IO ()
writeToFile fd initialOffset bytes =
    writeChunks initialOffset (BL.toChunks bytes)
  where
    writeChunks :: FileOffset -> [BS.ByteString] -> IO ()
    writeChunks _ [] = pure ()
    writeChunks offset (currentChunk : laterChunks)
      | BS.null currentChunk = writeChunks offset laterChunks
      | otherwise = do
          bytesWritten <- fdPwrite fd currentChunk offset
          when (bytesWritten == 0) $
            error "writeToFile: write made no progress (disk full?)"
          let writtenByteCount = fromIntegral bytesWritten
              nextOffset = offset + fromIntegral bytesWritten
              unwrittenPart = BS.drop writtenByteCount currentChunk
              remainingChunks
                | BS.null unwrittenPart = laterChunks
                | otherwise = unwrittenPart : laterChunks
          writeChunks nextOffset remainingChunks

-- | Read exactly the requested byte range.
readFileAt :: Fd -> FileOffset -> ByteCount -> IO BS.ByteString
readFileAt fd initialOffset requestedBytes =
    BS.concat . reverse <$> readRemaining initialOffset requestedBytes []
  where
    readRemaining _ 0 chunksReversed = pure chunksReversed
    readRemaining offset bytesRemaining chunksReversed = do
      chunk <- fdPread fd bytesRemaining offset
      when (BS.null chunk) $
        error "readFileAt: unexpected end of file (index/store mismatch)"
      let bytesRead = BS.length chunk
      readRemaining (offset + fromIntegral bytesRead)
                    (bytesRemaining - fromIntegral bytesRead)
                    (chunk : chunksReversed)

-- | Read a record and remove its header.
readRecordPayloadAt :: Store -> RecordLocation -> IO BL.ByteString
readRecordPayloadAt store location = do
    recordBytes <- readFileAt store.storeFd
                                 (fromIntegral location.recordOffset)
                                 (fromIntegral location.recordSize)
    pure (BL.fromStrict (BS.drop recordHeaderSize recordBytes))

-- | Read a record payload by key.
readRecord :: Ref -> IO BL.ByteString
readRecord ref = do
    store <- requireStore
    index <- readIORef store.storeIndex
    case M.lookup ref index of
      Nothing       -> error ("readRecord: no record for ref " ++ show ref)
      Just location -> readRecordPayloadAt store location

-- | Read a system if the store is open.
readSystemLiveMaybe :: Ref -> IO (Maybe System)
readSystemLiveMaybe ref = do
    existing <- readIORef globalStore
    case existing of
      Nothing -> pure Nothing
      Just _  -> Just <$> readSystemLive ref

-- | Rebuild a System from its shell and referenced fields.
readSystemLive :: Ref -> IO System
readSystemLive shellRef = do
    shell    <- deref shellRef :: IO SystemShell
    nodes    <- traverse deref shell.shNodes
    goals    <- mapM derefGoal shell.shGoals
    edges    <- mapM deref shell.shEdges
    lessAts  <- mapM deref shell.shLessAtoms
    subterms <- deref shell.shSubtermStore
    eqStore  <- deref shell.shEqStore
    formulas <- deref shell.shFormulas
    solved   <- deref shell.shSolvedFormulas
    lemmas   <- deref shell.shLemmas
    pure System
      { _sNodes          = nodes
      , _sEdges          = S.fromList edges
      , _sLessAtoms      = S.fromList lessAts
      , _sLastAtom       = shell.shLastAtom
      , _sSubtermStore   = subterms
      , _sEqStore        = eqStore
      , _sFormulas       = formulas
      , _sSolvedFormulas = solved
      , _sLemmas         = lemmas
      , _sGoals          = M.fromList goals
      , _sNextGoalNr     = shell.shNextGoalNr
      , _sSourceKind     = shell.shSourceKind
      , _sDiffSystem     = shell.shDiffSystem
      }
  where
    deref :: Bin.Binary a => Ref -> IO a
    deref ref = do
        payload <- readRecord ref
        decodePayload ref payload

    derefGoal (goalRef, status) = do
        goal <- deref goalRef
        pure (goal, status)

-- | Decode a stored payload or report which ref was invalid.
decodePayload :: Bin.Binary a => Ref -> BL.ByteString -> IO a
decodePayload ref payload = case Bin.decodeOrFail payload of
    Left (_, _, decodeError) ->
      error ("binary decode of " ++ show ref ++ ": " ++ decodeError)
    Right (_, _, value) ->
      pure value

-- storing systems

-- | A System with its larger fields replaced by refs.
data SystemShell = SystemShell
  { shNodes          :: M.Map NodeId Ref
  , shEdges          :: [Ref]
  , shLessAtoms      :: [Ref]
  , shLastAtom       :: Maybe NodeId
  , shSubtermStore   :: Ref
  , shEqStore        :: Ref
  , shFormulas       :: Ref
  , shSolvedFormulas :: Ref
  , shLemmas         :: Ref
  , shGoals          :: [(Ref, GoalStatus)]
  , shNextGoalNr     :: Integer
  , shSourceKind     :: SourceKind
  , shDiffSystem     :: Bool
  }
  deriving (Generic)

instance Bin.Binary SystemShell

-- Keep JSON keys aligned with System fields.
instance ToJSON SystemShell where
  toJSON shell = object
    [ "_sNodes"          .= shell.shNodes
    , "_sEdges"          .= shell.shEdges
    , "_sLessAtoms"      .= shell.shLessAtoms
    , "_sLastAtom"       .= shell.shLastAtom
    , "_sSubtermStore"   .= shell.shSubtermStore
    , "_sEqStore"        .= shell.shEqStore
    , "_sFormulas"       .= shell.shFormulas
    , "_sSolvedFormulas" .= shell.shSolvedFormulas
    , "_sLemmas"         .= shell.shLemmas
    , "_sGoals"          .= shell.shGoals
    , "_sNextGoalNr"     .= shell.shNextGoalNr
    , "_sSourceKind"     .= shell.shSourceKind
    , "_sDiffSystem"     .= shell.shDiffSystem
    ]

-- | Store a System and return its shell ref.
storeSystem :: System -> IO Ref
storeSystem system = do
    nodeRefs    <- traverse (writeOnce KNode) system._sNodes
    goalRefs    <- mapM storeGoal (M.toList system._sGoals)
    edgeRefs    <- mapM (writeOnce KEdge)     (S.toList system._sEdges)
    lessRefs    <- mapM (writeOnce KLessAtom) (S.toList system._sLessAtoms)
    formulasRef <- writeOnce KFormulas     system._sFormulas
    solvedRef   <- writeOnce KFormulas     system._sSolvedFormulas
    lemmasRef   <- writeOnce KFormulas     system._sLemmas
    subtermRef  <- writeOnce KSubtermStore system._sSubtermStore
    eqRef       <- writeOnce KEqStore      system._sEqStore
    let shell = SystemShell
          { shNodes          = nodeRefs
          , shEdges          = edgeRefs
          , shLessAtoms      = lessRefs
          , shLastAtom       = system._sLastAtom
          , shSubtermStore   = subtermRef
          , shEqStore        = eqRef
          , shFormulas       = formulasRef
          , shSolvedFormulas = solvedRef
          , shLemmas         = lemmasRef
          , shGoals          = goalRefs
          , shNextGoalNr     = system._sNextGoalNr
          , shSourceKind     = system._sSourceKind
          , shDiffSystem     = system._sDiffSystem
          }
    writeOnce KShell shell
  where
    storeGoal (goal, status) = do
        goalRef <- writeOnce KGoal goal
        pure (goalRef, status)

-- method edges

-- | The selected method and all child cases for one system in one lemma.
data MethodEdge = MethodEdge
  { meLemma     :: String
  , meParent    :: Ref                 -- ^ the parent system's ref
  , meMethod    :: ProofMethod
  , meChildren  :: M.Map CaseName Ref  -- ^ child system refs, not proof node refs
  , meChildKeys :: M.Map CaseName Ref  -- ^ the key each child's step is stored under
  } deriving (Generic)

instance Bin.Binary MethodEdge

instance ToJSON MethodEdge where
  toJSON edge = object [ "lemma"     .= edge.meLemma
                       , "subject"   .= edge.meParent
                       , "method"    .= show edge.meMethod
                       , "children"  .= edge.meChildren
                       , "childKeys" .= edge.meChildKeys ]

-- | Prepare the search-context hashes once, then select one by proof depth.
-- Each heuristic slot has its own shared hash because it can choose a
-- different method for the same system.
searchContextForDepth :: Heuristic ProofContext -> [Tactic ProofContext]
                      -> ProofContext -> Int -> Ref
searchContextForDepth heuristic tactics ctxt = contextAtDepth
  where
    Heuristic rankings = heuristic
    rankingCount = length rankings
    slotContexts = map contextForSlot [0 .. rankingCount - 1]

    contextForSlot slot =
        let lemmaName = L.get pcLemmaName ctxt
            useInduction = L.get pcUseInduction ctxt
            traceQuantifier = L.get pcTraceQuantifier ctxt
            hiddenLemmas = L.get pcHiddenLemmas ctxt
            sourceKind = L.get pcSourceKind ctxt
            searchSettings = ( lemmaName, useInduction, traceQuantifier
                             , hiddenLemmas, sourceKind, heuristic, tactics, slot )
            taggedContext = ("search-context" :: String, searchSettings)
        in keyOf KMethodEdge (Bin.encode taggedContext)

    contextAtDepth depth =
        let slot = depth `mod` rankingCount
        in slotContexts !! slot

-- | Derive the lookup key for a system's method edge in a search context.
searchKey :: Ref -> Ref -> Ref
searchKey contextRef systemRef =
    let searchStep = (contextRef, systemRef)
    in keyOf KMethodEdge (Bin.encode searchStep)

-- | Record a search step. Prepare this function with the lemma and its context
-- selector once; each call then supplies the depth, system, method and children.
storeProofStep :: String -> (Int -> Ref) -> Int -> Ref -> ProofMethod
               -> M.Map CaseName Ref -> IO ()
storeProofStep lemmaName contextAtDepth depth parentSystemRef method childSystemRefs = do
    let searchStepKey = searchKey (contextAtDepth depth) parentSystemRef
        childContextRef = contextAtDepth (succ depth)
        childSearchKeys = M.map (searchKey childContextRef) childSystemRefs
        methodEdge = MethodEdge
          { meLemma = lemmaName
          , meParent = parentSystemRef
          , meMethod = method
          , meChildren = childSystemRefs
          , meChildKeys = childSearchKeys
          }

    writeKeyed KMethodEdge searchStepKey methodEdge

-- | Read the stored proof step, if present.
readProofStepMaybe :: Ref -> IO (Maybe MethodEdge)
readProofStepMaybe searchStepKey = readKeyedMaybe searchStepKey

-- search starts

-- | A search of a lemma that started at a system, and its first step's key.
data SearchStart = SearchStart
  { ssLemma  :: String
  , ssSystem :: Ref  -- ^ the system where the search starts
  , ssKey    :: Ref  -- ^ the first method edge's search key
  } deriving (Generic)

instance Bin.Binary SearchStart

instance ToJSON SearchStart where
  toJSON start = object
    [ "lemma"  .= start.ssLemma
    , "system" .= start.ssSystem
    , "key"    .= start.ssKey
    ]

-- | Derive the lookup key for the searches of a lemma started at a system.
searchStartKey :: String -> Ref -> Ref
searchStartKey lemmaName systemRef =
    keyOf KSearchStart (Bin.encode (lemmaName, systemRef))

-- | Record that a search starts at a system. The newest record counts.
recordSearchStart :: String -> Ref -> Ref -> IO ()
recordSearchStart lemmaName systemRef searchStepKey =
    let key = searchStartKey lemmaName systemRef
        searchStart = SearchStart
          { ssLemma  = lemmaName
          , ssSystem = systemRef
          , ssKey    = searchStepKey
          }
    in writeKeyed KSearchStart key searchStart

-- | The first step's key of the newest search started at a system, if that
-- search started after the record at the given offset.
readSearchStartAfter :: Word64 -> String -> Ref -> IO (Maybe Ref)
readSearchStartAfter savedProofOffset lemmaName systemRef = do
    let key = searchStartKey lemmaName systemRef

    storedStart <- readKeyedAtMaybe key

    let newerSearchKey = case storedStart of
          Nothing -> Nothing
          Just (startOffset, SearchStart _ _ searchStepKey) ->
            if startOffset > savedProofOffset
              then Just searchStepKey
              else Nothing

    pure newerSearchKey

-- lemma roots

-- | A lemma name and its root system.
data LemmaRoot = LemmaRoot
  { lrLemma           :: String
  , lrTraceQuantifier :: SystemTraceQuantifier
  , lrRoot            :: Ref  -- ^ root system ref
  , lrFileProof       :: Ref  -- ^ 'fileProofRef' of the lemma's proof in the theory
  } deriving (Eq, Generic)

instance Bin.Binary LemmaRoot

instance ToJSON LemmaRoot where
  toJSON root = object
    [ "lemma" .= root.lrLemma
    , "traceQuantifier" .= show root.lrTraceQuantifier
    , "root" .= root.lrRoot
    , "fileProof" .= root.lrFileProof
    ]

-- | Derive the lookup key for a lemma root.
rootKey :: String -> Ref
rootKey lemmaName = keyOf KLemmaRoot (Bin.encode lemmaName)

-- | Record a lemma's root system and metadata, unless the record is unchanged.
recordLemmaRoot :: String -> SystemTraceQuantifier -> Ref -> Ref -> IO ()
recordLemmaRoot lemmaName traceQuantifier rootSystemRef inputProofRef = do
    storedRoot <- readLemmaRootMaybe lemmaName

    let lemmaRoot = LemmaRoot
          { lrLemma           = lemmaName
          , lrTraceQuantifier = traceQuantifier
          , lrRoot            = rootSystemRef
          , lrFileProof       = inputProofRef
          }

    if storedRoot == Just lemmaRoot
      then pure ()
      else writeKeyed KLemmaRoot (rootKey lemmaName) lemmaRoot

-- | Read a lemma root, if present.
readLemmaRootMaybe :: String -> IO (Maybe LemmaRoot)
readLemmaRootMaybe lemmaName = readKeyedMaybe (rootKey lemmaName)

-- proof trees

-- | One step of a stored proof. Its ref hashes its method, system ref and
-- child proof node refs. Equal systems can therefore have different proof
-- nodes, while identical complete subtrees share the same proof node ref.
-- Children are stored before their parents; a node does not point back to
-- itself just because a child has the same system.
data ProofNode = ProofNode
  { pnMethod   :: ProofMethod
  , pnSystem   :: Maybe Ref           -- ^ a system ref, when this step has a system
  , pnChildren :: M.Map CaseName Ref  -- ^ child proof node refs, not system refs
  } deriving (Generic)

instance Bin.Binary ProofNode

instance ToJSON ProofNode where
  toJSON node = object
    [ "method"   .= show node.pnMethod
    , "system"   .= node.pnSystem
    , "children" .= node.pnChildren
    ]

-- | The root node of a lemma's latest stored proof.
data ProofHead = ProofHead
  { phLemma   :: String
  , phRoot    :: Ref  -- ^ the root proof node's ref, not its system's ref
  , phBasedOn :: Ref  -- ^ the lemma root's file proof when the proof was stored
  } deriving (Generic)

instance Bin.Binary ProofHead

instance ToJSON ProofHead where
  toJSON proofHead = object
    [ "lemma"   .= proofHead.phLemma
    , "root"    .= proofHead.phRoot
    , "basedOn" .= proofHead.phBasedOn
    ]

-- | Store a proof node once and return its Ref.
storeProofNode :: ProofNode -> IO Ref
storeProofNode proofNode = writeOnce KProofNode proofNode

-- | Read a proof node, if present.
readProofNode :: Ref -> IO (Maybe ProofNode)
readProofNode proofNodeRef = readKeyedMaybe proofNodeRef

-- | Derive the lookup key for a lemma's proof head.
headKey :: String -> Ref
headKey lemmaName = keyOf KProofHead (Bin.encode lemmaName)

-- | Make a stored proof the lemma's current proof. Its nodes must be stored.
recordProofHead :: String -> Ref -> Ref -> IO ()
recordProofHead lemmaName rootProofNodeRef inputProofRef =
    let proofHead = ProofHead
          { phLemma   = lemmaName
          , phRoot    = rootProofNodeRef
          , phBasedOn = inputProofRef
          }
    in writeKeyed KProofHead (headKey lemmaName) proofHead

-- | Read a lemma's saved root node and its head's log offset when both the
-- root system and input proof match.
readMatchingProofRootMaybe :: String -> Ref -> Ref -> IO (Maybe (Word64, ProofNode))
readMatchingProofRootMaybe lemmaName rootSystemRef inputProofRef = do
    storedHead <- readKeyedAtMaybe (headKey lemmaName)

    case storedHead of
      Nothing -> pure Nothing
      Just (headOffset, proofHead) -> do
        storedRootNode <- readProofNode proofHead.phRoot

        case storedRootNode of
          Nothing -> pure Nothing
          Just rootNode -> do
            let sameRootSystem = pnSystem rootNode == Just rootSystemRef
                sameInputProof = phBasedOn proofHead == inputProofRef

            if sameRootSystem && sameInputProof
              then pure (Just (headOffset, rootNode))
              else pure Nothing

-- | Restore the saved proof and any searches started at its sorries after it
-- was saved. The caller builds each node from its method, optional System ref
-- and restored children, so the store need not depend on the in-memory proof type.
restoreStoredProof :: (ProofMethod -> Maybe Ref -> M.Map CaseName proof -> proof)
                   -> String -> Ref -> Ref -> IO (Maybe proof)
restoreStoredProof makeNode lemmaName rootSystemRef inputProofRef = do
    storedRoot <- readMatchingProofRootMaybe lemmaName rootSystemRef inputProofRef

    case storedRoot of
      Nothing -> pure Nothing
      Just (headOffset, rootProofNode) -> do
        restoredProof <- restoreNode headOffset rootProofNode

        pure (Just restoredProof)
  where
    restoreNode headOffset (ProofNode method maybeSystemRef childProofNodeRefs) = do
        newerSearch <- laterSearch headOffset method maybeSystemRef

        case newerSearch of
          Just (systemRef, searchStepKey) -> unfoldSearch S.empty systemRef searchStepKey
          Nothing -> do
            childProofs <- traverse (restoreChildNode headOffset) childProofNodeRefs

            pure (makeNode method maybeSystemRef childProofs)

    restoreChildNode headOffset proofNodeRef = do
        storedNode <- readProofNode proofNodeRef

        case storedNode of
          Just proofNode -> restoreNode headOffset proofNode
          Nothing -> error ("restoreProofFromStore: missing proof node " ++ show proofNodeRef)

    -- Only replace a saved sorry if a search started there after this snapshot
    -- and recorded at least one step. Otherwise keep the saved proof as it is.
    laterSearch headOffset (Sorry _) (Just systemRef) = do
        searchStart <- readSearchStartAfter headOffset lemmaName systemRef

        case searchStart of
          Nothing -> pure Nothing
          Just searchStepKey -> do
            firstStep <- readProofStepMaybe searchStepKey

            case firstStep of
              Nothing -> pure Nothing
              Just _  -> pure (Just (systemRef, searchStepKey))
    laterSearch _ _ _ = pure Nothing

    -- These are the search keys on this path, not every key in the tree.
    -- Reusing a key in another branch is fine; repeating it on this path
    -- would make restoration loop forever.
    unfoldSearch pathKeys systemRef searchStepKey
      | searchStepKey `S.member` pathKeys =
          pure (leaf (Sorry (Just "cycle in stored search")))
      | otherwise = do
          storedStep <- readProofStepMaybe searchStepKey

          case storedStep of
            Nothing   -> pure (leaf (Sorry (Just "not explored")))
            Just step -> do
              let nextPathKeys = S.insert searchStepKey pathKeys
                  -- Match each child's system Ref with its search key by case
                  -- name. Keep only cases present in both maps.
                  childSystemsAndKeys = M.intersectionWith (,)
                      (meChildren step) (meChildKeys step)

              childProofs <- traverse (restoreSearchChild nextPathKeys) childSystemsAndKeys

              pure (makeNode (meMethod step) (Just systemRef) childProofs)
      where
        leaf method = makeNode method (Just systemRef) M.empty

    restoreSearchChild pathKeys (childSystemRef, childSearchKey) =
        unfoldSearch pathKeys childSystemRef childSearchKey

-- | Identify a proof by its methods and case names, given its children's
-- identities. This is not the key of a stored record.
fileProofRef :: ProofMethod -> M.Map CaseName Ref -> Ref
fileProofRef method childProofRefs =
    let taggedProof = ("file-proof" :: String, method, childProofRefs)
    in keyOf KProofHead (Bin.encode taggedProof)

-- | Read a subject-addressed record, if present.
readKeyedMaybe :: Bin.Binary a => Ref -> IO (Maybe a)
readKeyedMaybe key = do
    storedRecord <- readKeyedAtMaybe key
    let storedValue = case storedRecord of
          Nothing -> Nothing
          Just recordAtOffset -> Just (snd recordAtOffset)
    pure storedValue

-- | Read a subject-addressed record and its offset in the log, if present.
readKeyedAtMaybe :: Bin.Binary a => Ref -> IO (Maybe (Word64, a))
readKeyedAtMaybe key = do
    existing <- readIORef globalStore
    case existing of
      Nothing    -> pure Nothing
      Just store -> do
        index <- readIORef store.storeIndex
        case M.lookup key index of
          Nothing       -> pure Nothing
          Just location -> do
            payload <- readRecordPayloadAt store location
            value <- decodePayload key payload
            pure (Just (location.recordOffset, value))

-- Store snapshots and JSON dump

-- | One complete record from an immutable prefix of store.bin.
data StoredRecord = StoredRecord
  { storedKind    :: Kind
  , storedKey     :: Ref
  , storedPayload :: BL.ByteString
  }

-- | Read the complete-record prefix of store.bin once. A torn tail is ignored.
readStoreRecords :: FilePath -> IO [StoredRecord]
readStoreRecords dir = do
    bytes <- BL.readFile (storePath dir)
    recordBytes <- removeStoreHeader bytes
    let records = collectStoreRecords recordBytes
    _ <- evaluate (length records)
    pure records

-- | Check and remove the version header for standalone readers.
removeStoreHeader :: BL.ByteString -> IO BL.ByteString
removeStoreHeader bytes
  | BL.take headerSize bytes == expectedHeader =
      pure (BL.drop headerSize bytes)
  | otherwise =
      ioError (userError ("incompatible store.bin; expected "
                          ++ show storeVersionHeader))
  where
    headerSize = fromIntegral storeVersionHeaderSize
    expectedHeader = BL.fromStrict storeVersionHeader

-- | Decode a stored payload and reject trailing bytes.
decodeStoredRecord :: Bin.Binary a => StoredRecord -> Either String a
decodeStoredRecord record =
    case Bin.decodeOrFail record.storedPayload of
      Left (_, _, decodeError) -> Left decodeError
      Right (remaining, _, value)
        | BL.null remaining -> Right value
        | otherwise         -> Left "binary payload has trailing bytes"

-- | Write store.jsonl from an already captured store snapshot.
writeStoreJSON :: FilePath -> [StoredRecord] -> IO FilePath
writeStoreJSON dir records = do
    let out = dir </> "store.jsonl"
    BL.writeFile out (BL.concat (map jsonLine records))
    pure out
  where
    jsonLine record =
        A.encode (object [ "kind"    .= kindTag record.storedKind
                         , "id"      .= record.storedKey
                         , "content" .= content record ]) <> "\n"

    content record = case record.storedKind of
      KNode          -> decodeJSON record (undefined :: RuleACInst)
      KGoal          -> decodeJSON record (undefined :: Goal)
      KEdge          -> decodeJSON record (undefined :: Edge)
      KLessAtom      -> decodeJSON record (undefined :: LessAtom)
      KFormulas      -> decodeJSON record (undefined :: S.Set LNGuarded)
      KSubtermStore  -> decodeJSON record (undefined :: SubtermStore)
      KEqStore       -> decodeJSON record (undefined :: EqStore)
      KShell         -> decodeJSON record (undefined :: SystemShell)
      KMethodEdge    -> decodeJSON record (undefined :: MethodEdge)
      KLemmaRoot     -> decodeJSON record (undefined :: LemmaRoot)
      KTheoryContext -> decodeJSON record (undefined :: Ref)
      KProofNode     -> decodeJSON record (undefined :: ProofNode)
      KProofHead     -> decodeJSON record (undefined :: ProofHead)
      KSearchStart   -> decodeJSON record (undefined :: SearchStart)

    decodeJSON :: (Bin.Binary a, ToJSON a) => StoredRecord -> a -> A.Value
    decodeJSON record expectedType =
        A.toJSON (decodedValue `asTypeOf` expectedType)
      where
        decodedValue = either (error . recordDecodeError record) id
                              (decodeStoredRecord record)

-- | Parse every complete record and stop before an invalid or torn tail.
collectStoreRecords :: BL.ByteString -> [StoredRecord]
collectStoreRecords remaining
  | BL.length headerBytes < fromIntegral recordHeaderSize = []
  | otherwise =
      case decodeRecordHeader (BL.toStrict headerBytes) of
        Nothing -> []
        Just header ->
          let payloadLength = header.headerPayloadLength
              (payload, afterRecord) =
                BL.splitAt (fromIntegral payloadLength) body
          in if BL.length payload < fromIntegral payloadLength
               then []
               else StoredRecord header.headerKind header.headerKey payload
                    : collectStoreRecords afterRecord
  where
    (headerBytes, body) = BL.splitAt (fromIntegral recordHeaderSize) remaining

-- | Add record identity to an export decoding error.
recordDecodeError :: StoredRecord -> String -> String
recordDecodeError record decodeError =
    "binary decode of " ++ show record.storedKey ++ " ("
    ++ show record.storedKind ++ "): " ++ decodeError
