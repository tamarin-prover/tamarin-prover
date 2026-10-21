{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings   #-}

-- |
-- Build the readable analysis artifacts for an eviction store. Both
-- store.jsonl and the per-lemma trees come from one immutable store.bin
-- snapshot, so they always refer to the same complete-record prefix.
module Theory.Constraint.Solver.TreeExport
  ( writeStoreExports
  ) where

import           Theory.Constraint.Solver.ProofMethod (ProofMethod (..), Result (..))
import           Theory.Constraint.Solver.Store       (Kind (..), LemmaRoot (..),
                                                        MethodEdge (..),
                                                        ProofHead (..), ProofNode (..),
                                                        Ref, SearchStart (..),
                                                        StoredRecord (..),
                                                        decodeStoredRecord, readStoreRecords,
                                                        refText, valueRef, writeStoreJSON)
import           Theory.Constraint.System             (SystemTraceQuantifier (..),
                                                        prettyGoal)
import           Theory.Text.Pretty                    (render)

import           Data.Aeson                           (Value, object, (.=))
import qualified Data.Aeson                           as JSON
import qualified Data.Binary                          as Binary
import           Data.List                            (sortOn)
import qualified Data.Map                             as Map
import qualified Data.Set                             as Set
import           System.FilePath                      ((</>))

-- | Write store.jsonl and every available lemma tree next to store.bin.
writeStoreExports :: FilePath -> IO [FilePath]
writeStoreExports storeDirectory = do
    storedRecords <- readStoreRecords storeDirectory
    lemmaTreePaths <- writeLemmaTrees storeDirectory storedRecords
    storeJSONPath <- writeStoreJSON storeDirectory storedRecords
    pure (storeJSONPath : lemmaTreePaths)

-- | Reconstruct and write all lemma trees contained in a store snapshot.
writeLemmaTrees :: FilePath -> [StoredRecord] -> IO [FilePath]
writeLemmaTrees storeDirectory storedRecords = mapM writeLemmaTree lemmaRoots
  where
    lemmaRoots :: [LemmaRoot]
    lemmaRoots = sortOn (\root -> root.lrLemma) $ Map.elems $ Map.fromList
      [ (lemmaRoot.lrLemma, lemmaRoot)
      | (_, lemmaRoot) <- decodeRecords KLemmaRoot storedRecords
      ]

    proofNodesByRef :: Map.Map Ref ProofNode
    proofNodesByRef = Map.fromList (decodeRecords KProofNode storedRecords)

    -- Records are in log order, so the newest record of a key wins.
    proofHeadsByLemma :: Map.Map String (Int, ProofHead)
    proofHeadsByLemma = Map.fromList
      [ (proofHead.phLemma, (position, proofHead))
      | (position, proofHead) <- decodeRecordsAt KProofHead storedRecords
      ]

    searchStartsBySystem :: Map.Map (String, Ref) (Int, Ref)
    searchStartsBySystem = Map.fromList
      [ ((lemmaName, systemRef), (position, searchKey))
      | (position, SearchStart lemmaName systemRef searchKey) <- decodeRecordsAt KSearchStart storedRecords
      ]

    methodEdgesByKey :: Map.Map Ref MethodEdge
    methodEdgesByKey = Map.fromList (decodeRecords KMethodEdge storedRecords)

    storedSystemRefs :: Set.Set Ref
    storedSystemRefs = Set.fromList
      [ record.storedKey
      | record <- storedRecords
      , record.storedKind == KShell
      ]

    writeLemmaTree :: LemmaRoot -> IO FilePath
    writeLemmaTree lemmaRoot = do
        let (rootJSON, proofStatus) =
              case Map.lookup lemmaRoot.lrLemma proofHeadsByLemma of
                Nothing -> unexpandedNode lemmaRoot.lrRoot
                Just (headPosition, proofHead) ->
                  case Map.lookup proofHead.phRoot proofNodesByRef of
                    Nothing -> unexpandedNode lemmaRoot.lrRoot
                    Just rootProofNode ->
                      let sameRootSystem = rootProofNode.pnSystem == Just lemmaRoot.lrRoot
                          sameFileProof = proofHead.phBasedOn == lemmaRoot.lrFileProof
                      -- Ignore a saved proof if the formula or its file proof changed.
                      in if sameRootSystem && sameFileProof
                         then buildTreeNode storedSystemRefs proofNodesByRef
                                            (findLaterSearch headPosition) proofHead.phRoot
                         else unexpandedNode lemmaRoot.lrRoot
            treePath = storeDirectory
                       </> (sanitizeFileName lemmaRoot.lrLemma ++ ".tree.json")
        JSON.encodeFile treePath $ object
          [ "lemma"      .= lemmaRoot.lrLemma
          , "quantifier" .= quantifierText lemmaRoot.lrTraceQuantifier
          , "status"     .= exportStatusText proofStatus
          , "root"       .= rootJSON
          ]
        pure treePath
      where
        -- A search that started at a system after the head was stored.
        findLaterSearch headPosition systemRef =
          case Map.lookup (lemmaRoot.lrLemma, systemRef) searchStartsBySystem of
            Nothing -> Nothing
            Just (startPosition, searchKey) ->
              let startedAfterSave = startPosition > headPosition
                  firstStepIsStored = Map.member searchKey methodEdgesByKey
              in if startedAfterSave && firstStepIsStored
                 then Just (buildSearchNode methodEdgesByKey Set.empty systemRef searchKey)
                 else Nothing

-- | A lemma root without a stored proof, or a search step never taken.
unexpandedNode :: Ref -> (Value, ExportStatus)
unexpandedNode systemRef =
    ( object [ "method"   .= ("unexpanded" :: String)
             , "system"   .= refText systemRef
             , "children" .= object []
             ]
    , ExportIncomplete
    )

-- | Build one nested proof tree and its aggregate status. A sorry shows the
-- search that started at its system after the proof was stored, if any.
buildTreeNode :: Set.Set Ref
              -> Map.Map Ref ProofNode
              -> (Ref -> Maybe (Value, ExportStatus))
              -> Ref
              -> (Value, ExportStatus)
buildTreeNode storedSystemRefs proofNodesByRef findLaterSearch proofNodeRef =
    case Map.lookup proofNodeRef proofNodesByRef of
      Nothing -> error ("lemma tree references missing proof node " ++ show proofNodeRef)
      Just proofNode ->
        case proofNode.pnMethod of
          Sorry _ ->
            case proofNode.pnSystem of
              Nothing -> exportProofNode proofNode
              Just systemRef ->
                case findLaterSearch systemRef of
                  Nothing -> exportProofNode proofNode
                  Just searchTree -> searchTree
          _ -> exportProofNode proofNode
  where
    exportProofNode :: ProofNode -> (Value, ExportStatus)
    exportProofNode proofNode =
        let buildChildNode childProofNodeRef =
              buildTreeNode storedSystemRefs proofNodesByRef findLaterSearch childProofNodeRef
            childResults = Map.map buildChildNode proofNode.pnChildren
            childNodes = Map.map fst childResults
            childStatuses = map snd (Map.elems childResults)
            -- Unused script steps have no system. Preserve them in JSON,
            -- but let only checked steps contribute a proof status.
            stepStatus = case proofNode.pnSystem of
              Nothing -> ExportComplete
              Just _  -> exportStatusForMethod proofNode.pnMethod
            proofStatus = maximum (stepStatus : childStatuses)
        in ( object [ "method"   .= methodToJSON proofNode.pnMethod
                    , "node"     .= refText proofNodeRef
                    , "system"   .= fmap systemText proofNode.pnSystem
                    , "children" .= childNodes
                    ]
           , proofStatus
           )

    systemText systemRef
      | systemRef `Set.member` storedSystemRefs = refText systemRef
      | otherwise = error ("lemma tree references missing system " ++ show systemRef)

-- | Build the tree of a stored search by following its step keys. Steps that
-- were never taken are unexpanded, and a key repeated on the path is a cycle.
buildSearchNode :: Map.Map Ref MethodEdge
                -> Set.Set Ref
                -> Ref
                -> Ref
                -> (Value, ExportStatus)
buildSearchNode methodEdgesByKey ancestorSearchKeys systemRef searchKey
  | searchKey `Set.member` ancestorSearchKeys =
      ( object [ "method"   .= methodToJSON cycleMethod
               , "system"   .= refText systemRef
               , "children" .= object []
               ]
      , exportStatusForMethod cycleMethod
      )
  | otherwise =
      case Map.lookup searchKey methodEdgesByKey of
        Nothing   -> unexpandedNode systemRef
        Just methodEdge ->
          let nextAncestorSearchKeys = Set.insert searchKey ancestorSearchKeys
              buildChildSearch childSystemRef childSearchKey =
                buildSearchNode methodEdgesByKey nextAncestorSearchKeys childSystemRef childSearchKey
              -- Each child needs both a system ref and a search key. Keep
              -- only case names present in both maps, as in the stored search.
              childResults = Map.intersectionWith buildChildSearch
                methodEdge.meChildren methodEdge.meChildKeys
              childNodes = Map.map fst childResults
              childStatuses = map snd (Map.elems childResults)
              proofStatus = maximum
                (exportStatusForMethod methodEdge.meMethod : childStatuses)
          in ( object [ "method"   .= methodToJSON methodEdge.meMethod
                      , "node"     .= refText searchKey
                      , "system"   .= refText systemRef
                      , "children" .= childNodes
                      ]
             , proofStatus
             )
  where
    cycleMethod = Sorry (Just "cycle in stored search")

-- | Export a proof method in the existing tree-file schema.
methodToJSON :: ProofMethod -> Value
methodToJSON (SolveGoal goal) = object
    [ "solveGoal" .= object
        [ "ref"    .= refText (valueRef KGoal goal)
        , "pretty" .= render (prettyGoal goal)
        ]
    ]
methodToJSON Simplify          = JSON.toJSON ("simplify" :: String)
methodToJSON Induction         = JSON.toJSON ("induction" :: String)
methodToJSON (Sorry reason)    = object ["sorry" .= reason]
methodToJSON Invalidated       = JSON.toJSON ("invalidated" :: String)
methodToJSON (Finished result) = object ["finished" .= resultText result]

resultText :: Result -> String
resultText Solved            = "solved"
resultText Unfinishable      = "unfinishable"
resultText (Contradictory _) = "contradiction"

-- | Constructors are ordered from the least to the most important status.
data ExportStatus
  = ExportComplete
  | ExportUnfinishable
  | ExportIncomplete
  | ExportTrace
  | ExportInvalidated
  deriving (Eq, Ord)

exportStatusForMethod :: ProofMethod -> ExportStatus
exportStatusForMethod Invalidated                  = ExportInvalidated
exportStatusForMethod (Finished Solved)            = ExportTrace
exportStatusForMethod (Finished Unfinishable)      = ExportUnfinishable
exportStatusForMethod (Sorry _)                    = ExportIncomplete
exportStatusForMethod _                            = ExportComplete

exportStatusText :: ExportStatus -> String
exportStatusText ExportComplete       = "completeProof"
exportStatusText ExportUnfinishable   = "unfinishableProof"
exportStatusText ExportIncomplete     = "incompleteProof"
exportStatusText ExportTrace          = "traceFound"
exportStatusText ExportInvalidated    = "invalidatedProof"

quantifierText :: SystemTraceQuantifier -> String
quantifierText ExistsNoTrace   = "AllTraces"
quantifierText ExistsSomeTrace = "ExistsTrace"

-- | Decode every record of one kind or fail with record identity.
decodeRecords :: Binary.Binary a => Kind -> [StoredRecord] -> [(Ref, a)]
decodeRecords requestedKind storedRecords = map decodeRecord matchingRecords
  where
    matchingRecords :: [StoredRecord]
    matchingRecords = filter hasRequestedKind storedRecords

    hasRequestedKind :: StoredRecord -> Bool
    hasRequestedKind record = record.storedKind == requestedKind

    decodeRecord record =
        case decodeStoredRecord record of
          Right value       -> (record.storedKey, value)
          Left decodeError  -> error
            ("binary decode of " ++ show record.storedKey ++ " ("
             ++ show record.storedKind ++ "): " ++ decodeError)

-- | Like 'decodeRecords', with each record's position in the log.
decodeRecordsAt :: Binary.Binary a => Kind -> [StoredRecord] -> [(Int, a)]
decodeRecordsAt requestedKind storedRecords = decodeMatchingRecords recordsWithPositions
  where
    -- Count every record before filtering by kind. The positions must describe
    -- the shared log, so heads and search starts can be compared.
    recordsWithPositions = zip [0 ..] storedRecords

    decodeMatchingRecords [] = []
    decodeMatchingRecords ((position, record) : remainingRecords)
      | record.storedKind /= requestedKind =
          decodeMatchingRecords remainingRecords
      | otherwise =
          case decodeStoredRecord record of
            Right value ->
              (position, value) : decodeMatchingRecords remainingRecords
            Left decodeError -> error
              ("binary decode of " ++ show record.storedKey ++ " ("
               ++ show record.storedKind ++ "): " ++ decodeError)

sanitizeFileName :: String -> String
sanitizeFileName name = map replaceCharacter name
  where
    replaceCharacter character
      | character == '/' || character == ' ' = '_'
      | otherwise                            = character
