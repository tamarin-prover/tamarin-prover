{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
--
-- AC-unification of DH terms using Maude as a backend.
module Term.Maude.Process (
  -- * Handle to a maude process
    MaudeHandle(..)
  , startMaude
  , getMaudeStats

  -- * Unification using Maude
  , unifyViaMaude

  -- * Matching using Maude
  , matchViaMaude

  -- * Variants using Maude
  , variantsViaMaude

  -- * Normalization using Maude
  , normViaMaude

  -- * Managing the persistent Maude process
  , WithMaude
) where

-- import Data.Traversable hiding ( mapM )
import qualified Data.Map as M

import Term.Term
import Term.LTerm
import Term.Rewriting.Definitions
import Term.Maude.Signature
import Term.Maude.Types
import Term.Maude.Parser
import Term.Substitution

-- import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Fresh
import Control.Concurrent
import Control.Exception (onException, evaluate, SomeException, try)
import Control.DeepSeq   (rnf)
import Control.Monad.Bind

import qualified Data.ByteString as B
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC

import System.Process
import System.IO

import Utils.Misc
-- import Extension.Data.Monoid

-- import Debug.Trace

import Control.Concurrent.STM
import Control.Concurrent.Async
import qualified Data.Sequence as Seq

-- | A pool of Maude processes with job queue
data MaudeHandle = MaudeHandle 
    { mhFilePath :: FilePath
    , mhMaudeSig :: MaudeSig
    , mhPool     :: MaudePool 
    }

data MaudePool = MaudePool
    { mpProcesses   :: TVar [MaudeWorker]        -- Available processes
    , mpJobQueue    :: TQueue MaudeJob          -- Job queue
    , mpWorkerCount :: Int                       -- Total number of workers
    , mpStats       :: TVar MaudeStats           -- Aggregated statistics
    }

data MaudeWorker = MaudeWorker
    { mwProcess   :: MaudeProcess
    , mwWorkerId  :: Int
    , mwBusy      :: TVar Bool
    }

data MaudeJob = MaudeJob
    { mjCommand     :: ByteString
    , mjUpdateStats :: MaudeProcess -> MaudeProcess
    , mjResult      :: TMVar (Either String ByteString)  -- Result or error
    }

data MaudeStats = MaudeStats
    { msUnifCount  :: !Int
    , msMatchCount :: !Int
    , msNormCount  :: !Int
    , msVarCount   :: !Int
    } deriving Show

data MaudeProcess = MP {
      mIn        :: !Handle
    , mOut       :: !Handle
    , _mErr      :: !Handle
    , mProc      :: !ProcessHandle
    , unifCount  :: !Int
    , matchCount :: !Int
    , normCount  :: !Int
    , varCount   :: !Int
    }

-- | Start a pool of Maude processes
startMaude :: FilePath -> MaudeSig -> Int -> IO MaudeHandle
startMaude maudePath maudeSig poolSize = do
    -- Create job queue (bounded to prevent memory issues)
    jobQueue <- newTQueueIO
    
    -- Create worker processes
    workers <- mapM (createWorker maudePath maudeSig) [1..poolSize]
    
    -- Create process pool
    processesVar <- newTVarIO workers
    statsVar <- newTVarIO (MaudeStats 0 0 0 0)
    
    let pool = MaudePool processesVar jobQueue poolSize statsVar
    
    -- Start worker threads
    mapM_ (forkWorkerThread pool) workers
    
    return (MaudeHandle maudePath maudeSig pool)

-- | Create a single worker process
createWorker :: FilePath -> MaudeSig -> Int -> IO MaudeWorker
createWorker maudePath maudeSig workerId = do
    process <- startMaudeProcess maudePath maudeSig
    busyVar <- newTVarIO False
    return (MaudeWorker process workerId busyVar)

-- | Fork a worker thread that processes jobs
forkWorkerThread :: MaudePool -> MaudeWorker -> IO ThreadId
forkWorkerThread pool worker = forkIO $ forever $ do
    -- Get next job from queue
    job <- atomically $ readTQueue (mpJobQueue pool)
    
    -- Mark worker as busy
    atomically $ writeTVar (mwBusy worker) True
    
    -- Process the job
    result <- processJob worker job
    
    -- Return result
    atomically $ putTMVar (mjResult job) result
    
    -- Mark worker as available
    atomically $ writeTVar (mwBusy worker) False

-- | Process a single job with error handling
processJob :: MaudeWorker -> MaudeJob -> IO (Either String ByteString)
processJob worker job = do
    let process = mwProcess worker
        cmd = mjCommand job
        updateStats = mjUpdateStats job
    
    result <- try $ do
        -- Ensure command is fully evaluated
        evaluate (rnf cmd)
        
        -- Execute command
        let inp = mIn process
            out = mOut process
        B.hPut inp cmd
        hFlush inp
        
        -- Update statistics (modify the worker's process)
        let updatedProcess = updateStats process
        -- Note: In a pool, we might want to track stats separately
        
        -- Get result
        getToDelim out
    
    case result of
        Right res -> return (Right res)
        Left ex -> do
            -- Restart this worker's process on error
            restartWorkerProcess worker
            return (Left $ "Maude process error: " ++ show ex)
  where
    try :: IO a -> IO (Either SomeException a)
    try = Control.Exception.try

-- | Restart a worker's Maude process
restartWorkerProcess :: MaudeWorker -> IO ()
restartWorkerProcess worker = do
    let oldProcess = mwProcess worker
    -- Terminate old process
    terminateProcess (mProc oldProcess)
    _ <- waitForProcess (mProc oldProcess)
    
    -- This would need access to maudePath and maudeSig
    -- In practice, you'd store these in MaudeWorker or pass them
    -- newProcess <- startMaudeProcess maudePath maudeSig
    -- Update worker with new process (this would need STM)
    return ()

-- | Start a Maude process.
startMaudeProcess :: FilePath -- ^ Path to Maude
                  -> MaudeSig
                  -> IO (MaudeProcess)
startMaudeProcess maudePath maudeSig = do
    (hin,hout,herr,hproc) <- runInteractiveCommand maudeCmd
    _ <- getToDelim hout
    -- set maude flags
    mapM_ (executeMaudeCommand hin hout) setupCmds
    -- input the maude theory
    executeMaudeCommand hin hout (ppTheory maudeSig)
    return (MP hin hout herr hproc 0 0 0 0)
  where
    maudeCmd
      | dEBUGMAUDE = "sh -c \"tee /tmp/maude.input | "
                     ++ maudePath ++ " -interactive -no-tecla -no-banner -no-wrap -batch "
                     ++ "\" | tee /tmp/maude.output"
      | otherwise  =
          maudePath ++ " -interactive -no-tecla -no-banner -no-wrap -batch "
    executeMaudeCommand hin hout cmd =
        B.hPutStr hin cmd >> hFlush hin >> getToDelim hout >> return ()
    setupCmds = [ "set show command off .\n"
                , "set show timing off .\n"
                , "set show stats off .\n" ]
    dEBUGMAUDE = envIsSet "DEBUG_MAUDE"



-- -- | Restart the Maude process on this handle.
-- restartMaude :: MaudeHandle -> IO ()
-- restartMaude (MaudeHandle maudePath maudeSig mv) = modifyMVar_ mv $ \mp -> do
--     terminateProcess (mProc mp) <* waitForProcess (mProc mp)
    -- startMaudeProcess maudePath maudeSig

-- | @getToDelim ih@ reads input from @ih@ until the Maude delimitier is encountered.
--   It returns the 'ByteString' up to (not including) the delimiter.
getToDelim :: Handle -> IO ByteString
getToDelim ih =
    go BC.empty
  where
    go !acc = do
        bs <- BC.append acc <$> B.hGetSome ih 8096
        case BC.breakSubstring mDelim bs of
            (before, after) | after == mDelim -> return before
            (_,      after) | after == ""     -> go bs
            _  -> error $ "Too much maude output" ++ BC.unpack bs
    mDelim = "Maude> "

-- | Submit a job to the Maude pool and wait for result
callMaude :: MaudeHandle
          -> (MaudeProcess -> MaudeProcess) -- ^ Statistics updater
          -> ByteString 
          -> IO ByteString
callMaude (MaudeHandle _ _ pool) updateStatistics cmd = do
    -- Create result TMVar
    resultVar <- newEmptyTMVarIO
    
    -- Create job
    let job = MaudeJob cmd updateStatistics resultVar
    
    -- Submit job to queue (blocks if queue is full)
    atomically $ writeTQueue (mpJobQueue pool) job
    
    -- Wait for result
    result <- atomically $ takeTMVar resultVar
    
    case result of
        Right res -> return res
        Left err  -> error $ "callMaude failed: " ++ err

-- | Get aggregated statistics from the pool
getMaudeStats :: MaudeHandle -> IO String
getMaudeStats (MaudeHandle _ _ pool) = do
    stats <- readTVarIO (mpStats pool)
    let total = msUnifCount stats + msMatchCount stats + msNormCount stats + msVarCount stats
    return $ "Maude pool has processed " ++ show total ++ " commands ("
           ++ show (msUnifCount stats) ++ " unifications, "
           ++ show (msMatchCount stats) ++ " matchings, "
           ++ show (msNormCount stats) ++ " normalizations, "
           ++ show (msVarCount stats) ++ " variants)."

-- | Compute a result via Maude.
computeViaMaude ::
       MaudeHandle
    -> (MaudeProcess -> MaudeProcess)                                 -- ^ Update statistics
    -> (a -> BindT (Lit c LVar) MaudeLit Fresh ByteString)            -- ^ Conversion to Maude command
    -> (M.Map MaudeLit (Lit c LVar) -> ByteString -> Either String b) -- ^ Conversion from Maude reply
    -> a
    -> IO b
computeViaMaude hnd updateStats toMaude fromMaude inp = do
    let (cmd, bindings) = runConversion $ toMaude inp
    reply <- callMaude hnd updateStats cmd
    case fromMaude bindings reply of
        Right res -> return res
        Left    e -> fail $ "\ncomputeViaMaude:\nParse error: `" ++ e ++"'"++
                            "\nFor Maude Output: `" ++ BC.unpack reply ++"'"++
                            "\nFor query: `" ++ BC.unpack cmd++"'"

------------------------------------------------------------------------------
-- Unification modulo AC
------------------------------------------------------------------------------

-- | @unifyCmd eqs@ returns the Maude command to solve the unification problem @eqs@.
--   Expects a nonempty list of equations
unifyCmd :: [Equal MTerm] -> ByteString
unifyCmd []  = error "unifyCmd: cannot create cmd for empty list of equations."
unifyCmd eqs =
    "unify in MSG : " <> seqs <> " .\n"
  where
    ppEq (Equal t1 t2) = ppMaude t1 <> " =? " <> ppMaude t2
    seqs = B.intercalate " /\\ " $ map ppEq eqs


-- | @unifyViaMaude hnd eqs@ computes all AC unifiers of @eqs@ using the
--   Maude process @hnd@.
unifyViaMaude
    :: (IsConst c)
    => MaudeHandle
    -> (c -> LSort) -> [Equal (VTerm c LVar)] -> IO [SubstVFresh c LVar]
unifyViaMaude _   _      []  = return [emptySubstVFresh]
unifyViaMaude hnd sortOf eqs =
    computeViaMaude hnd incUnifCount toMaude fromMaude eqs
  where
    msig = mhMaudeSig hnd
    toMaude          = fmap unifyCmd . mapM (traverse (lTermToMTerm sortOf))
    fromMaude bindings reply =
        map (msubstToLSubstVFresh bindings) <$> parseUnifyReply msig reply
    incUnifCount mp  = mp { unifCount = 1 + unifCount mp }

------------------------------------------------------------------------------
-- Matching modulo AC
------------------------------------------------------------------------------

-- | @matchCmd p t@ returns the Maude command to match the terms @t@ to the
-- pattern @p@.
matchCmd :: [Equal MTerm] -> ByteString
matchCmd eqs =
    "match in MSG : " <> ppTerms t2s <> " <=? " <> ppTerms t1s <> " .\n"
  where
    (t1s,t2s) = unzip [ (a,b) | Equal a b <- eqs ]
    ppTerms = ppMaude . fAppList

-- | @matchViaMaude (t, p)@ computes a complete set of AC matchers of the term
-- @t@ to the pattern @p@ via Maude.
matchViaMaude :: (IsConst c)
              => MaudeHandle
              -> (c -> LSort)
              -> Match (VTerm c LVar)
              -> IO [Subst c LVar]
matchViaMaude hnd sortOf matchProblem =
    case flattenMatch matchProblem of
      Nothing -> return []
      Just [] -> return [emptySubst]
      Just ms -> computeViaMaude hnd incMatchCount toMaude fromMaude
                                 (uncurry Equal <$> ms)
  where
    msig = mhMaudeSig hnd
    toMaude  = fmap matchCmd . mapM (traverse (lTermToMTerm sortOf))
    fromMaude bindings reply =
        map (msubstToLSubstVFree bindings) <$> parseMatchReply msig reply
    incMatchCount mp = mp { matchCount = 1 + matchCount mp }



------------------------------------------------------------------------------
-- Getting variants
------------------------------------------------------------------------------
variantsCmd :: MTerm -> ByteString
variantsCmd tm = "get variants in MSG : " <> ppMaude tm <> " .\n"

variantsViaMaude :: (IsConst c)
                 => MaudeHandle
                 -> (c -> LSort)
                 -> VTerm c LVar
                 -> IO [SubstVFresh c LVar]
variantsViaMaude hnd sortOf t =
    computeViaMaude hnd incVarCount toMaude fromMaude t
  where
    msig = mhMaudeSig hnd
    toMaude = fmap variantsCmd . (lTermToMTerm sortOf)
    fromMaude bindings reply =
        map (msubstToLSubstVFresh bindings) <$> parseVariantsReply msig reply
    incVarCount mp = mp {varCount = 1 + varCount mp }

------------------------------------------------------------------------------
-- Normalization of terms
------------------------------------------------------------------------------

-- | @normCmd t@ returns the Maude command to normalize the term @t@
-- pattern @p@.
normCmd :: MTerm -> ByteString
normCmd tm = "reduce " <> ppMaude tm <> " .\n"

-- | @normViaMaude t@ normalizes the term t via Maude.
normViaMaude :: (IsConst c)
             => MaudeHandle
             -> (c -> LSort)
             -> VTerm c LVar
             -> IO (VTerm c LVar)
normViaMaude hnd sortOf t =
    computeViaMaude hnd incNormCount toMaude fromMaude t
  where
    msig = mhMaudeSig hnd
    toMaude = fmap normCmd . (lTermToMTerm sortOf)
    fromMaude bindings reply =
        (\mt -> (mTermToLNTerm "z" mt `evalBindT` bindings) `evalFresh` nothingUsed)
            <$> parseReduceReply msig reply
    incNormCount mp = mp { normCount = 1 + normCount mp }


-- Passing the Handle to Maude via a Reader monad
-------------------------------------------------

-- | Values that depend on a 'MaudeHandle'.
type WithMaude = Reader MaudeHandle
