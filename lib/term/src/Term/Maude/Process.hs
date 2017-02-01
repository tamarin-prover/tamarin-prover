{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
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
import Control.Exception (onException, evaluate)
import Control.DeepSeq   (rnf)
import Control.Monad.Bind

import qualified Data.ByteString as B
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC

import System.Process
import System.IO

import Utils.Misc
import Extension.Data.Monoid


-- Unification using a persistent Maude process
-----------------------------------------------------------------------

-- | A handle to a Maude process. It requires the Maude path for Signatures to
-- be serializable. If we also add the string for the Maude config file, then
-- it would even be serializable on its own.
data MaudeHandle = MaudeHandle { mhFilePath :: FilePath
                               , mhMaudeSig :: MaudeSig
                               , mhProc     :: MVar MaudeProcess }

-- | @getMaudeStats@ returns the maude stats formatted as a string.
getMaudeStats :: MaudeHandle -> IO String
getMaudeStats (MaudeHandle {mhProc = maude}) =
    withMVar maude $ \mp -> do
      let mc = matchCount mp
          uc = unifCount mp
      return $ "Maude has been called "++show (mc+uc)++ " times ("
                 ++show uc++" unifications and "++show mc++" matchings)."

data MaudeProcess = MP {
      mIn        :: !Handle
    , mOut       :: !Handle
    , _mErr      :: !Handle
    , mProc      :: !ProcessHandle
    , unifCount  :: !Int
    , matchCount :: !Int
    , normCount  :: !Int
    }

-- | @startMaude@ starts a new instance of Maude and returns a Handle to it.
startMaude :: FilePath -> MaudeSig -> IO MaudeHandle
startMaude maudePath maudeSig = do
    mv <- newMVar =<< startMaudeProcess maudePath maudeSig
    -- Add a finalizer to the MVar that stops maude.
    _  <- mkWeakMVar mv $ withMVar mv $ \mp -> do
        terminateProcess (mProc mp) <* waitForProcess (mProc mp)      
    -- return the maude handle
    return (MaudeHandle maudePath maudeSig mv)

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
    return (MP hin hout herr hproc 0 0 0)
  where
    maudeCmd
      | dEBUGMAUDE = "sh -c \"tee /tmp/maude.input | "
                     ++ maudePath ++ " -no-tecla -no-banner -no-wrap -batch "
                     ++ "\" | tee /tmp/maude.output"
      | otherwise  =
          maudePath ++ " -no-tecla -no-banner -no-wrap -batch "
    executeMaudeCommand hin hout cmd =
        B.hPutStr hin cmd >> hFlush hin >> getToDelim hout >> return ()
    setupCmds = [ "set show command off .\n"
                , "set show timing off .\n"
                , "set show stats off .\n" ]
    dEBUGMAUDE = envIsSet "DEBUG_MAUDE"



-- | Restart the Maude process on this handle.
restartMaude :: MaudeHandle -> IO ()
restartMaude (MaudeHandle maudePath maudeSig mv) = modifyMVar_ mv $ \mp -> do
    terminateProcess (mProc mp) <* waitForProcess (mProc mp)
    startMaudeProcess maudePath maudeSig

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

-- | @callMaude cmd@ sends the command @cmd@ to Maude and returns Maude's
-- output up to the next prompt sign.
callMaude :: MaudeHandle
          -> (MaudeProcess -> MaudeProcess) -- ^ Statistics updater.
          -> ByteString -> IO ByteString
callMaude hnd updateStatistics cmd = do
    -- Ensure that the command is fully evaluated and therefore does not depend
    -- on another call to Maude anymore. Otherwise, we could end up in a
    -- deadlock.
    evaluate (rnf cmd)
    -- If there was an exception, then we might be out of sync with the current
    -- persistent Maude process: restart the process.
    (`onException` restartMaude hnd) $ modifyMVar (mhProc hnd) $ \mp -> do
        let inp = mIn  mp
            out = mOut mp
        B.hPut inp cmd
        hFlush  inp
        mp' <- evaluate (updateStatistics mp)
        res <- getToDelim out
        return (mp', res)

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
