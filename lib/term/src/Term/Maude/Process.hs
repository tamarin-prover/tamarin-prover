{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts, NamedFieldPuns #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
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

import Data.Either
import Data.List
import Data.Traversable hiding ( mapM )
import qualified Data.Map as M

import Term.Term
import Term.LTerm
import Term.Maude.Types
import Term.Substitution
import Term.Rewriting.Definitions

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Fresh
import Control.Concurrent
import Control.Exception (onException, evaluate)
import Control.DeepSeq   (rnf)
import Control.Monad.Bind

import System.Process
import System.IO

import Utils.Misc


-- Pretty printing Maude commands
----------------------------------------------------------------------

-- | The term algebra and rewriting rules as a functional module in Maude.
theory :: MaudeSig -> String
theory msig@(MaudeSig {enableDH, enableXor, enableMSet, funSig}) = unlines $
    [ "fmod MSG is"
    , "  protecting NAT ." ]
    ++
    (if enableMSet
     then [ "  sort Pub Fresh Msg MSet Node TOP ."
          , "  subsort Msg < MSet ."
          , "  subsort MSet < TOP ."
          , "  op m : Nat -> MSet ."
          , "  op "++funsymPrefix++"mun : MSet MSet -> MSet [comm assoc] ."
          , "  op "++funsymPrefix++"empty : -> MSet ."
          ]
     else [ "  sort Pub Fresh Msg Node TOP ."])
    ++
    [ "  subsort Pub < Msg ."
    , "  subsort Fresh < Msg ."
    , "  subsort Msg < TOP ."
    , "  subsort Node < TOP ."
    -- constants
    , "  op f : Nat -> Fresh ."
    , "  op p : Nat -> Pub ."
    , "  op c : Nat -> Msg ."
    , "  op n : Nat -> Node ."
    -- used for encoding App List [t1,..,tk]
    -- list(cons(t1,cons(t2,..,cons(tk,nil)..)))
    , "  op "++funsymPrefix++"list : TOP -> TOP ."
    , "  op "++funsymPrefix++"cons : TOP TOP -> TOP ."
    , "  op "++funsymPrefix++"nil  : -> TOP ." ]
    ++
    (if enableDH
       then
       [ "  op "++funsymPrefix++"one : -> Msg ."
       , "  op "++funsymPrefix++"exp : Msg Msg -> Msg ."
       , "  op "++funsymPrefix++"mult : Msg Msg -> Msg [comm assoc] ."
       , "  op "++funsymPrefix++"inv : Msg -> Msg ." ]
       else [])
    ++
    (if enableXor
       then
       [ "  op "++funsymPrefix++"zero : -> Msg ."
       , "  op "++funsymPrefix++"xor : Msg Msg -> Msg [comm assoc] ."]
       else [])
    ++
    map theoryFunSym funSig
    ++
    (map theoryRule $ rrulesForMaudeSig msig)
    ++
    [ "endfm" ]
  where
    theoryFunSym (s,ar) =
        "  op " ++ funsymPrefix ++ s ++" : " ++(concat $ replicate ar "Msg ")++" -> Msg ."
    theoryRule (l `RRule` r) =
        "  eq " ++ ppMaude lm ++" = " ++ ppMaude rm ++" ."
      where (lm,rm) = evalBindT ((,) <$>  lTermToMTerm' l <*> lTermToMTerm' r) noBindings
                        `evalFresh` nothingUsed

--
-- Unification using Maude
----------------------------------------------------------------------

-- | Check environment if communication with Maude should be logged
dEBUGMAUDE ::Bool
dEBUGMAUDE = envIsSet "DEBUG_MAUDE"

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
    addMVarFinalizer mv $ withMVar mv $ \mp -> do
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
    -- input the maude theory
    hPutStr hin (theory maudeSig)
    hFlush  hin
    _ <- getToDelim hout
    return (MP hin hout herr hproc 0 0 0)
  where 
    maudeCmd
      | dEBUGMAUDE = "sh -c \"tee /tmp/maude.input | " 
                     ++ maudePath ++ " -no-tecla -no-banner -no-wrap -batch "
                     ++ "\" | tee /tmp/maude.output"
      | otherwise  = 
          maudePath ++ " -no-tecla -no-banner -no-wrap -batch " 

-- | Restart the Maude process on this handle.
restartMaude :: MaudeHandle -> IO ()
restartMaude (MaudeHandle maudePath maudeSig mv) = modifyMVar_ mv $ \mp -> do
    terminateProcess (mProc mp) <* waitForProcess (mProc mp)
    startMaudeProcess maudePath maudeSig

-- | @getToDelim ih@ reads input from @ih@ until @mDelim@ is encountered.
--   It returns the string read up to (not including) mDelim.
getToDelim :: Handle -> IO String
getToDelim ih = go []
  where
    go acc = do
        c <- hGetChar ih
        let acc' = c:acc
        if mDelim `isPrefixOf` acc'
          then return (reverse (drop (length mDelim) acc'))
          else go acc'
    mDelim = reverse "Maude> "

-- | @callMaude cmd@ sends the command @cmd@ to Maude and returns Maude's
-- output up to the next prompt sign.
callMaude :: MaudeHandle
          -> (MaudeProcess -> MaudeProcess) -- ^ Statistics updater.
          -> String -> IO String
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
        hPutStr inp cmd
        hFlush  inp
        mp' <- evaluate (updateStatistics mp)
        res <- getToDelim out
        return (mp', res)

-- | Compute a result via Maude.
computeViaMaude :: 
       (Show a, Show b, Ord c)
    => MaudeHandle
    -> (MaudeProcess -> MaudeProcess)                   -- ^ Update statistics
    -> (a -> BindT (Lit c LVar) MaudeLit Fresh String)  -- ^ Conversion to Maude
    -> (M.Map MaudeLit (Lit c LVar) -> MSubst -> b)     -- ^ Conversion from Maude
    -> a
    -> IO [b]
computeViaMaude hnd updateStats toMaude fromMaude inp = do
    let (cmd, bindings) = runConversion $ toMaude inp
    s <- callMaude hnd updateStats cmd
    let esubstsm = parseMaudeReply s
        substs   = map (fromMaude bindings) $ rights esubstsm
    case lefts esubstsm of
      [] -> return $ substs
      es -> fail $ "\ncomputeViaMaude:\nParse error: \n" ++ 
                   concatMap show es ++ 
                   "\n For Maude Output:\n" ++ s ++
                   "\nFor query:\n" ++ cmd


------------------------------------------------------------------------------
-- Unification
------------------------------------------------------------------------------

-- | @unifyCmd eqs@ returns the Maude command to solve the unification problem @eqs@.
--   Expects a nonempty list of equations
unifyCmd :: [Equal MTerm] -> [Char]
unifyCmd []  = error "unifyCmd: cannot create cmd for empty list of equations."
unifyCmd eqs =
    "unify in MSG : " ++seqs++" .\n"
  where
    ppEq (Equal t1 t2) = ppMaude t1 ++ " =? " ++ ppMaude t2
    seqs = intercalate " /\\ " $ map ppEq eqs


-- | @unifyViaMaude hnd eqs@ computes all AC unifiers of @eqs@ using the
--   Maude process @hnd@.
unifyViaMaude 
    :: (IsConst c , Show (Lit c LVar), Ord c)
    => MaudeHandle
    -> (c -> LSort) -> [Equal (VTerm c LVar)] -> IO [SubstVFresh c LVar]
unifyViaMaude _   _      []  = return [emptySubstVFresh]
unifyViaMaude hnd sortOf eqs =
    computeViaMaude hnd incUnifCount toMaude msubstToLSubstVFresh eqs
  where
    toMaude          = fmap unifyCmd . mapM (traverse (lTermToMTerm sortOf))
    incUnifCount mp  = mp { unifCount = 1 + unifCount mp }


------------------------------------------------------------------------------
-- Matching modulo AC
------------------------------------------------------------------------------

-- | @matchCmd p t@ returns the Maude command to match the terms @t@ to the
-- pattern @p@.
matchCmd :: [Equal MTerm] -> String
matchCmd eqs =
    "match in MSG : " ++ppTerms t2s++ " <=? " ++ ppTerms t1s++" .\n"
  where
    -- FIXME: slow
    (t1s,t2s) = unzip [ (a,b) | Equal a b <- eqs ]
    ppTerms = ppMaude . fAppList

-- | @matchViaMaude (t, p)@ computes a complete set of AC matchers of the term
-- @t@ to the pattern @p@ via Maude.
matchViaMaude :: (IsConst c , Show (Lit c LVar), Ord c)
              => MaudeHandle
              -> (c -> LSort)
              -> [Match (VTerm c LVar)]
              -> IO [Subst c LVar]
matchViaMaude _   _      []  = return [emptySubst]
matchViaMaude hnd sortOf matcheqs =
    computeViaMaude hnd incMatchCount toMaude msubstToLSubstVFree eqs
  where
    toMaude  = fmap matchCmd . mapM (traverse (lTermToMTerm sortOf)) 
    incMatchCount mp = mp { matchCount = 1 + matchCount mp }
    eqs = [Equal t p | MatchWith t p <- matcheqs ]

------------------------------------------------------------------------------
-- Normalization of terms
------------------------------------------------------------------------------

-- | @normCmd t@ returns the Maude command to normalize the term @t@
-- pattern @p@.
normCmd :: MTerm -> String
normCmd tm = "reduce "++ppMaude tm++" .\n"


-- | @normViaMaude t@ normalizes the term t via Maude.
normViaMaude :: (IsConst c , Show (Lit c LVar), Ord c)
             => MaudeHandle
             -> (c -> LSort)
             -> VTerm c LVar
             -> IO (VTerm c LVar)
normViaMaude hnd sortOf t = do
    let (cmd, bindings) = runConversion $ toMaude t
    s <- callMaude hnd incNorm cmd
    case parseReduceSolution s of
      Right mt -> return $ evalBindT (mTermToLNTerm "z" mt) bindings
                             `evalFresh` nothingUsed
      Left  e  -> fail $ "\ncomputeViaMaude:\nParse error: \n" ++ 
                   show e ++ 
                   "\n For Maude Output:\n" ++ s ++
                   "\nFor query:\n" ++ cmd
  where
    toMaude    = fmap normCmd . (lTermToMTerm sortOf)
    incNorm mp = mp { normCount = 1 + normCount mp }

-- Passing the Handle to Maude via a Reader monad
-------------------------------------------------

-- | Values that depend on a 'MaudeHandle'.
type WithMaude = Reader MaudeHandle
