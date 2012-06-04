{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Theory loading infrastructure.
module Main.TheoryLoader (
  -- * Static theory loading settings
    intruderVariantsFile
  , theoryLoadFlags

  -- ** Loading open theories
  , loadOpenThy

  -- ** Loading and closing theories
  , loadClosedThy
  , loadClosedWfThy
  , loadClosedThyString

  -- ** Constructing automatic provers
  , constructAutoProver

  , closeThy

  ) where

import           Prelude                             hiding (id, (.))

import           Data.Char                           (toLower)
import           Data.Label
import           Data.Monoid

import           Control.Basics
import           Control.Category
import           Control.DeepSeq (rnf)

import           System.Console.CmdArgs.Explicit
import           System.Directory

import           Extension.Prelude

import           Theory
import           Theory.Text.Parser
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.IntruderRules
import           Theory.Tools.Wellformedness

import           Main.Console
import           Main.Environment

import           Paths_tamarin_prover                (getDataFileName)


------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------

-- | The name of the intruder variants file.
intruderVariantsFile :: FilePath
intruderVariantsFile = "intruder_variants_dh.spthy"


-- | Flags for loading a theory.
theoryLoadFlags :: [Flag Arguments]
theoryLoadFlags =
  [ flagNone ["prove"] (addEmptyArg "addProofs")
      "Attempt to prove all security properties"

  , flagOpt "dfs" ["stop-on-trace"] (updateArg "stopOnTrace") "DFS|BFS|NONE"
      "How to search for traces (default DFS)"

  , flagOpt "5" ["bound", "b"] (updateArg "bound") "INT"
      "Bound the depth of the proofs"

  , flagOpt "s" ["heuristic"] (updateArg "heuristic") "(s|S|c|C)+"
      "Sequence of goal rankings to use (default 's')"

  --, flagOpt "" ["intruder","i"] (updateArg "intruderVariants") "FILE"
  --    "Cached intruder rules to use"

  , flagOpt "summary" ["partial-evaluation"] (updateArg "partialEvaluation")
      "SUMMARY|VERBOSE"
      "Partially evaluate multiset rewriting system"

  , flagOpt "" ["defines","D"] (updateArg "defines") "STRING"
      "Define flags for pseudo-preprocessor."
  ]

loadOpenThy :: Arguments -> FilePath -> IO OpenTheory
loadOpenThy = fst . loadThy

loadClosedThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedThy = uncurry (>=>) . loadThy

loadClosedWfThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedWfThy as file = do
    thy <- loadOpen file
    case checkWellformedness thy of
      []     -> close thy
      report -> do
          putStrLn $ "WARNING: ignoring the following errors"
          putStrLn $ renderDoc $ prettyWfErrorReport report
          close thy
      -- report -> error $ renderDoc $ prettyWfErrorReport report
  where
    (loadOpen, close) = loadThy as

loadClosedThyString :: Arguments -> String -> IO ClosedTheory
loadClosedThyString = uncurry (>=>) . loadThyString

-- | Load an open/closed theory from a file.
loadThy :: Arguments -> (FilePath -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadThy as = loadGenericThy (parseOpenTheory (defines as)) as

-- | Load an open/closed theory from a string.
loadThyString :: Arguments -> (String -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadThyString as = loadGenericThy loader as
  where
    loader str =
      case parseOpenTheoryString (defines as) str of
        Right thy -> return thy
        Left err -> error $ show err

-- | The defined pre-processor flags in the argument.
defines :: Arguments -> [String]
defines = findArg "defines"

-- | Load an open/closed theory given a loader function.
loadGenericThy :: (a -> IO OpenTheory)
               -> Arguments
               -> (a -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadGenericThy loader as =
    (loader, (closeThy as) <=< tryAddIntrVariants)
  where
    -- intruder variants
    --------------------
    tryAddIntrVariants :: OpenTheory -> IO OpenTheory
    tryAddIntrVariants thy0 = do
      let msig = get (sigpMaudeSig . thySignature) thy0
          thy  = addIntrRuleACs (subtermIntruderRules msig ++ specialIntruderRules) thy0
      if (enableDH msig) then
         do variantsFile <- getDataFileName intruderVariantsFile
            ifM (doesFileExist variantsFile)
                (do intrVariants <- parseIntruderRulesDH variantsFile
                    return $ addIntrRuleACs intrVariants thy
                )
                (error $ "could not find intruder message deduction theory '"
                           ++ variantsFile ++ "'")
         else return thy

-- | Close a theory according to arguments.
closeThy :: Arguments -> OpenTheory -> IO ClosedTheory
closeThy as =
      fmap (proveTheory prover . partialEvaluation)
    . closeTheory (maudePath as)
    -- FIXME: wf-check is at the wrong position here. Needs to be more
    -- fine-grained.
    . wfCheck
  where

    -- apply partial application
    ----------------------------
    partialEvaluation = case map toLower <$> findArg "partialEvaluation" as of
      Just "verbose" -> applyPartialEvaluation Tracing
      Just _         -> applyPartialEvaluation Summary
      _              -> id

    -- wellformedness check
    -----------------------
    wfCheck :: OpenTheory -> OpenTheory
    wfCheck thy =
      noteWellformedness
        (checkWellformedness thy) thy

    prover :: Prover
    prover | argExists "addProofs" as = runAutoProver $ constructAutoProver as
           | otherwise                = mempty

-- | Construct an 'AutoProver' from the given arguments (--bound,
-- --stop-on-trace).
constructAutoProver :: Arguments -> AutoProver
constructAutoProver as =
    -- force error early
    (rnf rankings) `seq`
    AutoProver (roundRobinHeuristic rankings) proofBound stopOnTrace
  where
    -- handles to relevant arguments
    --------------------------------
    proofBound      = read <$> findArg "bound" as

    rankings = case findArg "heuristic" as of
        Just (rawRankings@(_:_)) -> map ranking rawRankings
        Just []                  -> error "--heuristic: at least one ranking must be given"
        _                        -> [SmartRanking True]

    ranking 's' = SmartRanking False
    ranking 'S' = SmartRanking True
    ranking 'c' = UsefulGoalNrRanking
    ranking 'C' = GoalNrRanking
    ranking r   = error $ render $ fsep $ map text $ words $
      "Unknown goal ranking '" ++ [r] ++ "'. Use one of the following:\
      \ 's' for the smart ranking without loop breakers,\
      \ 'S' for the smart ranking with loop breakers,\
      \ 'c' for the creation order and useful goals first,\
      \ and 'C' for the creation order."

    stopOnTrace = case (map toLower) <$> findArg "stopOnTrace" as of
      Nothing     -> CutDFS
      Just "dfs"  -> CutDFS
      Just "none" -> CutNothing
      Just "bfs"  -> CutBFS
      Just other  -> error $ "unknown stop-on-trace method: " ++ other
