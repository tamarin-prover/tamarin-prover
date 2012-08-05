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
    theoryLoadFlags

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
import           Data.Monoid

import           Control.Basics
import           Control.Category
import           Control.DeepSeq (rnf)

import           System.Console.CmdArgs.Explicit

import           Theory
import           Theory.Text.Parser
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.Wellformedness

import           Main.Console
import           Main.Environment


------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------


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
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Theory file '" ++ file ++ "'"
          putStrLn $ replicate 78 '-'
          putStrLn ""
          putStrLn $ "WARNING: ignoring the following wellformedness errors"
          putStrLn ""
          putStrLn $ renderDoc $ prettyWfErrorReport report
          putStrLn $ replicate 78 '-'
          putStrLn ""
          close thy
      -- report -> error $ renderDoc $ prettyWfErrorReport report
  where
    (loadOpen, close) = loadThy as

loadClosedThyString :: Arguments -> String -> IO (Either String ClosedTheory)
loadClosedThyString as file = do
    let (loader, closer) = loadThyString as
    openThy <- loader file
    case openThy of
      Right thy -> Right <$> closer thy
      Left  err -> return $ Left err

-- | Load an open/closed theory from a file.
loadThy :: Arguments -> (FilePath -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadThy as = loadGenericThy (parseOpenTheory (defines as)) as

-- | Load an open/closed theory from a string.
loadThyString :: Arguments -> ( String -> IO (Either String OpenTheory)
                              , OpenTheory -> IO ClosedTheory)
loadThyString as = loadGenericThy loader as
  where
    loader str =
      case parseOpenTheoryString (defines as) str of
        Right thy -> return $ Right thy
        Left err  -> return $ Left $ "parse error: " ++ show err

-- | The defined pre-processor flags in the argument.
defines :: Arguments -> [String]
defines = findArg "defines"

-- FIXME: SM: This naming, tupling, blah is a mess and can be done more
-- cleanly. DO IT!

-- | Load an open/closed theory given a loader function.
loadGenericThy :: a -> Arguments -> (a, OpenTheory -> IO ClosedTheory)
loadGenericThy loader as =
    (loader, (closeThy as) <=< addMessageDeductionRuleVariants)

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

    -- replace all annotated sorrys with the configured autoprover.
    prover :: Prover
    prover | argExists "addProofs" as =
                 replaceSorryProver $ runAutoProver $ constructAutoProver as
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
        _                        -> [SmartRanking False]

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
