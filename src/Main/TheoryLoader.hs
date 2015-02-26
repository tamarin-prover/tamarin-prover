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
  , loadClosedThyWfReport
  , loadClosedThyString

  -- ** Loading open diff theories
  , loadOpenDiffThy

  -- ** Loading and closing diff theories
  , loadClosedDiffThy
  , loadClosedDiffThyWfReport
  , loadClosedDiffThyString

  
  -- ** Constructing automatic provers
  , constructAutoProver
  , constructAutoDiffProver

  -- ** Cached Message Deduction Rule Variants
  , dhIntruderVariantsFile
  , bpIntruderVariantsFile
  , addMessageDeductionRuleVariants

  ) where

import           Prelude                             hiding (id, (.))

import           Data.Char                           (toLower)
import           Data.Label
import           Data.List                           (isPrefixOf)
import           Data.Monoid

import           Control.Basics
import           Control.Category
import           Control.DeepSeq                     (rnf)
import           Extension.Prelude                   (ifM)

import           System.Console.CmdArgs.Explicit
import           System.Directory                    (doesFileExist)

import           Theory
import           Theory.Text.Parser                  (parseIntruderRules, parseOpenTheory, parseOpenTheoryString, parseOpenDiffTheory, parseOpenDiffTheoryString)
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.IntruderRules          (specialIntruderRules, subtermIntruderRules
                                                     , multisetIntruderRules)
import           Theory.Tools.Wellformedness

import           Main.Console
import           Main.Environment
import           Paths_tamarin_prover                (getDataFileName)


------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------


-- | Flags for loading a theory.
theoryLoadFlags :: [Flag Arguments]
theoryLoadFlags =
  [ flagOpt "" ["prove"] (updateArg "prove") "LEMMAPREFIX"
      "Attempt to prove a lemma "

  , flagOpt "dfs" ["stop-on-trace"] (updateArg "stopOnTrace") "DFS|BFS|NONE"
      "How to search for traces (default DFS)"

  , flagOpt "5" ["bound", "b"] (updateArg "bound") "INT"
      "Bound the depth of the proofs"

  , flagOpt "s" ["heuristic"] (updateArg "heuristic") "(s|S|c|C)+"
      "Sequence of goal rankings to use (default 's')"

  , flagOpt "summary" ["partial-evaluation"] (updateArg "partialEvaluation")
      "SUMMARY|VERBOSE"
      "Partially evaluate multiset rewriting system"

  , flagOpt "" ["defines","D"] (updateArg "defines") "STRING"
      "Define flags for pseudo-preprocessor."

  , flagNone ["diff"] (addEmptyArg "diff")
      "Turn on observational equivalence mode using diff terms."

--  , flagOpt "" ["diff"] (updateArg "diff") "OFF|ON"
--      "Turn on observational equivalence (default OFF)."
  ]

-- | The defined pre-processor flags in the argument.
defines :: Arguments -> [String]
defines = findArg "defines"

-- | Diff flag in the argument
diff :: Arguments -> [String]
diff as = if (argExists "diff" as) then ["diff"] else []

-- | Load an open theory from a file.
loadOpenDiffThy :: Arguments -> FilePath -> IO OpenDiffTheory
loadOpenDiffThy as fp = parseOpenDiffTheory (diff as ++ defines as) fp

-- | Load an open theory from a file.
loadOpenThy :: Arguments -> FilePath -> IO OpenTheory
loadOpenThy as = parseOpenTheory (diff as ++ defines as)

-- | Load a closed theory.
loadClosedDiffThy :: Arguments -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThy as inFile = loadOpenDiffThy as inFile >>= closeDiffThy as

-- | Load a closed theory.
loadClosedThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedThy as inFile = loadOpenThy as inFile >>= closeThy as

-- | Load a close theory and report on well-formedness errors.
loadClosedThyWfReport :: Arguments -> FilePath -> IO ClosedTheory
loadClosedThyWfReport as inFile = do
    thy <- loadOpenThy as inFile
    -- report
    case checkWellformedness thy of
      []     -> return ()
      report -> do
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Theory file '" ++ inFile ++ "'"
          putStrLn $ replicate 78 '-'
          putStrLn ""
          putStrLn $ "WARNING: ignoring the following wellformedness errors"
          putStrLn ""
          putStrLn $ renderDoc $ prettyWfErrorReport report
          putStrLn $ replicate 78 '-'
          putStrLn ""
    -- return closed theory
    closeThy as thy

-- | Load a closed diff theory and report on well-formedness errors.
loadClosedDiffThyWfReport :: Arguments -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThyWfReport as inFile = do
    thy <- loadOpenDiffThy as inFile
    -- report
    case checkWellformednessDiff thy of
      []     -> return ()
      report -> do
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Theory file '" ++ inFile ++ "'"
          putStrLn $ replicate 78 '-'
          putStrLn ""
          putStrLn $ "WARNING: ignoring the following wellformedness errors"
          putStrLn ""
          putStrLn $ renderDoc $ prettyWfErrorReport report
          putStrLn $ replicate 78 '-'
          putStrLn ""
    -- return closed theory
    closeDiffThy as (addDefaultDiffLemma thy)

loadClosedThyString :: Arguments -> String -> IO (Either String ClosedTheory)
loadClosedThyString as input =
    case parseOpenTheoryString (defines as) input of
        Left err  -> return $ Left $ "parse error: " ++ show err
        Right thy -> fmap Right $ closeThy as thy

loadClosedDiffThyString :: Arguments -> String -> IO (Either String ClosedDiffTheory)
loadClosedDiffThyString as input =
    case parseOpenDiffTheoryString (defines as) input of
        Left err  -> return $ Left $ "parse error: " ++ show err
        Right thy -> fmap Right $ closeDiffThy as (addDefaultDiffLemma thy)
             
-- | Close a theory according to arguments.
closeThy :: Arguments -> OpenTheory -> IO ClosedTheory
closeThy as thy0 = do
  thy1 <- addMessageDeductionRuleVariants thy0
  -- FIXME: wf-check is at the wrong position here. Needs to be more
  -- fine-grained.
  let thy2 = wfCheck thy1
  -- close and prove
  cthy <- closeTheory (maudePath as) thy2
  return $ proveTheory lemmaSelector prover $ partialEvaluation cthy
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

      lemmaSelector :: Lemma p -> Bool
      lemmaSelector lem =
          any (`isPrefixOf` get lName lem) lemmaNames
        where
          lemmaNames = findArg "prove" as

      -- replace all annotated sorrys with the configured autoprover.
      prover :: Prover
      prover | argExists "prove" as =
                  replaceSorryProver $ runAutoProver $ constructAutoProver as
             | otherwise            = mempty
             
-- | Close a diff theory according to arguments.
closeDiffThy :: Arguments -> OpenDiffTheory -> IO ClosedDiffTheory
closeDiffThy as thy0 = do
  thy1 <- addMessageDeductionRuleVariantsDiff thy0
  -- FIXME: wf-check is at the wrong position here. Needs to be more
  -- fine-grained.
  let thy2 = wfCheck thy1
  -- close and prove
  cthy <- closeDiffTheory (maudePath as) thy2
  return $ proveDiffTheory lemmaSelector diffLemmaSelector prover diffprover $ partialEvaluation cthy
    where
      -- apply partial application
      ----------------------------
      partialEvaluation = case map toLower <$> findArg "partialEvaluation" as of
        Just "verbose" -> applyPartialEvaluationDiff Tracing
        Just _         -> applyPartialEvaluationDiff Summary
        _              -> id

      -- wellformedness check
      -----------------------
      wfCheck :: OpenDiffTheory -> OpenDiffTheory
      wfCheck thy =
        noteWellformednessDiff
          (checkWellformednessDiff thy) thy

      lemmaSelector :: Lemma p -> Bool
      lemmaSelector lem =
          any (`isPrefixOf` get lName lem) lemmaNames
        where
          lemmaNames = findArg "prove" as

      diffLemmaSelector :: DiffLemma p -> Bool
      diffLemmaSelector lem =
          any (`isPrefixOf` get lDiffName lem) lemmaNames
        where
          lemmaNames = findArg "prove" as

      -- diff prover: replace all annotated sorrys with the configured autoprover.
      diffprover :: DiffProver
      diffprover | argExists "prove" as =
                         replaceDiffSorryProver $ runAutoDiffProver $ constructAutoDiffProver as
                 | otherwise            = mempty

      -- replace all annotated sorrys with the configured autoprover.
      prover :: Prover
      prover | argExists "prove" as =
                  replaceSorryProver $ runAutoProver $ constructAutoProver as
             | otherwise            = mempty
             
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

-- | Construct an 'AutoProver' from the given arguments (--bound,
-- --stop-on-trace).
constructAutoDiffProver :: Arguments -> AutoProver
constructAutoDiffProver as =
    -- FIXME!
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


------------------------------------------------------------------------------
-- Message deduction variants cached in files
------------------------------------------------------------------------------

-- | The name of the intruder variants file.
dhIntruderVariantsFile :: FilePath
dhIntruderVariantsFile = "intruder_variants_dh.spthy"

-- | The name of the intruder variants file.
bpIntruderVariantsFile :: FilePath
bpIntruderVariantsFile = "intruder_variants_bp.spthy"

-- | Add the variants of the message deduction rule. Uses the cached version
-- of the @"intruder_variants_dh.spthy"@ file for the variants of the message
-- deduction rules for Diffie-Hellman exponentiation.
addMessageDeductionRuleVariants :: OpenTheory -> IO OpenTheory
addMessageDeductionRuleVariants thy0
  | enableBP msig = addIntruderVariants [ dhIntruderVariantsFile
                                        , bpIntruderVariantsFile ]
  | enableDH msig = addIntruderVariants [ dhIntruderVariantsFile ]
  | otherwise     = return thy
  where
    msig         = get (sigpMaudeSig . thySignature) thy0
    rules        = subtermIntruderRules msig ++ specialIntruderRules
                   ++ if enableMSet msig then multisetIntruderRules else []
    thy          = addIntrRuleACs rules thy0
    addIntruderVariants files = do
        ruless <- mapM loadRules files
        return $ addIntrRuleACs (concat ruless) thy
      where
        loadRules file = do
            variantsFile <- getDataFileName file
            ifM (doesFileExist variantsFile)
                (parseIntruderRules msig variantsFile)
                (error $ "could not find intruder message deduction theory '"
                           ++ variantsFile ++ "'")

-- | Add the variants of the message deduction rule. Uses the cached version
-- of the @"intruder_variants_dh.spthy"@ file for the variants of the message
-- deduction rules for Diffie-Hellman exponentiation.
addMessageDeductionRuleVariantsDiff :: OpenDiffTheory -> IO OpenDiffTheory
addMessageDeductionRuleVariantsDiff thy0
  | enableBP msig = addIntruderVariantsDiff [ dhIntruderVariantsFile
                                            , bpIntruderVariantsFile ]
  | enableDH msig = addIntruderVariantsDiff [ dhIntruderVariantsFile ]
  | otherwise     = return thy
  where
    msig         = get (sigpMaudeSig . diffThySignature) thy0
    rules        = subtermIntruderRules msig ++ specialIntruderRules
                   ++ if enableMSet msig then multisetIntruderRules else []
    thy          = addIntrRuleACsDiffBoth rules thy0
    addIntruderVariantsDiff files = do
        ruless <- mapM loadRules files
        return $ addIntrRuleACsDiffBoth (concat ruless) thy
      where
        loadRules file = do
            variantsFile <- getDataFileName file
            ifM (doesFileExist variantsFile)
                (parseIntruderRules msig variantsFile)
                (error $ "could not find intruder message deduction theory '"
                           ++ variantsFile ++ "'")
