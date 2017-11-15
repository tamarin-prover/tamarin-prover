{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
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
  , reportOnClosedThyStringWellformedness

  -- ** Loading open diff theories
  , loadOpenDiffThy

  -- ** Loading and closing diff theories
  , loadClosedDiffThy
  , loadClosedDiffThyWfReport
  , loadClosedDiffThyString
  , reportOnClosedDiffThyStringWellformedness

  
  -- ** Constructing automatic provers
  , constructAutoProver
  , constructAutoDiffProver

  -- ** Cached Message Deduction Rule Variants
  , dhIntruderVariantsFile
  , bpIntruderVariantsFile
  , addMessageDeductionRuleVariants

  ) where

-- import           Debug.Trace
  
import           Prelude                             hiding (id, (.))

import           Data.Char                           (toLower)
import           Data.Label
import           Data.List                           (isPrefixOf)
-- import           Data.Monoid
import           Data.FileEmbed                      (embedFile)

-- import           Control.Basics
import           Control.Category
import           Control.DeepSeq                     (rnf)

import           System.Console.CmdArgs.Explicit

import           Theory
import           Theory.Text.Parser                  (parseIntruderRules, parseOpenTheory, parseOpenTheoryString, parseOpenDiffTheory, parseOpenDiffTheoryString)
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.IntruderRules          (specialIntruderRules, subtermIntruderRules
                                                     , multisetIntruderRules)
import           Theory.Tools.Wellformedness

import           Main.Console
import           Main.Environment

import           Text.Parsec                hiding ((<|>))


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

  , flagOpt "s" ["heuristic"] (updateArg "heuristic") "(s|S|o|O|p|P|l|c|C|i|I)+"
      "Sequence of goal rankings to use (default 's')"

  , flagOpt "summary" ["partial-evaluation"] (updateArg "partialEvaluation")
      "SUMMARY|VERBOSE"
      "Partially evaluate multiset rewriting system"

  , flagOpt "" ["defines","D"] (updateArg "defines") "STRING"
      "Define flags for pseudo-preprocessor."

  , flagNone ["diff"] (addEmptyArg "diff")
      "Turn on observational equivalence mode using diff terms."

  , flagNone ["quit-on-warning"] (addEmptyArg "quit-on-warning")
      "Strict mode that quits on any warning that is emitted."

--  , flagOpt "" ["diff"] (updateArg "diff") "OFF|ON"
--      "Turn on observational equivalence (default OFF)."
  ]

-- | The defined pre-processor flags in the argument.
defines :: Arguments -> [String]
defines = findArg "defines"

-- | Diff flag in the argument
diff :: Arguments -> [String]
diff as = if (argExists "diff" as) then ["diff"] else []

-- | quit-on-warning flag in the argument
quitOnWarning :: Arguments -> [String]
quitOnWarning as = if (argExists "quit-on-warning" as) then ["quit-on-warning"] else []

-- | Load an open theory from a file.
loadOpenDiffThy :: Arguments -> FilePath -> IO OpenDiffTheory
loadOpenDiffThy as fp = parseOpenDiffTheory (diff as ++ defines as ++ quitOnWarning as) fp

-- | Load an open theory from a file.
loadOpenThy :: Arguments -> FilePath -> IO OpenTheory
loadOpenThy as = parseOpenTheory (diff as ++ defines as ++ quitOnWarning as)

-- | Load a closed theory.
loadClosedDiffThy :: Arguments -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThy as inFile = do
  thy0 <- loadOpenDiffThy as inFile
  thy1 <- addMessageDeductionRuleVariantsDiff thy0
  closeDiffThy as thy1

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
          if elem "quit-on-warning" (quitOnWarning as) then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""
    -- return closed theory
    closeThy as thy

-- | Load a closed diff theory and report on well-formedness errors.
loadClosedDiffThyWfReport :: Arguments -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThyWfReport as inFile = do
    thy0 <- loadOpenDiffThy as inFile
    thy1 <- addMessageDeductionRuleVariantsDiff thy0
    -- report
    case checkWellformednessDiff thy1 of
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
          if elem "quit-on-warning" (quitOnWarning as) then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""
    -- return closed theory
    closeDiffThy as thy1

loadClosedThyString :: Arguments -> String -> IO (Either String ClosedTheory)
loadClosedThyString as input =
    case parseOpenTheoryString (defines as) input of
        Left err  -> return $ Left $ "parse error: " ++ show err
        Right thy -> fmap Right $ closeThy as thy

loadClosedDiffThyString :: Arguments -> String -> IO (Either String ClosedDiffTheory)
loadClosedDiffThyString as input =
    case parseOpenDiffTheoryString (defines as) input of
        Left err  -> return $ Left $ "parse error: " ++ show err
        Right thy -> fmap Right $ do
          thy1 <- addMessageDeductionRuleVariantsDiff thy
          closeDiffThy as thy1

-- | Load an open theory from a string.
loadOpenThyString :: Arguments -> String -> Either ParseError OpenTheory
loadOpenThyString as = parseOpenTheoryString (diff as ++ defines as ++ quitOnWarning as)

-- | Load an open theory from a string.
loadOpenDiffThyString :: Arguments -> String -> Either ParseError OpenDiffTheory
loadOpenDiffThyString as = parseOpenDiffTheoryString (diff as ++ defines as ++ quitOnWarning as)

-- | Load a close theory and only report on well-formedness errors.
reportOnClosedThyStringWellformedness :: Arguments -> String -> IO String
reportOnClosedThyStringWellformedness as input = do
    case loadOpenThyString as input of
      Left  err -> return $ "parse error: " ++ show err
      Right thy ->
        case checkWellformedness thy of
          []     -> return ""
          report -> do
            if elem "quit-on-warning" (quitOnWarning as) then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""
            return $ " WARNING: ignoring the following wellformedness errors: " ++(renderDoc $ prettyWfErrorReport report)

-- | Load a closed diff theory and report on well-formedness errors.
reportOnClosedDiffThyStringWellformedness :: Arguments -> String -> IO String
reportOnClosedDiffThyStringWellformedness as input = do
    case loadOpenDiffThyString as input of
      Left  err   -> return $ "parse error: " ++ show err
      Right thy0 -> do
        thy1 <- addMessageDeductionRuleVariantsDiff thy0
        -- report
        case checkWellformednessDiff thy1 of
          []     -> return ""
          report -> do
            if elem "quit-on-warning" (quitOnWarning as) then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""
            return $ " WARNING: ignoring the following wellformedness errors: " ++(renderDoc $ prettyWfErrorReport report)

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
          (checkWellformedness thy) thy (elem "quit-on-warning" (quitOnWarning as))

      lemmaSelector :: Lemma p -> Bool
      lemmaSelector lem =
          any (`isPrefixOf` get lName lem) lemmaNames
        where
          lemmaNames :: [String]
          lemmaNames = findArg "prove" as

      -- replace all annotated sorrys with the configured autoprover.
      prover :: Prover
      prover | argExists "prove" as =
                  replaceSorryProver $ runAutoProver $ constructAutoProver as
             | otherwise            = mempty
             
-- | Close a diff theory according to arguments.
closeDiffThy :: Arguments -> OpenDiffTheory -> IO ClosedDiffTheory
closeDiffThy as thy0 = do
  -- FIXME: wf-check is at the wrong position here. Needs to be more
  -- fine-grained.
  let thy2 = wfCheckDiff thy0
  -- close and prove
  cthy <- closeDiffTheory (maudePath as) (addDefaultDiffLemma (addProtoRuleLabels thy2))
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
      wfCheckDiff :: OpenDiffTheory -> OpenDiffTheory
      wfCheckDiff thy =
        noteWellformednessDiff
          (checkWellformednessDiff thy) thy (elem "quit-on-warning" (quitOnWarning as))

      lemmaSelector :: Lemma p -> Bool
      lemmaSelector lem =
          any (`isPrefixOf` get lName lem) lemmaNames
        where
          lemmaNames :: [String]
          lemmaNames = findArg "prove" as

      diffLemmaSelector :: DiffLemma p -> Bool
      diffLemmaSelector lem =
          any (`isPrefixOf` get lDiffName lem) lemmaNames
        where
          lemmaNames :: [String]
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
    ranking 'o' = OracleRanking
    ranking 'O' = OracleSmartRanking
    ranking 'p' = SapicRanking
    ranking 'l' = SapicLivenessRanking
    ranking 'P' = SapicPKCS11Ranking
    ranking 'c' = UsefulGoalNrRanking
    ranking 'C' = GoalNrRanking
    ranking 'i' = InjRanking False
    ranking 'I' = InjRanking True
    ranking r   = error $ render $ fsep $ map text $ words $
      "Unknown goal ranking '" ++ [r] ++ "'. Use one of the following:\
      \ 's' for the smart ranking without loop breakers,\
      \ 'S' for the smart ranking with loop breakers,\
      \ 'o' for oracle ranking,\
      \ 'O' for oracle ranking with smart ranking without loop breakers as underlying baseline,\
      \ 'p' for the smart ranking optimized for translations coming from SAPIC (http://sapic.gforge.inria.fr),\
      \ 'l' for the smart ranking optimized for translations coming from SAPIC proving liveness properties,\
      \ 'P' for the smart ranking optimized for a specific model of PKCS11, translated using SAPIC,\
      \ 'i' for the ranking modified for the proof of stateful injective protocols without loop breakers,\
      \ 'I' for the ranking modified for the proof of stateful injective protocols with loop breakers,\
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
        _                        -> [SmartDiffRanking]

    ranking 's' = SmartRanking False
    ranking 'S' = SmartRanking True
    ranking 'o' = OracleRanking
    ranking 'O' = OracleSmartRanking
    ranking 'c' = UsefulGoalNrRanking
    ranking 'C' = GoalNrRanking
    ranking r   = error $ render $ fsep $ map text $ words $
      "Unknown goal ranking '" ++ [r] ++ "'. Use one of the following:\
      \ 's' for the smart ranking without loop breakers,\
      \ 'S' for the smart ranking with loop breakers,\
      \ 'o' for oracle ranking,\
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
dhIntruderVariantsFile = "data/intruder_variants_dh.spthy"

-- | The name of the intruder variants file.
bpIntruderVariantsFile :: FilePath
bpIntruderVariantsFile = "data/intruder_variants_bp.spthy"

-- | Construct the DH intruder variants for the given maude signature.
mkDhIntruderVariants :: MaudeSig -> [IntrRuleAC]
mkDhIntruderVariants msig =
    either (error . show) id  -- report errors lazily through 'error'
  $ parseIntruderRules msig dhIntruderVariantsFile
                $(embedFile "data/intruder_variants_dh.spthy")

-- | Construct the BP intruder variants for the given maude signature.
mkBpIntruderVariants :: MaudeSig -> [IntrRuleAC]
mkBpIntruderVariants msig =
    either (error . show) id  -- report errors lazily through 'error'
  $ parseIntruderRules msig bpIntruderVariantsFile
                $(embedFile "data/intruder_variants_bp.spthy")

-- | Add the variants of the message deduction rule. Uses built-in cached
-- files for the variants of the message deduction rules for Diffie-Hellman
-- exponentiation and Bilinear-Pairing.
addMessageDeductionRuleVariants :: OpenTheory -> IO OpenTheory
                                -- TODO (SM): drop use of IO here.
addMessageDeductionRuleVariants thy0
  | enableBP msig = addIntruderVariants [ mkDhIntruderVariants
                                        , mkBpIntruderVariants ]
  | enableDH msig = addIntruderVariants [ mkDhIntruderVariants ]
  | otherwise     = return thy
  where
    msig         = get (sigpMaudeSig . thySignature) thy0
    rules        = subtermIntruderRules False msig ++ specialIntruderRules False
                   ++ if enableMSet msig then multisetIntruderRules else []
    thy          = addIntrRuleACs rules thy0
    addIntruderVariants mkRuless = do
        return $ addIntrRuleACs (concatMap ($ msig) mkRuless) thy

-- | Add the variants of the message deduction rule. Uses the cached version
-- of the @"intruder_variants_dh.spthy"@ file for the variants of the message
-- deduction rules for Diffie-Hellman exponentiation.
addMessageDeductionRuleVariantsDiff :: OpenDiffTheory -> IO OpenDiffTheory
addMessageDeductionRuleVariantsDiff thy0
  | enableBP msig = addIntruderVariantsDiff [ mkDhIntruderVariants
                                            , mkBpIntruderVariants ]
  | enableDH msig = addIntruderVariantsDiff [ mkDhIntruderVariants ]
  | otherwise     = return $ addIntrRuleLabels thy
  where
    msig         = get (sigpMaudeSig . diffThySignature) thy0
    rules diff'  = subtermIntruderRules diff' msig ++ specialIntruderRules diff'
                    ++ if enableMSet msig then multisetIntruderRules else []
    thy          = addIntrRuleACsDiffBoth (rules False) $ addIntrRuleACsDiffBothDiff (rules True) thy0
    addIntruderVariantsDiff mkRuless = do
        return $ addIntrRuleLabels (addIntrRuleACsDiffBothDiff (concatMap ($ msig) mkRuless) $ addIntrRuleACsDiffBoth (concatMap ($ msig) mkRuless) thy)
