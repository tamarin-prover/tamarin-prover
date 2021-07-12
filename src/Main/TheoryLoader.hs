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
import           Data.List                           (isPrefixOf,intersperse)
import           Data.Map                            (keys)
-- import           Data.Monoid
import           Data.FileEmbed                      (embedFile)

-- import           Control.Basics
import           Control.Category

import           System.Console.CmdArgs.Explicit

import           Theory
import           Theory.Text.Parser                  (parseIntruderRules, parseOpenTheory, parseOpenTheoryString, parseOpenDiffTheory, parseOpenDiffTheoryString)
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.IntruderRules          (specialIntruderRules, subtermIntruderRules
                                                     , multisetIntruderRules, xorIntruderRules)
import           Theory.Tools.Wellformedness
import           Sapic
import           Main.Console
import           Main.Environment

import           Text.Parsec                hiding ((<|>),try)
import           Safe


------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------


-- | Flags for loading a theory.
theoryLoadFlags :: [Flag Arguments]
theoryLoadFlags =
  [ flagOpt "" ["prove"] (updateArg "prove") "LEMMAPREFIX*|LEMMANAME"
      "Attempt to prove all lemmas that start with LEMMAPREFIX or the lemma which name is LEMMANAME"

  , flagOpt "dfs" ["stop-on-trace"] (updateArg "stopOnTrace") "DFS|BFS|SEQDFS|NONE"
      "How to search for traces (default DFS)"

  , flagOpt "5" ["bound", "b"] (updateArg "bound") "INT"
      "Bound the depth of the proofs"

  , flagOpt (prettyGoalRanking $ head $ defaultRankings False)
      ["heuristic"] (updateArg "heuristic") ("(" ++ intersperse '|' (keys goalRankingIdentifiers) ++ ")+")
      ("Sequence of goal rankings to use (default '" ++ prettyGoalRanking (head $ defaultRankings False) ++ "')")

  , flagOpt "summary" ["partial-evaluation"] (updateArg "partialEvaluation")
      "SUMMARY|VERBOSE"
      "Partially evaluate multiset rewriting system"

  , flagOpt "" ["defines","D"] (updateArg "defines") "STRING"
      "Define flags for pseudo-preprocessor"

  , flagNone ["diff"] (addEmptyArg "diff")
      "Turn on observational equivalence mode using diff terms"

  , flagNone ["quit-on-warning"] (addEmptyArg "quit-on-warning")
      "Strict mode that quits on any warning that is emitted"

  , flagNone ["auto-sources"] (addEmptyArg "auto-sources")
      "Try to auto-generate sources lemmas"

  , flagOpt (oraclePath defaultOracle) ["oraclename"] (updateArg "oraclename") "FILE"
      ("Path to the oracle heuristic (default '" ++ oraclePath defaultOracle ++ "')")

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
loadOpenThy :: Arguments -> FilePath -> IO OpenTranslatedTheory
loadOpenThy as inFile =  do
    thy <- parseOpenTheory (diff as ++ defines as ++ quitOnWarning as) inFile
    thy' <-  Sapic.translate thy
    return thy'

-- | Load a closed theory.
loadClosedDiffThy :: Arguments -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThy as inFile = do
  thy0 <- loadOpenDiffThy as inFile
  thy1 <- addMessageDeductionRuleVariantsDiff thy0
  closeDiffThy as thy1

-- | Load a closed theory.
loadClosedThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedThy as inFile = loadOpenThy as inFile >>= closeThy as

-- | Load a closed theory and report on well-formedness errors.
loadClosedThyWfReport :: Arguments -> FilePath -> IO ClosedTheory
loadClosedThyWfReport as inFile = do
    thy0 <- loadOpenThy as inFile
    thy <- addMessageDeductionRuleVariants thy0
    sig <- toSignatureWithMaude (maudePath as) $ get thySignature thy
    -- report
    case checkWellformedness thy sig of
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
    closeThyWithMaude sig as thy

-- | Load a closed diff theory and report on well-formedness errors.
loadClosedDiffThyWfReport :: Arguments -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThyWfReport as inFile = do
    thy0 <- loadOpenDiffThy as inFile
    thy1 <- addMessageDeductionRuleVariantsDiff thy0
    sig <- toSignatureWithMaude (maudePath as) $ get diffThySignature thy1
    -- report
    case checkWellformednessDiff thy1 sig of
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
    closeDiffThyWithMaude sig as thy1

loadClosedThyString :: Arguments -> String -> IO (Either String ClosedTheory)
loadClosedThyString as input =
    case parseOpenTheoryString (defines as) input of
        Left err  -> return $ Left $ "parse error: " ++ show err
        Right thy -> do
            thy' <- Sapic.translate thy
            Right <$> closeThy as thy' -- No "return" because closeThy gives IO (ClosedTheory)


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

-- | Load a close theory and only report on well-formedness errors or translation errors
reportOnClosedThyStringWellformedness :: Arguments -> String -> IO String
reportOnClosedThyStringWellformedness as input =
    case loadOpenThyString as input of
      Left  err   -> return $ "parse error: " ++ show err
      Right thy -> do
            thy' <- Sapic.translate thy
            sig <- toSignatureWithMaude (maudePath as) $ get thySignature thy'
            case checkWellformedness thy' sig of
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
        sig <- toSignatureWithMaude (maudePath as) $ get diffThySignature thy1
        -- report
        case checkWellformednessDiff thy1 sig of
          []     -> return ""
          report -> do
            if elem "quit-on-warning" (quitOnWarning as) then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""
            return $ " WARNING: ignoring the following wellformedness errors: " ++(renderDoc $ prettyWfErrorReport report)


-- | Close a theory according to arguments.
closeThy :: Arguments -> OpenTranslatedTheory -> IO ClosedTheory
closeThy as thy0 = do
  thy1 <- addMessageDeductionRuleVariants thy0
  sig <- toSignatureWithMaude (maudePath as) $ get thySignature thy1
  closeThyWithMaude sig as thy1

-- | Close a theory according to arguments.
closeThyWithMaude :: SignatureWithMaude -> Arguments -> OpenTranslatedTheory -> IO ClosedTheory
closeThyWithMaude sig as thy0 = do
  -- FIXME: wf-check is at the wrong position here. Needs to be more
  -- fine-grained.
  let thy1 = wfCheck thy0
  -- close and prove
  let cthy = closeTheoryWithMaude sig thy1 (argExists "auto-sources" as)
  return $ proveTheory lemmaSelector prover $ partialEvaluation cthy
    where
      -- apply partial application
      ----------------------------
      partialEvaluation = case map toLower <$> findArg "partialEvaluation" as of
        Just "verbose" -> applyPartialEvaluation Tracing (argExists "auto-sources" as)
        Just _         -> applyPartialEvaluation Summary (argExists "auto-sources" as)
        _              -> id

      -- wellformedness check
      -----------------------
      wfCheck :: OpenTranslatedTheory -> OpenTranslatedTheory
      wfCheck thy =
        noteWellformedness
          (checkWellformedness thy sig) thy (elem "quit-on-warning" (quitOnWarning as))

      lemmaSelector :: Lemma p -> Bool
      lemmaSelector lem =
          if ((lastMay $ headDef "" lemmaNames) == Just('*'))
            then any (`isPrefixOf` get lName lem) [init $ head lemmaNames]
            else
              if (lemmaNames == [""])
                then any (`isPrefixOf` get lName lem) lemmaNames
                else any ( == get lName lem) lemmaNames
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
  sig <- toSignatureWithMaude (maudePath as) $ get diffThySignature thy0
  closeDiffThyWithMaude sig as thy0

-- | Close a diff theory according to arguments.
closeDiffThyWithMaude :: SignatureWithMaude -> Arguments -> OpenDiffTheory -> IO ClosedDiffTheory
closeDiffThyWithMaude sig as thy0 = do
  -- FIXME: wf-check is at the wrong position here. Needs to be more
  -- fine-grained.
  let thy2 = wfCheckDiff thy0
  -- close and prove
  let cthy = closeDiffTheoryWithMaude sig (addDefaultDiffLemma thy2) (argExists "auto-sources" as)
  return $ proveDiffTheory lemmaSelector diffLemmaSelector prover diffprover $ partialEvaluation cthy
    where
      -- apply partial application
      ----------------------------
      partialEvaluation = case map toLower <$> findArg "partialEvaluation" as of
        Just "verbose" -> applyPartialEvaluationDiff Tracing (argExists "auto-sources" as)
        Just _         -> applyPartialEvaluationDiff Summary (argExists "auto-sources" as)
        _              -> id

      -- wellformedness check
      -----------------------
      wfCheckDiff :: OpenDiffTheory -> OpenDiffTheory
      wfCheckDiff thy =
        noteWellformednessDiff
          (checkWellformednessDiff thy sig) thy (elem "quit-on-warning" (quitOnWarning as))

      lemmaSelector :: Lemma p -> Bool
      lemmaSelector lem =
          if ((lastMay $ headDef "" lemmaNames) == Just('*'))
            then any (`isPrefixOf` get lName lem) [init $ head lemmaNames]
            else
              if (lemmaNames == [""])
                then any (`isPrefixOf` get lName lem) lemmaNames
                else any ( == get lName lem) lemmaNames
        where
          lemmaNames :: [String]
          lemmaNames = findArg "prove" as

      diffLemmaSelector :: DiffLemma p -> Bool
      diffLemmaSelector lem =
          if ((lastMay $ headDef "" lemmaNames) == Just('*'))
            then any (`isPrefixOf` get lDiffName lem) [init $ head lemmaNames]
            else
              if (lemmaNames == [""])
                then any (`isPrefixOf` get lDiffName lem) lemmaNames
                else any ( == get lDiffName lem) lemmaNames
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
    AutoProver heuristic proofBound stopOnTrace
  where
    -- handles to relevant arguments
    --------------------------------
    proofBound      = read <$> findArg "bound" as

    heuristic = case findArg "heuristic" as of
        Just rawRankings@(_:_) -> Just $ roundRobinHeuristic
                                       $ map (mapOracleRanking (maybeSetOracleRelPath (findArg "oraclename" as)) . charToGoalRanking) rawRankings
        Just []                -> error "--heuristic: at least one ranking must be given"
        _                      -> Nothing

    stopOnTrace = case (map toLower) <$> findArg "stopOnTrace" as of
      Nothing       -> CutDFS
      Just "dfs"    -> CutDFS
      Just "none"   -> CutNothing
      Just "bfs"    -> CutBFS
      Just "seqdfs" -> CutSingleThreadDFS
      Just other    -> error $ "unknown stop-on-trace method: " ++ other

-- | Construct an 'AutoProver' from the given arguments (--bound,
-- --stop-on-trace).
constructAutoDiffProver :: Arguments -> AutoProver
constructAutoDiffProver as =
    AutoProver heuristic proofBound stopOnTrace
  where
    -- handles to relevant arguments
    --------------------------------
    proofBound      = read <$> findArg "bound" as

    heuristic = case findArg "heuristic" as of
        Just rawRankings@(_:_) -> Just $ roundRobinHeuristic
                                       $ map (mapOracleRanking (maybeSetOracleRelPath (findArg "oraclename" as)) . charToGoalRankingDiff) rawRankings
        Just []                -> error "--heuristic: at least one ranking must be given"
        _                      -> Nothing

    stopOnTrace = case (map toLower) <$> findArg "stopOnTrace" as of
      Nothing       -> CutDFS
      Just "dfs"    -> CutDFS
      Just "none"   -> CutNothing
      Just "bfs"    -> CutBFS
      Just "seqdfs" -> CutSingleThreadDFS
      Just other    -> error $ "unknown stop-on-trace method: " ++ other


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
addMessageDeductionRuleVariants :: OpenTranslatedTheory -> IO OpenTranslatedTheory
                                -- TODO (SM): drop use of IO here.
addMessageDeductionRuleVariants thy0
  | enableBP msig = addIntruderVariants [ mkDhIntruderVariants
                                        , mkBpIntruderVariants ]
  | enableDH msig = addIntruderVariants [ mkDhIntruderVariants ]
  | otherwise     = return thy
  where
    msig         = get (sigpMaudeSig . thySignature) thy0
    rules        = subtermIntruderRules False msig ++ specialIntruderRules False
                   ++ (if enableMSet msig then multisetIntruderRules else [])
                   ++ (if enableXor msig then xorIntruderRules else [])
    thy          = addIntrRuleACsAfterTranslate rules thy0
    addIntruderVariants mkRuless = do
        return $ addIntrRuleACsAfterTranslate (concatMap ($ msig) mkRuless) thy

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
                    ++ (if enableMSet msig then multisetIntruderRules else [])
                    ++ (if enableXor msig then xorIntruderRules else [])
    thy          = addIntrRuleACsDiffBoth (rules False) $ addIntrRuleACsDiffBothDiff (rules True) thy0
    addIntruderVariantsDiff mkRuless = do
        return $ addIntrRuleLabels (addIntrRuleACsDiffBothDiff (concatMap ($ msig) mkRuless) $ addIntrRuleACsDiffBoth (concatMap ($ msig) mkRuless) thy)
