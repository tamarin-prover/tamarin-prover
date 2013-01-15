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
import           Theory.Text.Parser
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
      fmap (proveTheory lemmaSelector prover . partialEvaluation)
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
{-
------------------------------------------------------------------------------
-- Message deduction variants cached in files
------------------------------------------------------------------------------

-- | The name of the intruder variants file.
intruderVariantsFile :: FilePath
intruderVariantsFile = "intruder_variants_dh.spthy"

-- | Add the variants of the message deduction rule. Uses the cached version
-- of the @"intruder_variants_dh.spthy"@ file for the variants of the message
-- deduction rules for Diffie-Hellman exponentiation.
addMessageDeductionRuleVariants :: OpenTheory -> IO OpenTheory
addMessageDeductionRuleVariants thy0
  | enableDH msig = do
      variantsFile <- getDataFileName intruderVariantsFile
      ifM (doesFileExist variantsFile)
          (do dhVariants <- parseIntruderRulesDH variantsFile
              return $ addIntrRuleACs dhVariants thy
          )
          (error $ "could not find intruder message deduction theory '"
                     ++ variantsFile ++ "'")
  | otherwise = return thy
  where
    msig         = get (sigpMaudeSig . thySignature) thy0
    rules        = subtermIntruderRules msig ++ specialIntruderRules
    thy          = addIntrRuleACs rules thy0
-}