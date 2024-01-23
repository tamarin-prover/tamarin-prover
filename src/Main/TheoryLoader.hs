{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Theory loading infrastructure.
module Main.TheoryLoader (
  -- * Static theory loading settings
    theoryLoadFlags
  , lemmaSelector

  , TheoryLoadOptions(..)
  , oProveMode
  , oDiffMode
  , oHeuristic
  , oOutputModule
  , oMaudePath
  , oVerboseMode
  , oParseOnlyMode
  , defaultTheoryLoadOptions
  , ArgumentError(..)
  , mkTheoryLoadOptions

  , TheoryLoadError(..)
  , loadTheory
  , translateAndCheckTheory
  , prettyOpenTheoryByModule
  , closeTheory

  -- ** Constructing automatic prover
  , constructAutoProver

  -- ** Cached Message Deduction Rule Variants
  , dhIntruderVariantsFile
  , bpIntruderVariantsFile
  , addMessageDeductionRuleVariants

  ) where

-- import           Debug.Trace

import           Prelude                             hiding (id, (.))

import           Data.Char                           (toLower)
import           Data.Label
import           Data.List                           (isPrefixOf, intercalate, find)
import qualified Data.Set
import           Data.Maybe                          (fromMaybe, fromJust, isJust, isNothing)
import           Data.Map                            (keys)
import           Data.FileEmbed                      (embedFile)
import qualified Data.Label as L
import           Data.Bifunctor (Bifunctor(bimap))
import           Data.Bitraversable (Bitraversable(bitraverse))

import           Control.Category
import           Control.Exception (evaluate)
import           Control.DeepSeq (force)

import           System.Console.CmdArgs.Explicit
import           System.Timeout (timeout)

import           Theory hiding (transReport, closeTheory)
import           Theory.Text.Parser                  (parseIntruderRules, theory, diffTheory)
import           Theory.Text.Parser.Token
import qualified Theory.Text.Pretty as Pretty
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.IntruderRules          (specialIntruderRules, subtermIntruderRules
                                                     , multisetIntruderRules, xorIntruderRules)
import           Theory.Tools.Wellformedness
import           Theory.Tools.MessageDerivationChecks
import           Theory.Module

import           TheoryObject                        (diffThyOptions, diffTheoryConfigBlock, theoryConfigBlock)

import qualified Sapic
import qualified Export
import           Main.Console

import           Text.Read (readEither)
import           Text.Parsec                hiding ((<|>),try,parse)

import           Safe

import           Items.LemmaItem (HasLemmaName, HasLemmaAttributes)
import           Items.OptionItem                    (openChainsLimit,saturationLimit,lemmasToProve,verboseOption)

import           Control.Monad.Except
import           Control.Monad.Catch (MonadCatch)


import qualified Accountability as Acc
import qualified Accountability.Generation as Acc

import           GHC.Records (HasField(getField))
import           GHC.Num (integerFromInt)

import           Debug.Trace

------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------

-----------------------------------------------
-- Flags
-----------------------------------------------

-- | Flags for loading a theory.
theoryLoadFlags :: [Flag Arguments]
theoryLoadFlags =
  [ flagOpt "" ["prove"] (updateArg "prove") "LEMMAPREFIX*|LEMMANAME"
      "Attempt to prove all lemmas that start with LEMMAPREFIX or the lemma which name is LEMMANAME (can be repeated)."

  , flagOpt "" ["lemma"] (updateArg "lemma") "LEMMAPREFIX*|LEMMANAME"
      "Select lemma(s) by name or prefx (can be repeated)"

  , flagOpt "dfs" ["stop-on-trace"] (updateArg "stop-on-trace") "DFS|BFS|SEQDFS|NONE"
      "How to search for traces (default DFS)"

  , flagOpt "5" ["bound", "b"] (updateArg "bound") "INT"
      "Bound the depth of the proofs"

  ,  flagOpt (prettyGoalRanking $ head $ defaultRankings False)
      ["heuristic"] (updateArg "heuristic") ("(" ++ (intercalate "|" $ keys goalRankingIdentifiers) ++ ")+")
      ("Sequence of goal rankings to use (default '" ++ prettyGoalRanking (head $ defaultRankings False) ++ "')")

  , flagOpt "summary" ["partial-evaluation"] (updateArg "partial-evaluation")
      "SUMMARY|VERBOSE"
      "Partially evaluate multiset rewriting system"

  , flagOpt "" ["defines","D"] (updateArg "defines") "STRING"
      "Define flags for pseudo-preprocessor."

  , flagNone ["diff"] (addEmptyArg "diff")
      "Turn on observational equivalence mode using diff terms."

  , flagNone ["quit-on-warning"] (addEmptyArg "quit-on-warning")
      "Strict mode that quits on any warning that is emitted."

  , flagNone ["auto-sources"] (addEmptyArg "auto-sources")
      "Try to auto-generate sources lemmas"

  , flagOpt "" ["oraclename"] (updateArg "oraclename") "FILE"
      ("Path to the oracle heuristic (default '" ++ "./theory_filename.oracle" ++ "', fallback '" ++ "./oracle" ++ "')")

  , flagNone ["quiet"] (addEmptyArg "quiet")
      "Do not display computation steps of oracle or tactic."

  , flagNone ["verbose", "v"] (addEmptyArg "verbose")
      "Display full information when calculating proof."

  , flagOpt "10" ["open-chains","c"] (updateArg "OpenChainsLimit" ) "PositiveInteger"
      "Limits the number of open chains to be resoled during precomputations (default 10)"

  , flagOpt "5" ["saturation","s"] (updateArg "SaturationLimit" ) "PositiveInteger"
      "Limits the number of saturations during precomputations (default 5)"

  , flagOpt "5" ["derivcheck-timeout","d"] (updateArg "derivcheck-timeout" ) "INT"
      "Set timeout for message derivation checks in sec (default 5). 0 deactivates check."


--  , flagOpt "" ["diff"] (updateArg "diff") "OFF|ON"
--      "Turn on observational equivalence (default OFF)."
  ]

-----------------------------------------------
-- TheoryLoadOptions
-----------------------------------------------

data TheoryLoadOptions = TheoryLoadOptions {
    _oProveMode         :: Bool
  , _oLemmaNames        :: [String]
  , _oStopOnTrace       :: Maybe SolutionExtractor
  , _oProofBound        :: Maybe Int
  , _oHeuristic         :: Maybe (Heuristic ProofContext)
  , _oPartialEvaluation :: Maybe EvaluationStyle
  , _oDefines           :: [String]
  , _oDiffMode          :: Bool
  , _oQuitOnWarning     :: Bool
  , _oAutoSources       :: Bool
  , _oVerboseMode       :: Bool
  , _oOutputModule      :: ModuleType -- Note: This flag is only used for batch mode.
  , _oMaudePath         :: FilePath -- FIXME: Other functions defined in Environment.hs
  , _oParseOnlyMode     :: Bool
  , _oOpenChain         :: Integer
  , _oSaturation        :: Integer
  , _oDerivationChecks  :: Int
} deriving Show
$(mkLabels [''TheoryLoadOptions])

defaultTheoryLoadOptions :: TheoryLoadOptions
defaultTheoryLoadOptions = TheoryLoadOptions {
    _oProveMode         = False
  , _oLemmaNames        = []
  , _oStopOnTrace       = Nothing
  , _oProofBound        = Nothing
  , _oHeuristic         = Nothing
  , _oPartialEvaluation = Nothing
  , _oDefines           = []
  , _oDiffMode          = False
  , _oQuitOnWarning     = False
  , _oAutoSources       = False
  , _oVerboseMode       = False
  , _oOutputModule      = ModuleMsr
  , _oMaudePath         = "maude"
  , _oParseOnlyMode     = False
  , _oOpenChain         = 10
  , _oSaturation        = 5
  , _oDerivationChecks  = 5
}

toParserFlags :: TheoryLoadOptions -> [String]
toParserFlags thyOpts = concat
  [ [ "diff" |  L.get oDiffMode thyOpts ]
  , L.get oDefines thyOpts
  , [ "quit-on-warning" | L.get oQuitOnWarning thyOpts ] ]

data ArgumentError = ArgumentError String

mkTheoryLoadOptions :: MonadError ArgumentError m => Arguments -> m TheoryLoadOptions
mkTheoryLoadOptions as = TheoryLoadOptions
                         <$> proveMode
                         <*> lemmaNames
                         <*> (stopOnTrace as)
                         <*> proofBound
                         <*> heuristic
                         <*> partialEvaluation
                         <*> defines
                         <*> diffMode
                         <*> quitOnWarning
                         <*> autoSources
                         <*> verboseMode
                         <*> outputModule
                         <*> (return $ maudePath as)
                         <*> parseOnlyMode
                         <*> openchain
                         <*> saturation
                         <*> deriv
  where
    proveMode  = return $ argExists "prove" as
    lemmaNames = return $ findArg "prove" as ++ findArg "lemma" as

    stopOnTrace = case map toLower <$> findArg "stop-on-trace" as of
      Nothing       -> return CutDFS
      Just "dfs"    -> return CutDFS
      Just "none"   -> return CutNothing
      Just "bfs"    -> return CutBFS
      Just "seqdfs" -> return CutSingleThreadDFS
      Just unknown  -> throwError $ ArgumentError ("unknown stop-on-trace method: " ++ unknown)

    parseIntArg args defaultValue conv errMsg = case args of
      []    -> return defaultValue
      (x:_) -> case (readEither x :: Either String Int) of
        Left  _ -> throwError $ ArgumentError errMsg
        Right i -> return $ conv i
      -- FIXME : provide option to handle potential error without crash (ie, take default value and raise error but continue)

    proofBound = parseIntArg (findArg "bound" as) Nothing Just "bound: invalid bound given"

    heuristic = case findArg "heuristic" as of
        Just rawRankings@(_:_) -> return $ Just $ roundRobinHeuristic
                                         $ map (mapOracleRanking (maybeSetOracleRelPath oraclename)) (filterHeuristic (argExists "diff" as) rawRankings)
        Just []                -> throwError $ ArgumentError "heuristic: at least one ranking must be given"
        _                      -> return Nothing
    oraclename = case findArg "oraclename" as of
      Just "" -> Nothing
      name    -> name
    --toGoalRanking | argExists "diff" as = stringToGoalRankingDiff
    --              | otherwise           = stringToGoalRanking

    partialEvaluation = case map toLower <$> findArg "partial-evaluation" as of
      Just "summary" -> return $ Just Summary
      Just "verbose" -> return $ Just Tracing
      Just _         -> throwError $ ArgumentError "partial-evaluation: unknown option"
      Nothing        -> return   Nothing

    defines       = return $ findArg "defines" as
    diffMode      = return $ argExists "diff" as
    verboseMode   = return $ argExists "verbose" as
    quitOnWarning = return $ argExists "quit-on-warning" as
    autoSources   = return $ argExists "auto-sources" as

    outputModule = case findArg "outModule" as of
      Just str -> case find ((str ==) . show) [minBound..] of
        Just m -> return m
        _       -> throwError $ ArgumentError "output mode not supported."
      Nothing   -> return $ L.get oOutputModule defaultTheoryLoadOptions

    parseOnlyMode = return $ argExists "parseOnly" as

    chain = findArg "OpenChainsLimit" as
    chainDefault = L.get oOpenChain defaultTheoryLoadOptions
    openchain = parseIntArg chain chainDefault integerFromInt "OpenChainsLimit: invalid bound given"

    sat = findArg "SaturationLimit" as
    satDefault = L.get oSaturation defaultTheoryLoadOptions
    saturation = parseIntArg sat satDefault integerFromInt "SaturationLimit: invalid bound given"
    
    derivchecks = findArg "derivcheck-timeout" as
    derivDefault = L.get oDerivationChecks defaultTheoryLoadOptions
    deriv = parseIntArg derivchecks derivDefault id "derivcheck-timeout: invalid bound given"

stopOnTrace :: MonadError ArgumentError m => Arguments -> m (Maybe SolutionExtractor)
stopOnTrace as = case map toLower <$> findArg "stop-on-trace" as of
  Just "dfs"    -> return $ Just CutDFS
  Just "none"   -> return $ Just CutNothing
  Just "bfs"    -> return $ Just CutBFS
  Just "seqdfs" -> return $ Just CutSingleThreadDFS
  Just unknown  -> throwError $ ArgumentError ("unknown stop-on-trace method: " ++ unknown)
  Nothing       -> return Nothing

lemmaSelectorByModule :: HasLemmaAttributes l => TheoryLoadOptions -> l -> Bool
lemmaSelectorByModule thyOpt lem = case lemmaModules of
    [] -> True -- default to true if no modules (or only empty ones) are set
    _  -> (L.get oOutputModule thyOpt) `elem` lemmaModules
    where
        lemmaModules = concat [ m | LemmaModule m <- getField @"lAttributes" lem]

-- | quiet flag in the argument
--quiet :: Arguments -> [String]
--quiet as = if (argExists "quiet" as) then ["quiet"] else []

-- | Select lemmas for proving
lemmaSelector :: HasLemmaName l => TheoryLoadOptions -> l -> Bool
lemmaSelector thyOpts lem
  | null lemmaNames = True
  | lemmaNames == [""] = True
  | lemmaNames == ["",""] = True
  | otherwise = any lemmaMatches lemmaNames
  where
      lemmaNames :: [String]
      lemmaNames = L.get oLemmaNames thyOpts

      lemmaMatches :: String -> Bool
      lemmaMatches pattern
        | lastMay pattern == Just '*' = init pattern `isPrefixOf` getField @"lName" lem
        | otherwise = getField @"lName" lem == pattern

data TheoryLoadError =
    ParserError ParseError
  | WarningError WfErrorReport

instance Show TheoryLoadError
  where
    show (ParserError e) = show e
    show (WarningError e) = Pretty.render (prettyWfErrorReport e)

-- | Load an open theory from a string with the given options.
loadTheory :: Monad m => TheoryLoadOptions -> String -> FilePath -> ExceptT TheoryLoadError m (Either OpenTheory OpenDiffTheory)
loadTheory thyOpts input inFile = do
    thy <- withExceptT ParserError $ liftEither $ unwrapError $ bimap parse parse thyParser
    traceM ("[Theory " ++ theoryName thy ++ "] Theory loaded")
    return $ addParamsOptions thyOpts thy
  where
    thyParser | isDiffMode = Right $ diffTheory $ Just inFile
              | otherwise  = Left  $ theory     $ Just inFile

    parse p = parseString (toParserFlags thyOpts) inFile p input

    isDiffMode   = L.get oDiffMode thyOpts

    unwrapError (Left (Left e)) = Left e
    unwrapError (Left (Right v)) = Right $ Left v
    unwrapError (Right (Left e)) = Left e
    unwrapError (Right (Right v)) = Right $ Right v
    theoryName = either (L.get thyName) (L.get diffThyName)

-- | Process an open theory based on the specified output module.
processOpenTheory :: MonadCatch m => TheoryLoadOptions -> OpenTheory -> m OpenTheory
processOpenTheory thyOpts = case modType of
  ModuleSpthy               -> return
  ModuleSpthyTyped          -> Sapic.typeTheory
  ModuleMsr                 -> Sapic.typeTheory >=> Sapic.translate >=> Acc.translate >=> (return . filterLemma lemmas)
  ModuleProVerifEquivalence -> Sapic.typeTheory -- Type theory here to catch errors.
  ModuleProVerif            -> Sapic.typeTheory -- Type theory here to catch errors.
  ModuleDeepSec             -> Sapic.typeTheory
  where
    modType = L.get oOutputModule thyOpts
    lemmas = lemmaSelector thyOpts

-- | Translate an open theory.
translateTheory :: MonadCatch m => MonadError TheoryLoadError m => TheoryLoadOptions -> Either OpenTheory OpenDiffTheory -> m (WfErrorReport, Either OpenTheory OpenDiffTheory)
translateTheory thyOpts thy = do
    traceM ("[Theory " ++ theoryName thy ++ "] Theory translated")
    let report = either (\t -> Sapic.checkWellformedness t ++ Acc.checkWellformedness t) (const []) thy
    transThy <- withTheory (processOpenTheory thyOpts) thy
    return (report, transThy)
  where
    withTheory f = bitraverse f return
    theoryName = either (L.get thyName) (L.get diffThyName)

-- | Perform wellformedness and deducability checks on a theory.
checkTranslatedTheory :: MonadIO m => MonadError TheoryLoadError m => TheoryLoadOptions -> SignatureWithMaude -> Either OpenTranslatedTheory OpenDiffTheory -> m ((WfErrorReport, Either OpenTranslatedTheory OpenDiffTheory))
checkTranslatedTheory thyOpts sign thy = do
  let transReport = either (`checkWellformedness` sign)
                           (`checkWellformednessDiff` sign) thy

  deducThy <- bitraverse (return . addMessageDeductionRuleVariants)
                         (return . addMessageDeductionRuleVariantsDiff) thy


  variableReport <- case compare derivChecks 0 of
    EQ -> pure $ Just []
    _ -> do
      traceM ("[Theory " ++ theoryName thy ++ "] Derivation checks started")
      derivCheckSignature <- liftIO $ toSignatureWithMaude (get oMaudePath thyOpts) $ maudePublicSig (toSignaturePure sign)
      rep <- liftIO $ timeout (1000000 * derivChecks) $ evaluate . force $ either (\t -> checkVariableDeducability t derivCheckSignature autoSources defaultProver)
             (\t-> diffCheckVariableDeducability t derivCheckSignature autoSources defaultProver defaultDiffProver) deducThy
      traceM ("[Theory " ++ theoryName thy ++ "] Derivation checks ended")
      return rep

  let report = transReport ++ fromMaybe derivTimeoutMsg  variableReport

  return (report, deducThy)
  where
    autoSources = L.get oAutoSources thyOpts
    derivChecks = L.get oDerivationChecks thyOpts
    derivTimeoutMsg = [(underlineTopic "Derivation Checks"
                      , Pretty.vcat [
                          Pretty.text "Derivation checks timed out."
                        , Pretty.text "Use --derivcheck-timeout=INT to configure timeout."
                        , Pretty.text "Set to 0 to deactivate for no timeout." ])]

    defaultProver = replaceSorryProver $ runAutoProver $ constructAutoProver defaultTheoryLoadOptions
    defaultDiffProver = replaceDiffSorryProver $ runAutoDiffProver $ constructAutoProver defaultTheoryLoadOptions
    maudePublicSig s = Signature $ (getSignature s)
      {stFunSyms = makepublic (stFunSyms (getSignature s))
      , funSyms = makepublicsym (funSyms (getSignature s))
      , irreducibleFunSyms = makepublicsym (irreducibleFunSyms (getSignature s))
      , reducibleFunSyms = makepublicsym (reducibleFunSyms (getSignature s))}
    getSignature =  Data.Label.get sigpMaudeSig
    makepublic = Data.Set.map (\(name, (int, _, construct)) -> (name,(int, Public, construct)))
    makepublicsym  = Data.Set.map (\el -> case el of
      NoEq (name, (int, _, constr)) -> NoEq (name,(int, Public, constr))
      x -> x
      )

    theoryName = either (L.get thyName) (L.get diffThyName)

-- | Add report and version information to a theory.
withVersionAndReport :: MonadError TheoryLoadError m => String -> TheoryLoadOptions -> WfErrorReport -> Either (Theory sig1 c1 r1 p1 s) (DiffTheory sig2 c2 r2 r3 p2 p3) -> m (Either (Theory sig1 c1 r1 p1 s) (DiffTheory sig2 c2 r2 r3 p2 p3))
withVersionAndReport version thyOpts report thy = do
    reportThy <- bitraverse (return . addComment     (reportToDoc report))
                            (return . addDiffComment (reportToDoc report)) thy

    versionThy <- bitraverse (return . addComment (Pretty.text version))
                             (return . addDiffComment (Pretty.text version) ) reportThy

    when (quitOnWarning && not (null report)) (throwError $ WarningError report)

    return versionThy
  where
    quitOnWarning = L.get oQuitOnWarning thyOpts

    reportToDoc rep
      | null rep = Pretty.text "All wellformedness checks were successful."
      | otherwise   = Pretty.vsep
                        [ Pretty.text "WARNING: the following wellformedness checks failed!"
                        , prettyWfErrorReport rep ]

-- | Close a translated theory.
closeTranslatedTheory :: MonadError TheoryLoadError m => TheoryLoadOptions -> SignatureWithMaude -> Either OpenTranslatedTheory OpenDiffTheory -> m (Either ClosedTheory ClosedDiffTheory)
closeTranslatedTheory thyOpts sign srcThy = do
  diffLemThy <- withDiffTheory (return . addDefaultDiffLemma) srcThy
  closedThy  <- bitraverse (\t -> return $ closeTheoryWithMaude     sign t autoSources True)
                           (\t -> return $ closeDiffTheoryWithMaude sign t autoSources) diffLemThy
  partialThy <- bitraverse (return . maybe id (`applyPartialEvaluation` autoSources) partialStyle)
                           (return . maybe id (`applyPartialEvaluationDiff` autoSources) partialStyle) closedThy
  provedThy  <- bitraverse (return . proveTheory     (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover)
                           (return . proveDiffTheory (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover diffProver) partialThy

  traceM ("[Theory " ++ theoryName srcThy ++ "] Theory closed")

  return provedThy
  where
    autoSources = L.get oAutoSources thyOpts
    partialStyle = L.get oPartialEvaluation thyOpts

    prover | L.get oProveMode thyOpts = replaceSorryProver $ runAutoProver $ constructAutoProver thyOpts
           | otherwise                = mempty

    diffProver | L.get oProveMode thyOpts = replaceDiffSorryProver $ runAutoDiffProver $ constructAutoProver thyOpts
               | otherwise                = mempty

    withDiffTheory = bitraverse return

    theoryName = either (L.get thyName) (L.get diffThyName)

-- | Translate an open theory, perform checks on the translated theory and finally close it.
closeTheory :: MonadCatch m => MonadIO m => MonadError TheoryLoadError m => String -> TheoryLoadOptions -> SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> m ((WfErrorReport, Either ClosedTheory ClosedDiffTheory))
closeTheory version thyOpts sign srcThy = do
  (preReport, transThy)    <- translateTheory thyOpts srcThy
  removedThy               <- withTheory (return . removeTranslationItems) transThy
  (postReport, checkedThy) <- checkTranslatedTheory thyOpts sign removedThy
  closedThy                <- closeTranslatedTheory thyOpts sign checkedThy
  finalThy                 <- withVersionAndReport version thyOpts (preReport ++ postReport) closedThy

  return (preReport ++ postReport, finalThy)
  where
    withTheory f = bitraverse f return

-- | Translate an open theory and perform checks on the translated theory.
translateAndCheckTheory :: MonadCatch m => MonadIO m => MonadError TheoryLoadError m => String -> TheoryLoadOptions -> SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> m ((WfErrorReport, Either OpenTheory OpenDiffTheory))
translateAndCheckTheory version thyOpts sign srcThy = do
  (preReport, transThy) <- translateTheory thyOpts srcThy
  removedThy            <- withTheory (return . removeTranslationItems) transThy
  (postReport, _)       <- checkTranslatedTheory thyOpts sign removedThy
  finalThy              <- withVersionAndReport version thyOpts (preReport ++ postReport) transThy

  return (preReport ++ postReport, finalThy)
  where
    withTheory f = bitraverse f return

-- | Pretty print an open theory based on the specified output module.
prettyOpenTheoryByModule :: TheoryLoadOptions -> OpenTheory -> IO Pretty.Doc
prettyOpenTheoryByModule thyOpts = case modType of
  ModuleSpthy               -> return . prettyOpenTheory
  ModuleSpthyTyped          -> return . prettyOpenTheory
  ModuleMsr                 -> return . prettyOpenTranslatedTheory . removeTranslationItems
  ModuleProVerifEquivalence -> Export.prettyProVerifEquivTheory   <=< Sapic.typeTheoryEnv
  ModuleProVerif            -> Export.prettyProVerifTheory lemmas <=< Sapic.typeTheoryEnv
  ModuleDeepSec             -> Export.prettyDeepSecTheory
  where
    modType = L.get oOutputModule thyOpts
    lemmas = lemmaSelector thyOpts


    loadedAutoSources = L.get oAutoSources loadedThyOptions
    loadedStopOnTrace = L.get oStopOnTrace loadedThyOptions
    loadedHeuristic   = L.get oHeuristic loadedThyOptions

    srcThyInFileName = either (L.get thyInFile) (L.get diffThyInFile) srcThy

    -- Update command line arguments with arguments taken from the configuration block.
    -- Set the default oraclename if needed.
    thyOpts = (thyHeurDefOracle . configStopOnTrace . configAutoSources) loadedThyOptions

    -- Set the oraclename to theory_filename.oracle (if none was supplied).
    thyHeurDefOracle =
      set oHeuristic $ (\(Heuristic grl) -> Just $ Heuristic $ defaultOracleNames srcThyInFileName grl) =<< loadedHeuristic

    -- Read and process the arguments from the theory's config block.
    srcThyConfigBlockArgs = argsConfigString $ either theoryConfigBlock diffTheoryConfigBlock srcThy

    argsConfigString =
      processValue (mode "configuration block arguments" [] "" (flagArg (updateArg "") "") theoryConfFlags) <$> splitArgs

    theoryConfFlags =
      [flagOpt "dfs" ["stop-on-trace"] (updateArg "stop-on-trace") "" ""
     , flagNone ["auto-sources"] (addEmptyArg "auto-sources") ""]

    configStopOnTrace =
      if isNothing loadedStopOnTrace
        then L.set oStopOnTrace (either (\(ArgumentError e) -> error e) id $ stopOnTrace srcThyConfigBlockArgs)
        else id

    configAutoSources = L.set oAutoSources (argExists "auto-sources" srcThyConfigBlockArgs || loadedAutoSources)

(&&&) :: (t -> Bool) -> (t -> Bool) -> t -> Bool
(&&&) f g x = f x && g x

-- | Construct an 'AutoProver' from the given arguments (--bound,
-- --stop-on-trace).
constructAutoProver :: TheoryLoadOptions -> AutoProver
constructAutoProver thyOpts =
    AutoProver (L.get oHeuristic thyOpts)
               Nothing
               (L.get oProofBound thyOpts)
               (fromMaybe CutDFS $ L.get oStopOnTrace thyOpts)

-----------------------------------------------
-- Add Options parameters in an OpenTheory
-----------------------------------------------

-- | Add parameters in the OpenTheory, here openchain and saturation in the options
addParamsOptions :: TheoryLoadOptions -> Either OpenTheory OpenDiffTheory -> Either OpenTheory OpenDiffTheory
addParamsOptions opt = addVerboseOptions . addSatArg . addChainsArg . addLemmaToProve

    where
      -- Add Open Chain Limit parameters in the Options
      chain = L.get oOpenChain opt
      addChainsArg (Left thy) = Left $ set (openChainsLimit.thyOptions) chain thy
      addChainsArg (Right diffThy) = Right $ set (openChainsLimit.diffThyOptions) chain diffThy
      -- Add Saturation Limit parameters in the Options
      sat = L.get oSaturation opt
      addSatArg (Left thy) = Left $ set (saturationLimit.thyOptions) sat thy
      addSatArg (Right diffThy) = Right $ set (saturationLimit.diffThyOptions) sat diffThy
      -- Add lemmas to Prove in the Options
      lem = L.get oLemmaNames opt
      addLemmaToProve (Left thy) = Left $ set (lemmasToProve.thyOptions) lem thy
      addLemmaToProve (Right diffThy) = Right $ set (lemmasToProve.diffThyOptions) lem diffThy
      -- Add Verbose parameter in the Options
      verb = L.get oVerboseMode opt
      addVerboseOptions (Left thy) = Left $ set (verboseOption.thyOptions) verb thy
      addVerboseOptions (Right diffThy) = Right $ set (verboseOption.diffThyOptions) verb diffThy


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
addMessageDeductionRuleVariants :: OpenTranslatedTheory -> OpenTranslatedTheory
addMessageDeductionRuleVariants thy0
  | enableBP msig = addIntruderVariants [ mkDhIntruderVariants
                                        , mkBpIntruderVariants ]
  | enableDH msig = addIntruderVariants [ mkDhIntruderVariants ]
  | otherwise     = thy
  where
    msig         = get (sigpMaudeSig . thySignature) thy0
    rules        = subtermIntruderRules False msig ++ specialIntruderRules False
                   ++ (if enableMSet msig then multisetIntruderRules else [])
                   ++ (if enableXor msig then xorIntruderRules else [])
    thy          = addIntrRuleACsAfterTranslate rules thy0
    addIntruderVariants mkRuless = addIntrRuleACsAfterTranslate (concatMap ($ msig) mkRuless) thy

-- | Add the variants of the message deduction rule. Uses the cached version
-- of the @"intruder_variants_dh.spthy"@ file for the variants of the message
-- deduction rules for Diffie-Hellman exponentiation.
addMessageDeductionRuleVariantsDiff :: OpenDiffTheory -> OpenDiffTheory
addMessageDeductionRuleVariantsDiff thy0
  | enableBP msig = addIntruderVariantsDiff [ mkDhIntruderVariants
                                            , mkBpIntruderVariants ]
  | enableDH msig = addIntruderVariantsDiff [ mkDhIntruderVariants ]
  | otherwise     = addIntrRuleLabels thy
  where
    msig         = get (sigpMaudeSig . diffThySignature) thy0
    rules diff'  = subtermIntruderRules diff' msig ++ specialIntruderRules diff'
                    ++ (if enableMSet msig then multisetIntruderRules else [])
                    ++ (if enableXor msig then xorIntruderRules else [])
    thy          = addIntrRuleACsDiffBoth (rules False) $ addIntrRuleACsDiffBothDiff (rules True) thy0
    addIntruderVariantsDiff mkRuless =
        addIntrRuleLabels (addIntrRuleACsDiffBothDiff (concatMap ($ msig) mkRuless) $ addIntrRuleACsDiffBoth (concatMap ($ msig) mkRuless) thy)


