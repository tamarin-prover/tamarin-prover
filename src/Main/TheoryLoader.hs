-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Theory loading infrastructure.
module Main.TheoryLoader
  ( -- * Static theory loading settings
    theoryLoadFlags,
    lemmaSelector,
    TheoryLoadOptions (..),
    defaultTheoryLoadOptions,
    ArgumentError (..),
    mkTheoryLoadOptions,
    TheoryLoadError (..),
    loadTheory,
    translateAndCheckTheory,
    prettyOpenTheoryByModule,
    closeTheory,

    -- ** Constructing automatic prover
    constructAutoProver,

    -- ** Cached Message Deduction Rule Variants
    dhIntruderVariantsFile,
    bpIntruderVariantsFile,
    addMessageDeductionRuleVariants,
  )
where

import Accountability qualified as Acc
import Accountability.Generation qualified as Acc
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad
import Control.Monad.Catch (MonadCatch)
import Control.Monad.Except
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Bifunctor (Bifunctor (bimap), first)
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Char (toLower)
import Data.FileEmbed (embedFile)
import Data.List (find, intercalate, isPrefixOf)
import Data.Map (keys)
import Data.Maybe (fromMaybe, isNothing)
import Data.Set qualified
import Debug.Trace
import Export qualified
import Items.LemmaItem (HasLemmaAttributes, HasLemmaName)
import Items.OptionItem (Option (..))
import Main.Console
import Safe
import Sapic qualified
import System.Console.CmdArgs.Explicit
import System.Timeout (timeout)
import Text.Parsec (ParseError)
import Text.Read (readEither)
import Theory hiding (closeTheory, transReport)
import Theory.Module
import Theory.Text.Parser (diffTheory, parseIntruderRules, theory)
import Theory.Text.Parser.Token
import Theory.Text.Pretty qualified as Pretty
import Theory.Tools.AbstractInterpretation (EvaluationStyle (..))
import Theory.Tools.IntruderRules
  ( multisetIntruderRules,
    natIntruderRules,
    specialIntruderRules,
    subtermIntruderRules,
    xorIntruderRules,
  )
import Theory.Tools.MessageDerivationChecks
import Theory.Tools.Wellformedness
import TheoryObject (diffTheoryConfigBlock, theoryConfigBlock)

------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------

-----------------------------------------------
-- Flags
-----------------------------------------------

-- | Flags for loading a theory.
theoryLoadFlags :: [Flag Arguments]
theoryLoadFlags =
  [ flagOpt
      ""
      ["prove"]
      (updateArg "prove")
      "LEMMAPREFIX*|LEMMANAME"
      "Attempt to prove all lemmas that start with LEMMAPREFIX or the lemma which name is LEMMANAME (can be repeated).",
    flagOpt
      ""
      ["lemma"]
      (updateArg "lemma")
      "LEMMAPREFIX*|LEMMANAME"
      "Select lemma(s) by name or prefx (can be repeated)",
    flagOpt
      "dfs"
      ["stop-on-trace"]
      (updateArg "stop-on-trace")
      "DFS|BFS|SEQDFS|NONE"
      "How to search for traces (default DFS)",
    flagOpt
      "5"
      ["bound", "b"]
      (updateArg "bound")
      "INT"
      "Bound the depth of the proofs",
    flagOpt
      (prettyGoalRanking $ head $ defaultRankings False)
      ["heuristic"]
      (updateArg "heuristic")
      ("(" ++ intercalate "|" (keys goalRankingIdentifiers) ++ ")+")
      ("Sequence of proof method rankings to use (default '" ++ prettyGoalRanking (head $ defaultRankings False) ++ "')"),
    flagOpt
      "summary"
      ["partial-evaluation"]
      (updateArg "partial-evaluation")
      "SUMMARY|VERBOSE"
      "Partially evaluate multiset rewriting system",
    flagOpt
      ""
      ["defines", "D"]
      (updateArg "defines")
      "STRING"
      "Define flags for pseudo-preprocessor.",
    flagNone
      ["diff"]
      (addEmptyArg "diff")
      "Turn on observational equivalence mode using diff terms.",
    flagNone
      ["quit-on-warning"]
      (addEmptyArg "quit-on-warning")
      "Strict mode that quits on any warning that is emitted.",
    flagNone
      ["auto-sources"]
      (addEmptyArg "auto-sources")
      "Try to auto-generate sources lemmas",
    flagOpt
      ""
      ["oraclename"]
      (updateArg "oraclename")
      "FILE"
      ("Path to the oracle heuristic (default '" ++ "./theory_filename.oracle" ++ "', fallback '" ++ "./oracle" ++ "')"),
    flagNone
      ["quiet"]
      (addEmptyArg "quiet")
      "Do not display computation steps of oracle or tactic.",
    flagNone
      ["verbose", "v"]
      (addEmptyArg "verbose")
      "Display full information when calculating proof.",
    flagOpt
      "10"
      ["open-chains", "c"]
      (updateArg "OpenChainsLimit")
      "PositiveInteger"
      "Limits the number of open chains to be resoled during precomputations (default 10)",
    flagOpt
      "5"
      ["saturation", "s"]
      (updateArg "SaturationLimit")
      "PositiveInteger"
      "Limits the number of saturations during precomputations (default 5)",
    flagOpt
      "5"
      ["derivcheck-timeout", "d"]
      (updateArg "derivcheck-timeout")
      "INT"
      "Set timeout for message derivation checks in sec (default 5). 0 deactivates check.",
      --  , flagOpt "" ["diff"] (updateArg "diff") "OFF|ON"
      --      "Turn on observational equivalence (default OFF).",
    flagNone
      ["no-reuse"]
      (addEmptyArg "no-reuse")
      "Do not export reuse or source lemmas",
    flagNone
      ["no-restrictions"]
      (addEmptyArg "no-restrictions")
      "Do not export restrictions",
    flagOpt
      "3"
      ["replication-bound"]
      (updateArg "replication-bound")
      "INT"
      "Replication bound for DeepSec export"
  ]

-----------------------------------------------
-- TheoryLoadOptions
-----------------------------------------------

data TheoryLoadOptions = TheoryLoadOptions
  { proveMode :: Bool,
    lemmaNames :: [String],
    stopOnTrace :: Maybe SolutionExtractor,
    proofBound :: Maybe Int,
    heuristic :: Maybe (Heuristic ProofContext),
    partialEvaluation :: Maybe EvaluationStyle,
    defines :: [String],
    diffMode :: Bool,
    quitOnWarning :: Bool,
    autoSources :: Bool,
    verboseMode :: Bool,
    outputModule :: Maybe ModuleType, -- Note: This flag is only used for batch mode.
    maudePath :: FilePath, -- FIXME: Other functions defined in Environment.hs
    parseOnlyMode :: Bool,
    precomputeOnlyMode :: Bool,
    openChain :: Integer,
    saturation :: Integer,
    derivationChecks :: Int,
    noReuse :: Bool,
    noRestrictions :: Bool,
    replicationBound :: Int
  }
  deriving (Show)

defaultTheoryLoadOptions :: TheoryLoadOptions
defaultTheoryLoadOptions =
  TheoryLoadOptions
    { proveMode = False,
      lemmaNames = [],
      stopOnTrace = Nothing,
      proofBound = Nothing,
      heuristic = Nothing,
      partialEvaluation = Nothing,
      defines = [],
      diffMode = False,
      quitOnWarning = False,
      autoSources = False,
      verboseMode = False,
      outputModule = Nothing,
      maudePath = "maude",
      parseOnlyMode = False,
      precomputeOnlyMode = False,
      openChain = 10,
      saturation = 5,
      derivationChecks = 5,
      noReuse = False,
      noRestrictions = False,
      replicationBound = 3
    }

toParserFlags :: TheoryLoadOptions -> [String]
toParserFlags thyOpts =
  concat
    [ ["diff" | thyOpts.diffMode]
    , thyOpts.defines
    , ["quit-on-warning" | thyOpts.quitOnWarning]
    ]

newtype ArgumentError = ArgumentError String

mkTheoryLoadOptions :: (MonadError ArgumentError m) => Arguments -> m TheoryLoadOptions
mkTheoryLoadOptions as =
  TheoryLoadOptions
    <$> proveMode
    <*> lemmaNames
    <*> stopOnTrace as
    <*> proofBound
    <*> heuristic
    <*> partialEvaluation
    <*> defines
    <*> diffMode
    <*> quitOnWarning
    <*> autoSources
    <*> verboseMode
    <*> outputModule
    <*> pure (maudePath as)
    <*> parseOnlyMode
    <*> precomputeOnlyMode
    <*> openchain
    <*> saturation
    <*> deriv
    <*> noReuse
    <*> noRestrictions
    <*> replicationBound
  where
    proveMode = pure $ argExists "prove" as
    lemmaNames = pure $ findArg "prove" as ++ findArg "lemma" as

    parseIntArg args defaultValue conv errMsg = case args of
      [] -> pure defaultValue
      (x : _) -> case (readEither x :: Either String Int) of
        Left _ -> throwError $ ArgumentError errMsg
        Right i -> pure $ conv i
    -- FIXME : provide option to handle potential error without crash (ie, take default value and raise error but continue)

    proofBound = parseIntArg (findArg "bound" as) Nothing Just "bound: invalid bound given"

    heuristic = case findArg "heuristic" as of
      Just rawRankings@(_ : _) ->
        pure $
          Just $
            roundRobinHeuristic $
              map
                (mapOracleRanking (maybeSetOracleRelPath oraclename))
                (filterHeuristic (argExists "diff" as) rawRankings)
      Just [] -> throwError $ ArgumentError "heuristic: at least one ranking must be given"
      _ -> pure Nothing
    oraclename = case findArg "oraclename" as of
      Just "" -> Nothing
      name -> name
    -- toGoalRanking | argExists "diff" as = stringToGoalRankingDiff
    --              | otherwise           = stringToGoalRanking

    partialEvaluation = case map toLower <$> findArg "partial-evaluation" as of
      Just "summary" -> pure $ Just Summary
      Just "verbose" -> pure $ Just Tracing
      Just _ -> throwError $ ArgumentError "partial-evaluation: unknown option"
      Nothing -> pure Nothing

    defines = pure $ findArg "defines" as
    diffMode = pure $ argExists "diff" as
    verboseMode = pure $ argExists "verbose" as
    quitOnWarning = pure $ argExists "quit-on-warning" as
    autoSources = pure $ argExists "auto-sources" as
    noReuse = pure $ argExists "no-reuse" as
    noRestrictions = pure $ argExists "no-restrictions" as

    outputModule = case findArg "outModule" as of
      Just str -> case find ((str ==) . show) [minBound ..] of
        Just m -> pure $ Just m
        _ -> throwError $ ArgumentError "output mode not supported."
      Nothing -> pure defaultTheoryLoadOptions.outputModule

    parseOnlyMode = pure $ argExists "parseOnly" as

    precomputeOnlyMode = pure $ argExists "precomputeOnly" as

    chain = findArg "OpenChainsLimit" as
    chainDefault = defaultTheoryLoadOptions.openChain
    openchain = parseIntArg chain chainDefault toInteger "OpenChainsLimit: invalid bound given"

    sat = findArg "SaturationLimit" as
    satDefault = defaultTheoryLoadOptions.saturation
    saturation = parseIntArg sat satDefault toInteger "SaturationLimit: invalid bound given"

    derivchecks = findArg "derivcheck-timeout" as
    derivDefault = defaultTheoryLoadOptions.derivationChecks
    deriv = parseIntArg derivchecks derivDefault id "derivcheck-timeout: invalid bound given"

    replicationBound = parseIntArg (findArg "replication-bound" as) defaultTheoryLoadOptions.replicationBound id "replication-bound: invalid bound given"

stopOnTrace :: (MonadError ArgumentError m) => Arguments -> m (Maybe SolutionExtractor)
stopOnTrace as = case map toLower <$> findArg "stop-on-trace" as of
  Just "dfs" -> pure $ Just CutDFS
  Just "none" -> pure $ Just CutNothing
  Just "bfs" -> pure $ Just CutBFS
  Just "seqdfs" -> pure $ Just CutSingleThreadDFS
  Just unknown -> throwError $ ArgumentError ("unknown stop-on-trace method: " ++ unknown)
  Nothing -> pure Nothing

lemmaSelectorByModule :: (HasLemmaAttributes l) => TheoryLoadOptions -> l -> Bool
lemmaSelectorByModule thyOpt lem = case lemmaModules of
  [] -> True -- default to true if no modules (or only empty ones) are set
  _ -> maybe True (`elem` lemmaModules) thyOpt.outputModule
  where
    lemmaModules = concat [m | LemmaModule m <- lem.lAttributes]

-- | quiet flag in the argument
-- quiet :: Arguments -> [String]
-- quiet as = if (argExists "quiet" as) then ["quiet"] else []

-- | Select lemmas for proving
lemmaSelector :: (HasLemmaName l) => TheoryLoadOptions -> l -> Bool
lemmaSelector thyOpts lem
  | null lemmaNames = True
  | lemmaNames == [""] = True
  | lemmaNames == ["", ""] = True
  | otherwise = any lemmaMatches lemmaNames
  where
    lemmaNames :: [String]
    lemmaNames = thyOpts.lemmaNames

    lemmaMatches :: String -> Bool
    lemmaMatches pattern
      | lastMay pattern == Just '*' = init pattern `isPrefixOf` lem.lName
      | otherwise = lem.lName == pattern

data TheoryLoadError
  = ParserError ParseError
  | WarningError WfErrorReport

instance Show TheoryLoadError where
  show (ParserError e) = show e
  show (WarningError e) = Pretty.render (prettyWfErrorReport e)

-- | Load an open theory from a string with the given options.
loadTheory ::
  (Monad m) =>
  TheoryLoadOptions ->
  String ->
  FilePath ->
  ExceptT TheoryLoadError m (Either OpenTheory OpenDiffTheory)
loadTheory thyOpts input inFile = do
  thy <- withExceptT ParserError $ liftEither $ unwrapError $ bimap parse parse thyParser
  traceM ("[Theory " ++ theoryName thy ++ "] Theory loaded")
  pure $ addParamsOptions thyOpts thy
  where
    thyParser
      | isDiffMode = Right $ diffTheory $ Just inFile
      | otherwise = Left $ theory $ Just inFile

    parse p = parseString (toParserFlags thyOpts) inFile p input

    isDiffMode = thyOpts.diffMode

    unwrapError (Left (Left e)) = Left e
    unwrapError (Left (Right v)) = Right $ Left v
    unwrapError (Right (Left e)) = Left e
    unwrapError (Right (Right v)) = Right $ Right v
    theoryName = either (._thyName) (._diffThyName)

-- | Preprocess an open theory based on the specified output module so that
-- well-formedness can be checked (but do not translate yet)
processOpenTheory :: (MonadCatch m) => TheoryLoadOptions -> OpenTheory -> m OpenTheory
processOpenTheory thyOpts = case thyOpts.outputModule of
  Nothing -> Sapic.typeTheory >=> Sapic.translate >=> Acc.translate
  Just ModuleSpthy -> pure
  Just ModuleSpthyTyped -> Sapic.typeTheory
  -- If the output module is set to MSR, we only keep the specified lemmas in the theory.
  Just ModuleMsr ->
    Sapic.typeTheory
      >=> Sapic.translate
      >=> Acc.translate
      >=> (pure . filterLemma lemmas)
  Just ModuleProVerifEquivalence -> Sapic.typeTheory -- Type theory here to catch errors.
  Just ModuleProVerif -> Sapic.typeTheory -- Type theory here to catch errors.
  Just ModuleDeepSec -> Sapic.typeTheory
  where
    lemmas = lemmaSelector thyOpts

-- | Translate an open theory: `translateTheory opts thy` with options `opts`
-- and Open(Diff)Theory `thy` translates it according to the output module and
-- performs a well-formedness check.
translateTheory ::
  (MonadCatch m, MonadError TheoryLoadError m) =>
  TheoryLoadOptions ->
  Either OpenTheory OpenDiffTheory ->
  m (WfErrorReport, Either OpenTheory OpenDiffTheory)
translateTheory thyOpts thy = do
  traceM ("[Theory " ++ theoryName thy ++ "] Theory translated")
  let report = either (\t -> Sapic.checkWellformedness t ++ Acc.checkWellformedness t) (const []) thy
  transThy <- withTheory (processOpenTheory thyOpts) thy
  pure (report, transThy)
  where
    withTheory f = bitraverse f pure
    theoryName = either (._thyName) (._diffThyName)

-- | Perform wellformedness and deducability checks on a theory.
checkTranslatedTheory ::
  (MonadIO m, MonadError TheoryLoadError m) =>
  TheoryLoadOptions ->
  SignatureWithMaude ->
  Either OpenTranslatedTheory OpenDiffTheory ->
  m (WfErrorReport, Either OpenTranslatedTheory OpenDiffTheory)
checkTranslatedTheory thyOpts sign thy = do
  let transReport =
        either
          (\thy -> checkWellformedness incompleteMSRs thy sign)
          (`checkWellformednessDiff` sign)
          thy

  let deducThy =
        bimap
          addMessageDeductionRuleVariants
          addMessageDeductionRuleVariantsDiff
          thy

  variableReport <- case compare derivChecks 0 of
    EQ -> pure $ Just []
    _ -> do
      traceM ("[Theory " ++ theoryName thy ++ "] Derivation checks started")
      derivCheckSignature <-
        liftIO $
          toSignatureWithMaude thyOpts.maudePath $
            maudePublicSig (toSignaturePure sign)
      rep <-
        liftIO $
          timeout (1000000 * derivChecks) $
            evaluate . force $
              either
                (\t -> checkVariableDeducability t derivCheckSignature autoSources defaultProver)
                (\t -> diffCheckVariableDeducability t derivCheckSignature autoSources defaultProver defaultDiffProver)
                deducThy
      traceM ("[Theory " ++ theoryName thy ++ "] Derivation checks ended")
      pure rep

  let report = transReport ++ fromMaybe derivTimeoutMsg variableReport

  pure (report, deducThy)
  where
    incompleteMSRs = False -- TODO how do we know if we do not have all MSRs due to translation?
    autoSources = thyOpts.autoSources
    derivChecks = thyOpts.derivationChecks
    derivTimeoutMsg =
      [ ( underlineTopic "Derivation Checks",
          Pretty.vcat
            [ Pretty.text "Derivation checks timed out.",
              Pretty.text "Use --derivcheck-timeout=INT to configure timeout.",
              Pretty.text "Set to 0 to deactivate for no timeout."
            ]
        )
      ]

    defaultProver = replaceSorryProver $ runAutoProver $ constructAutoProver defaultTheoryLoadOptions
    defaultDiffProver = replaceDiffSorryProver $ runAutoDiffProver $ constructAutoProver defaultTheoryLoadOptions
    maudePublicSig s =
      Signature $
        s._sigMaudeInfo
          { stFunSyms = makepublic (stFunSyms s._sigMaudeInfo)
          , funSyms = makepublicsym (funSyms s._sigMaudeInfo)
          , irreducibleFunSyms = makepublicsym (irreducibleFunSyms s._sigMaudeInfo)
          , reducibleFunSyms = makepublicsym (reducibleFunSyms s._sigMaudeInfo)
          }
    makepublic = Data.Set.map (\(name, (int, _, construct)) -> (name, (int, Public, construct)))
    makepublicsym = Data.Set.map $ \case
      NoEq (name, (int, _, constr)) -> NoEq (name, (int, Public, constr))
      x -> x

    theoryName = either (._thyName) (._diffThyName)

-- | Add report and version information to a theory.
withVersionAndReport ::
  (MonadError TheoryLoadError m) =>
  String ->
  TheoryLoadOptions ->
  WfErrorReport ->
  Either (Theory sig1 c1 r1 p1 s) (DiffTheory sig2 c2 r2 r3 p2 p3) ->
  m (Either (Theory sig1 c1 r1 p1 s) (DiffTheory sig2 c2 r2 r3 p2 p3))
withVersionAndReport version thyOpts report thy = do
  let reportThy =
        bimap
          (addComment (reportToDoc report))
          (addDiffComment (reportToDoc report))
          thy

  let versionThy =
        bimap
          (addComment (Pretty.text version))
          (addDiffComment (Pretty.text version))
          reportThy

  when (thyOpts.quitOnWarning && not (null report)) (throwError $ WarningError report)

  pure versionThy
  where
    reportToDoc rep
      | null rep = Pretty.text "All wellformedness checks were successful."
      | otherwise =
          Pretty.vsep
            [ Pretty.text "WARNING: the following wellformedness checks failed!",
              prettyWfErrorReport rep
            ]

-- | Close a translated theory.
closeTranslatedTheory
  :: (MonadError TheoryLoadError m)
  => TheoryLoadOptions
  -> SignatureWithMaude
  -> Either OpenTranslatedTheory OpenDiffTheory
  -> m (Either ClosedTheory ClosedDiffTheory)
closeTranslatedTheory thyOpts sign srcThy = do
  diffLemThy <- withDiffTheory (pure . addDefaultDiffLemma) srcThy
  let closedThy =
        bimap
          (\t -> closeTheoryWithMaude sign t autoSources True)
          (\t -> closeDiffTheoryWithMaude sign t autoSources)
          diffLemThy
      partialThy =
        case thyOpts.partialEvaluation of
          Just style ->
            bimap
              (applyPartialEvaluation style autoSources)
              (applyPartialEvaluationDiff style autoSources)
              closedThy
          Nothing -> closedThy
      provedThy =
        bimap
          (proveTheory selector prover)
          (proveDiffTheory selector prover diffProver)
          partialThy

  traceM ("[Theory " ++ theoryName srcThy ++ "] Theory closed")

  pure provedThy
  where
    autoSources = thyOpts.autoSources

    selector :: (HasLemmaName l, HasLemmaAttributes l) => l -> Bool
    selector l = lemmaSelectorByModule thyOpts l && lemmaSelector thyOpts l

    prover
      | thyOpts.proveMode = replaceSorryProver $ runAutoProver $ constructAutoProver thyOpts
      | otherwise = mempty

    diffProver
      | thyOpts.proveMode = replaceDiffSorryProver $ runAutoDiffProver $ constructAutoProver thyOpts
      | otherwise = mempty

    withDiffTheory = bitraverse pure

    theoryName = either (._thyName) (._diffThyName)

-- | Translate an open theory, perform checks on the translated theory and finally close it.
closeTheory ::
  (MonadCatch m, MonadIO m, MonadError TheoryLoadError m) =>
  String ->
  TheoryLoadOptions ->
  SignatureWithMaude ->
  Either OpenTheory OpenDiffTheory ->
  m (WfErrorReport, Either ClosedTheory ClosedDiffTheory)
closeTheory version loadedThyOpts sign srcThy = do
  (preReport, transThy) <- translateTheory thyOpts srcThy
  let removedThy = first removeTranslationItems transThy
  (postReport, checkedThy) <- checkTranslatedTheory thyOpts sign removedThy
  closedThy <- closeTranslatedTheory thyOpts sign checkedThy
  finalThy <- withVersionAndReport version thyOpts (preReport ++ postReport) closedThy

  pure (preReport ++ postReport, finalThy)
  where
    loadedAutoSources = loadedThyOpts.autoSources
    loadedStopOnTrace = loadedThyOpts.stopOnTrace
    loadedHeuristic = loadedThyOpts.heuristic

    srcThyInFileName = either (._thyInFile) (._diffThyInFile) srcThy

    -- Update command line arguments with arguments taken from the configuration block.
    -- Set the default oraclename if needed.
    thyOpts = (thyHeurDefOracle . configStopOnTrace . configAutoSources) loadedThyOpts

    -- Set the oraclename to theory_filename.oracle (if none was supplied).
    thyHeurDefOracle opts =
      opts { heuristic = (\(Heuristic grl) -> Heuristic $ defaultOracleNames srcThyInFileName grl) <$> loadedHeuristic }

    -- Read and process the arguments from the theory's config block.
    srcThyConfigBlockArgs = argsConfigString $ either theoryConfigBlock diffTheoryConfigBlock srcThy

    argsConfigString =
      processValue (mode "configuration block arguments" [] "" (flagArg (updateArg "") "") theoryConfFlags) <$> splitArgs

    theoryConfFlags =
      [ flagOpt "dfs" ["stop-on-trace"] (updateArg "stop-on-trace") "" "",
        flagNone ["auto-sources"] (addEmptyArg "auto-sources") ""
      ]

    configStopOnTrace opts =
      if isNothing loadedStopOnTrace
        then opts {stopOnTrace = either (\(ArgumentError e) -> error e) id $ stopOnTrace srcThyConfigBlockArgs}
        else opts

    configAutoSources opts =
      opts {autoSources = argExists "auto-sources" srcThyConfigBlockArgs || loadedAutoSources}

-- | Translate an open theory and perform checks on the translated theory.
translateAndCheckTheory ::
  (MonadCatch m, MonadIO m, MonadError TheoryLoadError m) =>
  String ->
  TheoryLoadOptions ->
  SignatureWithMaude ->
  Either OpenTheory OpenDiffTheory ->
  m (WfErrorReport, Either OpenTheory OpenDiffTheory)
translateAndCheckTheory version thyOpts sign srcThy = do
  (preReport, transThy) <- translateTheory thyOpts srcThy
  let removedThy = first removeTranslationItems transThy
  (postReport, _) <- checkTranslatedTheory thyOpts sign removedThy
  finalThy <- withVersionAndReport version thyOpts (preReport ++ postReport) transThy
  pure (preReport ++ postReport, finalThy)

-- | Pretty print an open theory based on the specified output module.
prettyOpenTheoryByModule :: TheoryLoadOptions -> OpenTheory -> IO Pretty.Doc
prettyOpenTheoryByModule thyOpts = case  thyOpts.outputModule of
  Nothing {- Same as ModuleMsr -} -> pure . prettyOpenTranslatedTheory . removeTranslationItems
  Just ModuleSpthy -> pure . prettyOpenTheory
  Just ModuleSpthyTyped -> pure . prettyOpenTheory
  Just ModuleMsr -> pure . prettyOpenTranslatedTheory . removeTranslationItems
  Just ModuleProVerifEquivalence -> Export.prettyProVerifEquivTheory <=< Sapic.typeTheoryEnv
  Just ModuleProVerif -> Export.prettyProVerifTheory ModuleProVerif noReuse noRestrictions lemmas <=< Sapic.typeTheoryEnv
  Just ModuleDeepSec -> Export.prettyDeepSecTheory replicationBound
  where
    lemmas = lemmaSelector thyOpts
    noReuse = thyOpts.noReuse
    noRestrictions = thyOpts.noRestrictions
    replicationBound = thyOpts.replicationBound

-- | Construct an 'AutoProver' from the given arguments (--bound, --stop-on-trace).
constructAutoProver :: TheoryLoadOptions -> AutoProver
constructAutoProver thyOpts =
  AutoProver
    thyOpts.heuristic
    Nothing
    thyOpts.proofBound
    (fromMaybe CutDFS thyOpts.stopOnTrace)
    False

-----------------------------------------------
-- Add Options parameters in an OpenTheory
-----------------------------------------------

-- | Add parameters in the OpenTheory, here openchain and saturation in the options
addParamsOptions ::
  TheoryLoadOptions ->
  Either OpenTheory OpenDiffTheory ->
  Either OpenTheory OpenDiffTheory
addParamsOptions opt = addVerboseOptions . addPrecomputationOnlyOptions . addSatArg . addChainsArg . addLemmaToProve
  where
    -- Add Open Chain Limit parameters in the Options
    _openChainsLimit = opt.openChain
    addChainsArg (Left thy) = Left thy {_thyOptions = thy._thyOptions {_openChainsLimit}}
    addChainsArg (Right diffThy) = Right diffThy {_diffThyOptions = diffThy._diffThyOptions {_openChainsLimit}}
    -- Add Saturation Limit parameters in the Options
    _saturationLimit = opt.saturation
    addSatArg (Left thy) = Left thy {_thyOptions = thy._thyOptions {_saturationLimit}}
    addSatArg (Right diffThy) = Right diffThy {_diffThyOptions = diffThy._diffThyOptions {_saturationLimit}}
    -- Add lemmas to Prove in the Options
    _lemmasToProve = opt.lemmaNames
    addLemmaToProve (Left thy) = Left thy {_thyOptions = thy._thyOptions {_lemmasToProve}}
    addLemmaToProve (Right diffThy) = Right diffThy {_diffThyOptions = diffThy._diffThyOptions {_lemmasToProve}}
    -- Add Verbose parameter in the Options
    _verboseOption = opt.verboseMode
    addVerboseOptions (Left thy) = Left thy {_thyOptions = thy._thyOptions {_verboseOption}}
    addVerboseOptions (Right diffThy) = Right diffThy {_diffThyOptions = diffThy._diffThyOptions {_verboseOption}}
    -- Add PrecomputationOnly parameter in the Options
    _precomputationOnlyOption = opt.precomputeOnlyMode
    addPrecomputationOnlyOptions (Left thy) = Left thy {_thyOptions = thy._thyOptions {_precomputationOnlyOption}}
    addPrecomputationOnlyOptions (Right diffThy) = Right diffThy {_diffThyOptions = diffThy._diffThyOptions {_precomputationOnlyOption}}

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
  either (error . show) id $ -- report errors lazily through 'error'
    parseIntruderRules
      msig
      dhIntruderVariantsFile
      $(embedFile "data/intruder_variants_dh.spthy")

-- | Construct the BP intruder variants for the given maude signature.
mkBpIntruderVariants :: MaudeSig -> [IntrRuleAC]
mkBpIntruderVariants msig =
  either (error . show) id $ -- report errors lazily through 'error'
    parseIntruderRules
      msig
      bpIntruderVariantsFile
      $(embedFile "data/intruder_variants_bp.spthy")

-- | Add the variants of the message deduction rule. Uses built-in cached
-- files for the variants of the message deduction rules for Diffie-Hellman
-- exponentiation and Bilinear-Pairing.
addMessageDeductionRuleVariants :: OpenTranslatedTheory -> OpenTranslatedTheory
addMessageDeductionRuleVariants thy0
  | enableBP msig =
      addIntruderVariants
        [ mkDhIntruderVariants,
          mkBpIntruderVariants
        ]
  | enableDH msig = addIntruderVariants [mkDhIntruderVariants]
  | otherwise = thy
  where
    msig = thy0._thySignature._sigMaudeInfo
    rules =
      subtermIntruderRules False msig
        ++ specialIntruderRules False
        ++ (if enableNat msig then natIntruderRules else [])
        ++ (if enableMSet msig then multisetIntruderRules else [])
        ++ (if enableXor msig then xorIntruderRules else [])
    thy = addIntrRuleACsAfterTranslate rules thy0
    addIntruderVariants mkRuless = addIntrRuleACsAfterTranslate (concatMap ($ msig) mkRuless) thy

-- | Add the variants of the message deduction rule. Uses the cached version
-- of the @"intruder_variants_dh.spthy"@ file for the variants of the message
-- deduction rules for Diffie-Hellman exponentiation.
addMessageDeductionRuleVariantsDiff :: OpenDiffTheory -> OpenDiffTheory
addMessageDeductionRuleVariantsDiff thy0
  | enableBP msig =
      addIntruderVariantsDiff
        [ mkDhIntruderVariants,
          mkBpIntruderVariants
        ]
  | enableDH msig = addIntruderVariantsDiff [mkDhIntruderVariants]
  | otherwise = addIntrRuleLabels thy
  where
    msig = thy0._diffThySignature._sigMaudeInfo
    rules diff' =
      subtermIntruderRules diff' msig
        ++ specialIntruderRules diff'
        ++ (if enableNat msig then natIntruderRules else [])
        ++ (if enableMSet msig then multisetIntruderRules else [])
        ++ (if enableXor msig then xorIntruderRules else [])
    thy = addIntrRuleACsDiffBoth (rules False) $ addIntrRuleACsDiffBothDiff (rules True) thy0
    addIntruderVariantsDiff mkRuless =
      addIntrRuleLabels $
        addIntrRuleACsDiffBothDiff
          (concatMap ($ msig) mkRuless)
          (addIntrRuleACsDiffBoth (concatMap ($ msig) mkRuless) thy)
