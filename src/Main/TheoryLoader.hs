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
    addMessageDeductionRuleVariantsWithoutMaude
  )
where

import Accountability qualified as Acc
import Accountability.Generation qualified as Acc
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad
import Control.Monad.Catch (MonadCatch)
import Control.Monad.Except
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Reader

import Data.Bifunctor (Bifunctor (bimap), first)
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Char (toLower)
import Data.FileEmbed (embedFile)
import Data.Function (on)
import Data.Map (keys)
import Data.Maybe (fromMaybe, isNothing)
import Data.Set qualified
import Debug.Trace
import Data.List (isPrefixOf, intercalate, find, groupBy, sortOn)
import Data.Map (keys)

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
    subtermConstructorRules,
    xorIntruderRules,
    destructionRulesAC,
    destructionRulesNoEq
  )
import Theory.Tools.MessageDerivationChecks
import Theory.Tools.Wellformedness
import TheoryObject (diffTheoryConfigBlock, theoryConfigBlock, theoryConfigBlock, deductionChainCheck)

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
      "DFS|BFS|SEQDFS|SORRY|NONE"
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
      ["oracle-only"]
      (addEmptyArg "oracle-only")
      "When set, the oracle heuristic will stop proof search if the oracle does not rank any proof goals.",
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
      ["proverif-no-reuse-lemmas"]
      (addEmptyArg "proverif-no-reuse-lemmas")
      "Do not export reuse lemmas as ProVerif axioms",
    flagNone
      ["proverif-no-source-lemmas"]
      (addEmptyArg "proverif-no-source-lemmas")
      "Do not export source lemmas as ProVerif axioms",
    flagNone
      ["proverif-no-restrictions"]
      (addEmptyArg "proverif-no-restrictions")
      "Do not export restrictions to ProVerif",
    flagNone
      ["proverif-no-multiset"]
      (addEmptyArg "proverif-no-multiset")
      "Do not export multiset semantics to ProVerif (DistinctFact events and restriction)",
    flagNone
      ["proverif-no-precise"]
      (addEmptyArg "proverif-no-precise")
      "Do not set preciseActions in ProVerif output",
    flagOpt
      "3"
      ["replication-bound"]
      (updateArg "replication-bound")
      "INT"
      "Replication bound for DeepSec export",
    flagNone
      ["no-ndc"]
      (addEmptyArg "no-ndc")
      "Deactivate the no deconstruction chain (NDC) check (enabled by default)"
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
    oracleOnly :: Bool,
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
    noReuseLemmas :: Bool,
    noSourceLemmas :: Bool,
    noRestrictions :: Bool,
    ndcCheck :: Bool, -- ^ Whether to run the no deconstruction chain (NDC) check (enabled by default).
    noMultiset :: Bool,
    noPrecise :: Bool,
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
      oracleOnly = False,
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
      noReuseLemmas = False,
      noSourceLemmas = False,
      noRestrictions = False,
      ndcCheck = True,
      noMultiset = False,
      noPrecise = False,
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
    <*> oracleOnly
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
    <*> noReuseLemmas
    <*> noSourceLemmas
    <*> noRestrictions
    <*> ndcCheck
    <*> noMultiset
    <*> noPrecise
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
    oracleOnly = pure $ argExists "oracle-only" as

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
    -- The NDC check is enabled by default; --no-ndc deactivates it.
    ndcCheck = pure $ not $ argExists "no-ndc" as
    noReuseLemmas = pure $ argExists "proverif-no-reuse-lemmas" as
    noSourceLemmas = pure $ argExists "proverif-no-source-lemmas" as
    noRestrictions = pure $ argExists "proverif-no-restrictions" as
    noMultiset = pure $ argExists "proverif-no-multiset" as
    noPrecise = pure $ argExists "proverif-no-precise" as

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
  Just "sorry" -> pure $ Just CutAfterSorry
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

-- | Closes the intruder deduction rules and applies the no deconstruction chain check if enabled.
checkCloseIntrRule :: SignatureWithMaude -> String -> OpenTranslatedTheory -> (SignatureWithMaude, OpenTranslatedTheory)
checkCloseIntrRule sign name thy = (sigWithMaude', thy {_thyCache = intrRulesACred, _thySignature = sig'})
  where
    hnd = sign._sigMaudeInfo
    sig = thy._thySignature

    intrRules = thy._thyCache

    -- do the no deconstruction chain check or not?
    deductionChainCheckBool = thy._thyOptions._deductionChainCheck
    ocLimit = thy._thyOptions._openChainsLimit
    satLimit = thy._thyOptions._saturationLimit
    ndcChecks = if deductionChainCheckBool then prettyNDCcheck False ocLimit satLimit sign name intrRules else (sign, intrRules)
    (sigWithMaude', intrRulesACred) = ndcChecks
    sig' = if deductionChainCheckBool then toSignaturePure sigWithMaude' else sig

-- | Closes the intruder deduction rules and applies the no deconstruction chain check if enabled. Version for diff theories.
checkCloseIntrRuleDiff :: SignatureWithMaude -> String -> OpenDiffTheory -> (SignatureWithMaude, OpenDiffTheory)
checkCloseIntrRuleDiff sign name diffThy = if deductionChainCheckBool then (sigWithMaude'', diffCRThy) else (sign, diffThy)
  where
    -- hnd = sign._sigMaudeInfo
    -- sig = diffThy._diffThySignature

    dcl = diffThy._diffThyDiffCacheLeft
    cl  = diffThy._diffThyCacheLeft

    -- do the no deconstruction chain check or not?
    deductionChainCheckBool = diffThy._diffThyOptions._deductionChainCheck
    ocLimit = diffThy._diffThyOptions._openChainsLimit
    satLimit = diffThy._diffThyOptions._saturationLimit

    -- we need to do the NDC check for trace and equivalence mode separately:
    -- the NDC attribute governs the trace intruder rules, NDC-diff the diff intruder rules
    ndcChecksTrace = prettyNDCcheck False ocLimit satLimit sign name cl
    (sigWithMaude', clACred) = ndcChecksTrace

    -- FIXME : should we copy the trace NDC over to the diff rule caches ?
    ndcChecksDiff = prettyNDCcheck True ocLimit satLimit sigWithMaude' name dcl
    (sigWithMaude'', dclACred) = ndcChecksDiff
    sig'' = toSignaturePure sigWithMaude''

    diffDCLThy = diffThy    {_diffThyDiffCacheLeft = dclACred, _diffThySignature = sig''}  -- diffThySignature is the same for both sides, so we can just update it once
    diffDCRThy = diffDCLThy {_diffThyDiffCacheRight = dclACred}  -- diffThyDiffCacheLeft and diffThyDiffCacheRight contain the same Intruder Rules, so we use the same list of closed intruder rules for both sides

    diffCLThy = diffDCRThy {_diffThyCacheLeft = clACred}
    diffCRThy = diffCLThy  {_diffThyCacheRight = clACred}  -- diffThyCacheLeft and diffThyCacheRight contain the same Intruder Rules, so we use the same list of closed intruder rules for both sides

-- | Perform wellformedness and deducability checks on a theory.
checkTranslatedTheory ::
  (MonadIO m, MonadError TheoryLoadError m) =>
  TheoryLoadOptions ->
  SignatureWithMaude ->
  [ActionFactInfo] ->
  Either OpenTranslatedTheory OpenDiffTheory ->
  m (WfErrorReport, SignatureWithMaude, Either OpenTranslatedTheory OpenDiffTheory)
checkTranslatedTheory thyOpts sign processActions thy = do
  let transReport =
        either
          (\openThy -> checkWellformedness processActions openThy sign)
          (`checkWellformednessDiff` sign)
          thy

  deducThy0 <- bitraverse (\x -> return ((addMessageDeductionRuleVariants x) `runReader` (mh)))
                          (\x -> return ((addMessageDeductionRuleVariantsDiff x) `runReader` (mh))) thy

  deducThyAndSig <- bitraverse (liftIO . evaluate . force . (checkCloseIntrRule sign (theoryName thy))) (liftIO . evaluate . force . (checkCloseIntrRuleDiff sign (theoryName thy))) deducThy0

  let deducThy = case deducThyAndSig of
        Left (_, thy') -> Left thy'
        Right (_, diffThy') -> Right diffThy'
      signWithMaude = case deducThyAndSig of
        Left (sigWithMaude', _) -> sigWithMaude'
        Right (sigWithMaude', _) -> sigWithMaude'

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
                (\t -> checkVariableDeducibility t derivCheckSignature autoSources defaultProver)
                (\t -> diffCheckVariableDeducibility t derivCheckSignature autoSources defaultProver defaultDiffProver)
                deducThy
      traceM ("[Theory " ++ theoryName thy ++ "] Derivation checks ended")
      pure rep

  let report = transReport ++ fromMaybe derivTimeoutMsg variableReport

  pure (report, signWithMaude, deducThy)
  where
    mh = sign._sigMaudeInfo
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
          , stACFunSyms = makepublicAC (stACFunSyms s._sigMaudeInfo)
          , funSyms = makepublicsym (funSyms s._sigMaudeInfo)
          , irreducibleFunSyms = makepublicsym (irreducibleFunSyms s._sigMaudeInfo)
          , reducibleFunSyms = makepublicsym (reducibleFunSyms s._sigMaudeInfo)
          }
    makepublic = Data.Set.map (\(name, (int, _, construct, ndc)) -> (name, (int, Public, construct, ndc)))
    makepublicAC = Data.Set.map (\(name, (_, construct, ndc)) -> (name,(Public, construct, ndc)))
    makepublicsym  = Data.Set.map $ \case
      NoEq (name, (int, _, constr, ndc)) -> NoEq (name,(int, Public, constr, ndc))
      AC (ACfct (name, (_, constr, ndc))) -> AC (ACfct (name,(Public, constr, ndc)))
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
  let processActions = either processActionFactInfos (const []) transThy
      removedThy = first removeTranslationItems transThy
  (postReport, sign', checkedThy) <- checkTranslatedTheory thyOpts sign processActions removedThy
  closedThy <- closeTranslatedTheory thyOpts sign' checkedThy
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
  let processActions = either processActionFactInfos (const []) transThy
      removedThy = first removeTranslationItems transThy
  (postReport, _, _) <- checkTranslatedTheory thyOpts sign processActions removedThy
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
  Just ModuleProVerif -> Export.prettyProVerifTheory ModuleProVerif noReuseLemmas noSourceLemmas noRestrictions noMultiset noPrecise hasSpecificLemmas lemmas <=< Sapic.typeTheoryEnv
  Just ModuleDeepSec -> Export.prettyDeepSecTheory replicationBound
  where
    lemmas = lemmaSelector thyOpts
    hasSpecificLemmas = not (null thyOpts.lemmaNames || thyOpts.lemmaNames == [""] || thyOpts.lemmaNames == ["", ""])
    noReuseLemmas = thyOpts.noReuseLemmas
    noSourceLemmas = thyOpts.noSourceLemmas
    noRestrictions = thyOpts.noRestrictions
    noMultiset = thyOpts.noMultiset
    noPrecise = thyOpts.noPrecise
    replicationBound = thyOpts.replicationBound

-- | Construct an 'AutoProver' from the given arguments (--bound, --stop-on-trace).
constructAutoProver :: TheoryLoadOptions -> AutoProver
constructAutoProver thyOpts =
  AutoProver
    thyOpts.heuristic
    Nothing
    thyOpts.proofBound
    (fromMaybe CutDFS thyOpts.stopOnTrace)
    thyOpts.oracleOnly

-----------------------------------------------
-- Add Options parameters in an OpenTheory
-----------------------------------------------

-- | Add parameters in the OpenTheory, here openchain and saturation in the options
addParamsOptions ::
  TheoryLoadOptions ->
  Either OpenTheory OpenDiffTheory ->
  Either OpenTheory OpenDiffTheory
addParamsOptions opt = addVerboseOptions . addPrecomputationOnlyOptions . addSatArg . addChainsArg . addLemmaToProve . addNdcOption
  where
    -- Add the no deconstruction chain (NDC) check parameter in the Options
    _deductionChainCheck = opt.ndcCheck
    addNdcOption (Left thy) = Left thy {_thyOptions = thy._thyOptions {_deductionChainCheck}}
    addNdcOption (Right diffThy) = Right diffThy {_diffThyOptions = diffThy._diffThyOptions {_deductionChainCheck}}
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
addMessageDeductionRuleVariants :: OpenTranslatedTheory -> WithMaude OpenTranslatedTheory
addMessageDeductionRuleVariants thy0
  | enableBP msig =
      addIntruderVariants
        [ mkDhIntruderVariants,
          mkBpIntruderVariants
        ]
  | enableDH msig = addIntruderVariants [mkDhIntruderVariants]
  | otherwise = thy
  where
    msig = thy0._thySignature._sigMaudeInfo --get (sigpMaudeSig . thySignature) thy0
    rules0 = reader $ \hnd -> subtermConstructorRules False hnd msig ++ specialIntruderRules False
                   ++ (if enableMSet msig then multisetIntruderRules else [])
                   ++ (if enableXor msig then xorIntruderRules else [])
    rulesAC = (destructionRulesAC False (acUserFunSyms msig))
    rulesNoEq = (destructionRulesNoEq False (noEqFunSyms msig))
    rulesACNoEq = liftA2 (++) rulesAC rulesNoEq
    rules = liftA2 (++) rules0 rulesACNoEq
    thy = rules >>= \x -> return (addIntrRuleACsAfterTranslate x thy0)
    addIntruderVariants mkRuless = thy >>= \x -> return (addIntrRuleACsAfterTranslate (concatMap ($ msig) mkRuless) x)

-- FIX-ME : this function exists only for compilation of testParseFile in ParserTests.hs, it don't contain destruction rules for AC user defined function symbol nor subterm intruder rules
addMessageDeductionRuleVariantsWithoutMaude :: OpenTranslatedTheory -> OpenTranslatedTheory
addMessageDeductionRuleVariantsWithoutMaude thy0
  | enableBP msig = addIntruderVariants [ mkDhIntruderVariants
                                        , mkBpIntruderVariants ]
  | enableDH msig = addIntruderVariants [ mkDhIntruderVariants ]
  | otherwise     = thy
  where
    msig         = thy0._thySignature._sigMaudeInfo
    rules        = specialIntruderRules False -- subtermConstructorRules False hnd msig ++ 
                   ++ (if enableMSet msig then multisetIntruderRules else [])
                   ++ (if enableXor msig then xorIntruderRules else [])
    thy          = addIntrRuleACsAfterTranslate rules thy0
    addIntruderVariants mkRuless = addIntrRuleACsAfterTranslate (concatMap ($ msig) mkRuless) thy

-- | Add the variants of the message deduction rule. Uses the cached version
-- of the @"intruder_variants_dh.spthy"@ file for the variants of the message
-- deduction rules for Diffie-Hellman exponentiation.
addMessageDeductionRuleVariantsDiff :: OpenDiffTheory -> WithMaude OpenDiffTheory
addMessageDeductionRuleVariantsDiff thy0
  | enableBP msig =
      addIntruderVariantsDiff
        [ mkDhIntruderVariants,
          mkBpIntruderVariants
        ]
  | enableDH msig = addIntruderVariantsDiff [mkDhIntruderVariants]
  | otherwise = thy >>= \x -> return (addIntrRuleLabels x)
  where
    msig = thy0._diffThySignature._sigMaudeInfo
    rules0 diff' = reader $ \hnd -> subtermConstructorRules diff' hnd msig
        ++ specialIntruderRules diff'
        ++ (if enableNat msig then natIntruderRules else [])
        ++ (if enableMSet msig then multisetIntruderRules else [])
        ++ (if enableXor msig then xorIntruderRules else [])
    rulesAC diff' = (destructionRulesAC diff' (acUserFunSyms msig))
    rulesNoEq diff' =  (destructionRulesNoEq diff' (noEqFunSyms msig))
    rulesACNoEq diff' = liftA2 (++) (rulesAC diff') (rulesNoEq diff')
    rules diff' = liftA2 (++) (rules0 diff') (rulesACNoEq diff')
    bothDiffTh = rules True >>= \x -> return (addIntrRuleACsDiffBothDiff x thy0)
    thy = rules False >>= (\x -> (bothDiffTh >>= (return . addIntrRuleACsDiffBoth x)))
    addIntruderVariantsDiff mkRuless = thy >>= (\x -> return
      (addIntrRuleLabels $
        addIntrRuleACsDiffBothDiff (concatMap ($ msig) mkRuless)
        (addIntrRuleACsDiffBoth (concatMap ($ msig) mkRuless) x)))
