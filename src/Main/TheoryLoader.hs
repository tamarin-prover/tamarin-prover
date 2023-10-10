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
  , oOutputModule
  , oMaudePath
  , oVerboseMode
  , oParseOnlyMode
  , defaultTheoryLoadOptions
  , ArgumentError(..)
  , mkTheoryLoadOptions

  , TheoryLoadError(..)
  , loadTheory
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
import           Data.Maybe                          (fromMaybe)
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
import           Theory.Module (ModuleType (ModuleSpthy, ModuleMsr))

import           TheoryObject                        (diffThyOptions)

import qualified Sapic
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

  , flagOpt (oraclePath defaultOracle) ["oraclename"] (updateArg "oraclename") "FILE"
      ("Path to the oracle heuristic (default '" ++ oraclePath defaultOracle ++ "')")

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
  , _oStopOnTrace       :: SolutionExtractor
  , _oProofBound        :: Maybe Int
  , _oHeuristic         :: Maybe (Heuristic ProofContext)
  , _oPartialEvaluation :: Maybe EvaluationStyle
  , _oDefines           :: [String]
  , _oDiffMode          :: Bool
  , _oQuitOnWarning     :: Bool
  , _oAutoSources       :: Bool
  , _oVerboseMode       :: Bool
  , _oOutputModule      :: Maybe ModuleType -- Note: This flag is only used for batch mode.
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
  , _oStopOnTrace       = CutDFS
  , _oProofBound        = Nothing
  , _oHeuristic         = Nothing
  , _oPartialEvaluation = Nothing
  , _oDefines           = []
  , _oDiffMode          = False
  , _oQuitOnWarning     = False
  , _oAutoSources       = False
  , _oVerboseMode       = False
  , _oOutputModule      = Nothing
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
                         <*> stopOnTrace
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
                                         $ map (mapOracleRanking (maybeSetOracleRelPath (findArg "oraclename" as))) (filterHeuristic (argExists "diff" as) rawRankings)
        Just []                -> throwError $ ArgumentError "heuristic: at least one ranking must be given"
        _                      -> return Nothing

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

    outputModule
    -- MSR is default module, i.e., we translate by default ... otherwise we get warnings for actions used in lemmas that appear only in processes.
     | Nothing  <- findArg "outModule" as = return $ Just ModuleMsr
     -- Otherwise, find output module  that matches string argument
     | Just str <- findArg "outModule" as
     , Just modCon <- find (\x -> show x  == str) (enumFrom minBound) = return $ Just modCon
     | otherwise   = throwError $ ArgumentError "output mode not supported."

    -- NOTE: Output mode implicitly activates parse-only mode
    parseOnlyMode = return $ argExists "parseOnly" as || argExists "outModule" as

    chain = findArg "OpenChainsLimit" as
    chainDefault = L.get oOpenChain defaultTheoryLoadOptions
    openchain = parseIntArg chain chainDefault integerFromInt "OpenChainsLimit: invalid bound given"

    sat = findArg "SaturationLimit" as
    satDefault = L.get oSaturation defaultTheoryLoadOptions
    saturation = parseIntArg sat satDefault integerFromInt "SaturationLimit: invalid bound given"
    
    derivchecks = findArg "derivcheck-timeout" as
    derivDefault = L.get oDerivationChecks defaultTheoryLoadOptions
    deriv = parseIntArg derivchecks derivDefault id "derivcheck-timeout: invalid bound given"

lemmaSelectorByModule :: HasLemmaAttributes l => TheoryLoadOptions -> l -> Bool
lemmaSelectorByModule thyOpt lem = case lemmaModules of
    [] -> True -- default to true if no modules (or only empty ones) are set
    _  -> case L.get oOutputModule thyOpt of
      Just outMod -> outMod `elem` lemmaModules
      Nothing     -> ModuleSpthy `elem` lemmaModules
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

-- FIXME: How can we avoid the MonadCatch here?
loadTheory :: MonadCatch m => TheoryLoadOptions -> String -> FilePath -> ExceptT TheoryLoadError m (Either OpenTheory OpenDiffTheory)
loadTheory thyOpts input inFile = do
    thy <- withExceptT ParserError $ liftEither $ unwrapError $ bimap parse parse thyParser
    let thy' = addParamsOptions thyOpts thy
    withTheory translate thy'
  where
    thyParser | isDiffMode = Right $ diffTheory $ Just inFile
              | otherwise  = Left  $ theory     $ Just inFile

    parse p = parseString (toParserFlags thyOpts) inFile p input

    translate | isMSRModule = Sapic.typeTheory
                          >=> Sapic.translate
                          >=> Acc.translate
              | otherwise   = return

    isDiffMode   = L.get oDiffMode thyOpts
    isMSRModule  = L.get oOutputModule thyOpts == Just ModuleMsr

    unwrapError (Left (Left e)) = Left e
    unwrapError (Left (Right v)) = Right $ Left v
    unwrapError (Right (Left e)) = Left e
    unwrapError (Right (Right v)) = Right $ Right v

    withTheory f = bitraverse f return

closeTheory :: MonadIO m => MonadError TheoryLoadError m => String -> TheoryLoadOptions -> SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> m ((WfErrorReport, Either ClosedTheory ClosedDiffTheory))
closeTheory version thyOpts sign srcThy = do
  let name = either (L.get thyName) (L.get diffThyName) srcThy

  traceM ("[Theory " ++ show name ++ "] Loading Theory")

  let preReport = either (\t -> Sapic.checkWellformedness t ++ Acc.checkWellformedness t)
                         (const []) srcThy

  transThy   <- withTheory (return . removeTranslationItems) srcThy

  let transReport = either (`checkWellformedness` sign)
                           (`checkWellformednessDiff` sign) transThy

  let wellformednessReport = preReport ++ transReport

  when (quitOnWarning && not (null wellformednessReport)) (throwError $ WarningError wellformednessReport)

  deducThy   <- bitraverse (return . addMessageDeductionRuleVariants)
                           (return . addMessageDeductionRuleVariantsDiff) transThy

  variableReport <- case compare derivChecks 0 of
    EQ -> pure $ Just []
    _ -> do
      traceM ("[Theory " ++ show name ++ "] Derivation Checks Begin")
      derivCheckSignature <- Control.Monad.Except.liftIO $ toSignatureWithMaude (get oMaudePath thyOpts) $ maudePublicSig (toSignaturePure sign)
      rep <- Control.Monad.Except.liftIO $ timeout (1000000 * derivChecks) $ evaluate . force $ either (\t -> checkVariableDeducability  t derivCheckSignature autoSources defaultProver)
        (\t-> diffCheckVariableDeducability t derivCheckSignature autoSources defaultProver defaultDiffProver) deducThy
      traceM ("[Theory " ++ show name ++ "] Derivation Checks End")
      return rep


  let report = wellformednessReport  ++ fromMaybe [(underlineTopic "Derivation Checks", Pretty.text "Derivation checks timed out. Use --derivcheck-timeout=INT to configure timeout, 0 to deactivate.")] variableReport

  checkedThy <- bitraverse (return . addComment     (reportToDoc report))
                           (return . addDiffComment (reportToDoc report)) deducThy

  when (quitOnWarning && not (null report)) (throwError $ WarningError report)

  diffLemThy <- withDiffTheory (return . addDefaultDiffLemma) checkedThy
  closedThy  <- bitraverse (\t -> return $ closeTheoryWithMaude     sign t autoSources True)
                           (\t -> return $ closeDiffTheoryWithMaude sign t autoSources) diffLemThy
  partialThy <- bitraverse (return . maybe id (`applyPartialEvaluation` autoSources) partialStyle)
                           (return . maybe id (`applyPartialEvaluationDiff` autoSources) partialStyle) closedThy
  provedThy  <- bitraverse (return . proveTheory     (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover)
                           (return . proveDiffTheory (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover diffProver) partialThy
  provedThyWithVersion <- bitraverse (return . addComment (Pretty.text version))
                           (return . addDiffComment (Pretty.text version) )  provedThy

  traceM ("[Theory " ++ show name ++ "] Theory Loaded")

  return (report, provedThyWithVersion)

  where
    autoSources = L.get oAutoSources thyOpts
    derivChecks = L.get oDerivationChecks thyOpts
    partialStyle = L.get oPartialEvaluation thyOpts
    quitOnWarning = L.get oQuitOnWarning thyOpts

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

    prover | L.get oProveMode thyOpts = replaceSorryProver $ runAutoProver $ constructAutoProver thyOpts
           | otherwise                = mempty

    diffProver | L.get oProveMode thyOpts = replaceDiffSorryProver $ runAutoDiffProver $ constructAutoProver thyOpts
               | otherwise                = mempty

    reportToDoc report
      | null report = Pretty.text "All wellformedness checks were successful."
      | otherwise   = Pretty.vsep
                        [ Pretty.text "WARNING: the following wellformedness checks failed!"
                        , prettyWfErrorReport report ]

    withTheory f = bitraverse f return
    withDiffTheory = bitraverse return

(&&&) :: (t -> Bool) -> (t -> Bool) -> t -> Bool
(&&&) f g x = f x && g x

-- | Construct an 'AutoProver' from the given arguments (--bound,
-- --stop-on-trace).
constructAutoProver :: TheoryLoadOptions -> AutoProver
constructAutoProver thyOpts =
    AutoProver (L.get oHeuristic thyOpts)
               Nothing
               (L.get oProofBound thyOpts)
               (L.get oStopOnTrace thyOpts)

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


