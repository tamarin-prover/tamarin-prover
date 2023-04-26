{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

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
  , lemmaSelector

  , TheoryLoadOptions(..)
  , oProveMode
  , oDiffMode
  , oOutputModule
  , oMaudePath
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

import           Data.Map                            (keys)
import           Data.FileEmbed                      (embedFile)

import           Control.Category

import           System.Console.CmdArgs.Explicit

import           Theory hiding (transReport, closeTheory)
import           Theory.Text.Parser                  (parseIntruderRules, theory, diffTheory)
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.IntruderRules          (specialIntruderRules, subtermIntruderRules
                                                     , multisetIntruderRules, xorIntruderRules)
import           Theory.Tools.Wellformedness
import qualified Sapic as Sapic
import           Main.Console                        (argExists, findArg, addEmptyArg, updateArg, Arguments)

import           Main.Environment

import           Text.Parsec                hiding ((<|>),try,parse)
import           Safe

import qualified Theory.Text.Pretty as Pretty
import           Items.LemmaItem (HasLemmaName, HasLemmaAttributes)
import           Control.Monad.Except
import           Text.Read (readEither, readMaybe)
import           Theory.Module (ModuleType (ModuleSpthy, ModuleMsr))
import           qualified Data.Label as L
import           Data.Bifunctor (Bifunctor(bimap))
import           Data.Bitraversable (Bitraversable(bitraverse))
import           Control.Monad.Catch (MonadCatch)
import qualified Accountability as Acc
import qualified Accountability.Generation as Acc
import GHC.Records (HasField(getField))

import           TheoryObject                        (diffThyOptions)
import           Items.OptionItem                    (openChainsLimit,saturationLimit,lemmasToProve)
import Data.Maybe (fromMaybe, fromJust, isJust)

import qualified Data.Set
import Theory.Text.Parser.Token
import Theory.Tools.MessageDerivationChecks

import System.Directory.Internal.Prelude (timeout)
--import Web.Types (TheoryPath(TheoryRules))


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

  , flagOpt "10" ["open-chains","c"] (updateArg "OpenChainsLimit" ) "PositiveInteger"
      "Limits the number of open chains to be resoled during precomputations (default 10)"

  , flagOpt "5" ["saturation","s"] (updateArg "SaturationLimit" ) "PositiveInteger"
      "Limits the number of saturations during precomputations (default 5)"

  , flagOpt "5" ["derivcheck-timeout"] (updateArg "derivcheck-timeout" ) "INT"
      "Set timeout for message derivation checks"


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

    proofBound = case maybe (Right Nothing) readEither (findArg "bound" as) of
      Left _ -> throwError $ ArgumentError "bound: invalid bound given"
      Right b -> liftEither $ Right b

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
      Nothing        -> return $ Nothing

    defines       = return $ findArg "defines" as
    diffMode      = return $ argExists "diff" as
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
    openchain = if not (null chain)
                  then return (fromMaybe chainDefault (readMaybe (head chain) ::Maybe Integer))
                  else return chainDefault
    -- FIXME : use "read" and handle potential error without crash (with default version and raising error)

    sat = findArg "SaturationLimit" as
    satDefault = L.get oSaturation defaultTheoryLoadOptions
    saturation = if not (null sat)
                   then return (fromMaybe satDefault (readMaybe (head sat) ::Maybe Integer))
                   else return satDefault
    -- FIXME : use "read" and handle potential error without crash (with default version and raising error)

    derivchecks = findArg "derivcheck-timeout" as
    derivDefault = L.get oDerivationChecks defaultTheoryLoadOptions
    deriv = if not (null derivchecks)
                   then return (fromMaybe derivDefault (readMaybe (head derivchecks) :: Maybe Int))
                   else return derivDefault
    -- FIXME : use "read" and handle potential error without crash (with default version and raising error)

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

    translate | isMSRModule   = Sapic.typeTheory
                              >=> Sapic.translate
                              >=> Acc.translate
              | otherwise     = return

    isDiffMode   = L.get oDiffMode thyOpts
    isMSRModule  = L.get oOutputModule thyOpts == Just ModuleMsr

    unwrapError (Left (Left e)) = Left e
    unwrapError (Left (Right v)) = Right $ Left v
    unwrapError (Right (Left e)) = Left e
    unwrapError (Right (Right v)) = Right $ Right v

    withTheory     f t = bitraverse f return t

closeTheory :: MonadIO m => MonadError TheoryLoadError m => String -> TheoryLoadOptions -> SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> m ((WfErrorReport, Either ClosedTheory ClosedDiffTheory))
closeTheory version thyOpts sig srcThy = do
  let preReport = either (\t -> (Sapic.checkWellformedness t ++ Acc.checkWellformedness t))
                         (const []) srcThy

  transThy   <- withTheory (return . removeTranslationItems) srcThy

  let transReport = either (\t -> checkWellformedness t sig)
                           (\t -> checkWellformednessDiff t sig) transThy

  let wellformednessReport = preReport ++ transReport

  checkedThy <- bitraverse (\t -> return $ addComment     (reportToDoc wellformednessReport) t)
                           (\t -> return $ addDiffComment (reportToDoc wellformednessReport) t) transThy

  when (quitOnWarning && (not $ null wellformednessReport)) (throwError $ WarningError wellformednessReport)

  deducThy   <- bitraverse (return . addMessageDeductionRuleVariants)
                           (return . addMessageDeductionRuleVariantsDiff) transThy

  derivCheckSignature <- Control.Monad.Except.liftIO $ toSignatureWithMaude (get oMaudePath thyOpts) $ maudePublicSig (toSignaturePure sig)
  variableReport <- case compare derivChecks 0 of
    EQ -> pure $ Just []
    _ -> Control.Monad.Except.liftIO $ timeout (1000000 * derivChecks) $ (either (\t -> checkVariableDeducability  t derivCheckSignature autoSources defaultProver)
      (\t-> diffCheckVariableDeducability t derivCheckSignature autoSources defaultProver defaultDiffProver) deducThy)

  let report = wellformednessReport  ++ (if isJust variableReport then fromJust variableReport else [("Timed Out", Pretty.text "Derivation Checks")])

  checkedThy <- bitraverse (\t -> return $ addComment     (reportToDoc report) t)
                           (\t -> return $ addDiffComment (reportToDoc report) t) deducThy

  when (quitOnWarning && (not $ null report)) (throwError $ WarningError report)

  diffLemThy <- withDiffTheory (return . addDefaultDiffLemma) checkedThy
  closedThy  <- bitraverse (\t -> return $ closeTheoryWithMaude     sig t autoSources)
                           (\t -> return $ closeDiffTheoryWithMaude sig t autoSources) diffLemThy
  partialThy <- bitraverse (return . (maybe id (\s -> applyPartialEvaluation     s autoSources) partialStyle))
                           (return . (maybe id (\s -> applyPartialEvaluationDiff s autoSources) partialStyle)) closedThy
  provedThy  <- bitraverse (\t -> return $ proveTheory     (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover t)
                           (\t -> return $ proveDiffTheory (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover diffProver t) partialThy
  provedThyWithVersion <- bitraverse (return . addComment (Pretty.text version))
                           (return . addDiffComment (Pretty.text version) )  provedThy

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
    getSignature s =  (Data.Label.get sigpMaudeSig s)
    makepublic = Data.Set.map (\(name, (int, _, construct)) -> (name,(int, Public, construct)))
    makepublicsym  = Data.Set.map (\elem -> case elem of
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

    withTheory     f t = bitraverse f return t
    withDiffTheory f t = bitraverse return f t

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
addParamsOptions opt = addSatArg . addChainsArg . addLemmaToProve

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


