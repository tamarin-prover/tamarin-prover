{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}

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

  , TheoryLoadOptions(..)
  , oDiffMode
  , oOutputModule
  , oMaudePath
  , oParseOnlyMode
  , defaultTheoryLoadOptions
  , ArgumentError(..)
  , mkTheoryLoadOptions

  , TheoryLoadError(..)
  , loadTheory
  , closeTheory'

  -- ** Loading open theories
  , loadOpenThy

  -- ** Loading and closing theories
  , loadClosedThyWf
  , loadClosedThyWfReport
  , reportOnClosedThyStringWellformedness
  , reportWellformednessDoc


  -- ** Loading open diff theories
  , loadOpenDiffThy

  -- ** Loading and closing diff theories
  , loadClosedDiffThy
  , loadClosedDiffThyWfReport
  , loadClosedDiffThyString
  , reportOnClosedDiffThyStringWellformedness


  -- ** Constructing automatic prover
  , constructAutoProver

  -- ** Cached Message Deduction Rule Variants
  , dhIntruderVariantsFile
  , bpIntruderVariantsFile
  , addMessageDeductionRuleVariants

  , lemmaSelector
  ) where

import           Debug.Trace

import           Prelude                             hiding (id, (.))

import           Data.Char                           (toLower)
import           Data.Label
import           Data.List                           (isPrefixOf,intersperse, find)
import           Data.Map                            (keys)
import           Data.FileEmbed                      (embedFile)

import           Control.Category

import           System.Console.CmdArgs.Explicit

import           Theory
import           Theory.Text.Parser                  (parseIntruderRules, parseOpenTheory, parseOpenTheoryString, parseOpenDiffTheory, parseOpenDiffTheoryString, theory, diffTheory)
import           Theory.Tools.AbstractInterpretation (EvaluationStyle(..))
import           Theory.Tools.IntruderRules          (specialIntruderRules, subtermIntruderRules
                                                     , multisetIntruderRules, xorIntruderRules)
import           Theory.Tools.Wellformedness
import qualified Sapic as Sapic
import           Main.Console                        (renderDoc, argExists, findArg, addEmptyArg, updateArg, Arguments)

import           Main.Environment

import           Text.Parsec                hiding ((<|>),try,parse)
import           Safe
import qualified Theory.Text.Pretty as Pretty
import           Items.LemmaItem (HasLemmaName, HasLemmaAttributes)
import           Control.Monad.Except
import           Text.Read (readEither)
import           Theory.Module (ModuleType (ModuleSpthy, ModuleMsr))
import           qualified Data.Label as L
import           Theory.Text.Parser.Token (parseString)
import           Data.Bifunctor (Bifunctor(bimap))
import           Data.Bitraversable (Bitraversable(bitraverse))
import           Control.Monad.Catch (MonadCatch)
import qualified Accountability as Acc
import qualified Accountability.Generation as Acc

------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------


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

  , flagOpt (prettyGoalRanking $ head $ defaultRankings False)
      ["heuristic"] (updateArg "heuristic") ("(" ++ intersperse '|' (keys goalRankingIdentifiers) ++ ")+")
      ("Sequence of goal rankings to use (default '" ++ prettyGoalRanking (head $ defaultRankings False) ++ "')")

  , flagOpt "summary" ["partial-evaluation"] (updateArg "partial-evaluation")
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
  ]

data TheoryLoadOptions = TheoryLoadOptions {
    _oProveMode         :: Bool
  , _oLemmaNames        :: [String]
  , _oStopOnTrace       :: SolutionExtractor
  , _oProofBound        :: Maybe Int
  , _oHeuristic         :: Maybe Heuristic
  , _oPartialEvaluation :: Maybe EvaluationStyle
  , _oDefines           :: [String]
  , _oDiffMode          :: Bool
  , _oQuitOnWarning     :: Bool
  , _oAutoSources       :: Bool
  , _oOutputModule      :: Maybe ModuleType -- Note: This flag is only used for batch mode.
  , _oMaudePath         :: FilePath -- FIXME: Other functions defined in Environment.hs
  , _oParseOnlyMode     :: Bool
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
}

toParserFlags :: TheoryLoadOptions -> [String]
toParserFlags thyOpts = concat
  [ [ "diff" |  _oDiffMode thyOpts ]
  , _oDefines thyOpts
  , [ "quit-on-warning" | _oQuitOnWarning thyOpts ] ]

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
                                         $ map (mapOracleRanking (maybeSetOracleRelPath (findArg "oraclename" as)) . toGoalRanking) rawRankings
        Just []                -> throwError $ ArgumentError "heuristic: at least one ranking must be given"
        _                      -> return Nothing

    toGoalRanking | argExists "diff" as = charToGoalRankingDiff
                  | otherwise           = charToGoalRanking

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
     | Nothing  <- findArg "outModule" as , [] /= findArg "prove" as = return $ Just ModuleMsr
     -- ^ when proving, we act like we chose the Msr Output module.
     | Nothing  <- findArg "outModule" as = return $ Just ModuleSpthy -- default
     | Just str <- findArg "outModule" as
     , Just modCon <- find (\x -> show x  == str) (enumFrom minBound) = return $ Just modCon
     | otherwise   = throwError $ ArgumentError "output mode not supported."

    -- Note: Output mode implicitly activates parse-only mode
    parseOnlyMode = return $ argExists "parseOnly" as || argExists "outputMode" as

lemmaSelectorByModule :: HasLemmaAttributes l => TheoryLoadOptions -> l -> Bool
lemmaSelectorByModule thyOpt lem = case lemmaModules of
    [] -> True -- default to true if no modules (or only empty ones) are set
    _  -> case (L.get oOutputModule thyOpt) of
      Just outMod -> outMod `elem` lemmaModules
      Nothing     -> ModuleSpthy `elem` lemmaModules
    where
        lemmaModules = concat [ m | LemmaModule m <- lem.lAttributes]

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
        | lastMay pattern == Just '*' = init pattern `isPrefixOf` lem.lName
        | otherwise = lem.lName == pattern


-- | Load an open theory from a file.
loadOpenThy :: TheoryLoadOptions -> FilePath -> IO OpenTheory
loadOpenThy thyOpts inFile = parseOpenTheory (toParserFlags thyOpts) inFile

data TheoryLoadError =
    ParserError ParseError
  | WarningError WfErrorReport

instance Show TheoryLoadError
  where
    show (ParserError e) = "ParserError " ++ show e
    show (WarningError e) = "WarningError " ++ Pretty.render (prettyWfErrorReport e)

-- FIXME: How can we avoid the MonadCatch here?
loadTheory :: MonadCatch m => TheoryLoadOptions -> String -> FilePath -> ExceptT TheoryLoadError m (Either OpenTheory OpenDiffTheory)
loadTheory thyOpts input inFile = do
    thy <- withExceptT ParserError $ liftEither $ unwrapError $ bimap parse parse thyParser
    withTheory translate thy
  where
    thyParser | isDiffMode = Right $ diffTheory $ Just inFile
              | otherwise  = Left  $ theory     $ Just inFile

    parse p = parseString (toParserFlags thyOpts) inFile p input

    translate | isParseOnlyMode = return
              | otherwise       = Sapic.typeTheory
                              >=> Sapic.translate
                              >=> Acc.translate

    isDiffMode      = L.get oDiffMode thyOpts
    isParseOnlyMode = L.get oParseOnlyMode thyOpts

    unwrapError (Left (Left e)) = Left e
    unwrapError (Left (Right v)) = Right $ Left v
    unwrapError (Right (Left e)) = Left e
    unwrapError (Right (Right v)) = Right $ Right v

    withTheory     f t = bitraverse f return t

closeTheory' :: MonadError TheoryLoadError m => TheoryLoadOptions -> SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> m ((WfErrorReport, Either ClosedTheory ClosedDiffTheory))
closeTheory' thyOpts sig srcThy = do
  let preReport = either (\t -> (Sapic.checkWellformedness t ++ Acc.checkWellformedness t))
                         (const []) srcThy

  transThy   <- withTheory (return . removeTranslationItems) srcThy

  let transReport = either (\t -> checkWellformedness t sig)
                           (\t -> checkWellformednessDiff t sig) transThy

  let report = preReport ++ transReport
  checkedThy <- bitraverse (\t -> return $ addComment     (reportToDoc report) t)
                           (\t -> return $ addDiffComment (reportToDoc report) t) transThy

  when (quitOnWarning && (not $ null report)) (throwError $ WarningError report)

  deducThy   <- bitraverse (return . addMessageDeductionRuleVariants)
                           (return . addMessageDeductionRuleVariantsDiff) checkedThy
  diffLemThy <- withDiffTheory (return . addDefaultDiffLemma) deducThy
  closedThy  <- bitraverse (\t -> return $ closeTheoryWithMaude     sig t autoSources)
                           (\t -> return $ closeDiffTheoryWithMaude sig t autoSources) diffLemThy
  partialThy <- bitraverse (return . (maybe id (\s -> applyPartialEvaluation     s autoSources) partialStyle))
                           (return . (maybe id (\s -> applyPartialEvaluationDiff s autoSources) partialStyle)) closedThy
  provedThy  <- bitraverse (\t -> return $ proveTheory     (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover t)
                           (\t -> return $ proveDiffTheory (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover diffProver t) partialThy
  return (report, provedThy)

  where
    autoSources   = L.get oAutoSources thyOpts
    partialStyle  = L.get oPartialEvaluation thyOpts
    quitOnWarning = L.get oQuitOnWarning thyOpts

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

-- | Load an open theory from a file. Returns the open and the translated theory.
loadOpenAndTranslatedThy :: TheoryLoadOptions -> FilePath -> IO (OpenTheory, OpenTranslatedTheory)
loadOpenAndTranslatedThy thyOpts inFile =  do
    thy <- loadOpenThy thyOpts inFile
    transThy <-
      Sapic.typeTheory thy
      >>= Sapic.translate
      >>= Acc.translate
    return (thy, removeTranslationItems transThy)

-- | Load an open diff theory from a file.
loadOpenDiffThy :: TheoryLoadOptions -> FilePath -> IO OpenDiffTheory
loadOpenDiffThy thyOpts = parseOpenDiffTheory (toParserFlags thyOpts)

-- | Load a closed diff theory from a file.
loadClosedDiffThy :: TheoryLoadOptions -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThy thyOpts inFile = do
  thy0 <- loadOpenDiffThy thyOpts inFile
  thy1 <- return $ addMessageDeductionRuleVariantsDiff thy0
  closeDiffThy thyOpts thy1

reportWellformednessDoc :: WfErrorReport  -> Pretty.Doc
reportWellformednessDoc [] =  Pretty.emptyDoc
reportWellformednessDoc errs  = Pretty.vcat
                          [ Pretty.text $ "WARNING: " ++ show (length errs)
                                                      ++ " wellformedness check failed!"
                          , Pretty.text "         The analysis results might be wrong!"
                          , prettyWfErrorReport errs
                          ]

-- | Report well-formedness errors unless empty. Quit on warning. Start with prefix `prefixAct`
reportWellformedness :: IO a -> Bool -> WfErrorReport -> IO ()
reportWellformedness _          _            []       = return ()
reportWellformedness prefixAct quit           wfreport =
   do
      _ <- prefixAct -- optional: printout of file name or similar
      putStrLn "WARNING: ignoring the following wellformedness errors"
      putStrLn ""
      putStrLn $ renderDoc $ prettyWfErrorReport wfreport
      putStrLn $ replicate 78 '-'
      if quit then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""

-- | helper function: print header with theory filename
printFileName :: [Char] -> IO ()
printFileName inFile = do
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Theory file '" ++ inFile ++ "'"
          putStrLn $ replicate 78 '-'
          putStrLn ""

loadClosedThyWf :: TheoryLoadOptions -> FilePath -> IO (ClosedTheory, Pretty.Doc)
loadClosedThyWf thyOpts inFile = do
    (openThy, transThy0) <- loadOpenAndTranslatedThy thyOpts inFile
    transThy <- return $ addMessageDeductionRuleVariants transThy0
    sig <- toSignatureWithMaude (L.get oMaudePath thyOpts) $ get thySignature transThy
    -- report
    let errors = checkWellformedness transThy sig ++ Sapic.checkWellformedness openThy ++ Acc.checkWellformedness openThy
    let report = reportWellformednessDoc errors
    -- return closed theory
    let closedTheory = closeThyWithMaude sig thyOpts openThy transThy
    return (closedTheory, report)

-- | Load a closed theory and report on well-formedness errors.
loadClosedThyWfReport :: TheoryLoadOptions -> FilePath -> IO ClosedTheory
loadClosedThyWfReport thyOpts inFile = do
    (openThy, transThy0) <- loadOpenAndTranslatedThy thyOpts inFile
    transThy <- return $ addMessageDeductionRuleVariants transThy0
    transSig <- toSignatureWithMaude (L.get oMaudePath thyOpts) $ get thySignature transThy
    -- report
    let prefix = printFileName inFile
    let errors = checkWellformedness transThy transSig ++ Sapic.checkWellformedness openThy ++ Acc.checkWellformedness openThy
    reportWellformedness prefix (L.get oQuitOnWarning thyOpts) errors
    -- return closed theory
    return $ closeThyWithMaude transSig thyOpts openThy transThy

-- | Load a closed diff theory and report on well-formedness errors.
loadClosedDiffThyWfReport :: TheoryLoadOptions -> FilePath -> IO ClosedDiffTheory
loadClosedDiffThyWfReport thyOpts inFile = do
    thy0 <- loadOpenDiffThy thyOpts inFile
    thy1 <- return $ addMessageDeductionRuleVariantsDiff thy0
    sig <- toSignatureWithMaude (L.get oMaudePath thyOpts) $ get diffThySignature thy1
    -- report
    let prefix = printFileName inFile
    let errors = checkWellformednessDiff thy1 sig
    reportWellformedness prefix (L.get oQuitOnWarning thyOpts) errors
    -- return closed theory
    return $ closeDiffThyWithMaude sig thyOpts thy1

-- loadClosedThyString :: TheoryLoadOptions -> String -> IO (Either String ClosedTheory)
-- loadClosedThyString thyOpts input =
--     case parseOpenTheoryString (toParserFlags thyOpts) input of
--         Left err  -> return $ Left $ "parse error: " ++ show err
--         Right thy -> do
--             thy' <-  Sapic.typeTheory thy
--                   >>= Sapic.translate
--                   >>= Acc.translate
--             Right <$> closeThy thyOpts thy (removeTranslationItems thy') -- No "return" because closeThy gives IO (ClosedTheory)


loadClosedDiffThyString :: TheoryLoadOptions -> String -> IO (Either String ClosedDiffTheory)
loadClosedDiffThyString thyOpts input =
    case parseOpenDiffTheoryString (toParserFlags thyOpts) input of
        Left err  -> return $ Left $ "parse error: " ++ show err
        Right thy -> fmap Right $ do
          thy1 <- return $ addMessageDeductionRuleVariantsDiff thy
          closeDiffThy thyOpts thy1

-- | Load an open theory from a string.
loadOpenThyString :: TheoryLoadOptions -> String -> Either ParseError OpenTheory
loadOpenThyString thyOpts = parseOpenTheoryString (toParserFlags thyOpts)

-- | Load an open theory from a string.
loadOpenDiffThyString :: TheoryLoadOptions -> String -> Either ParseError OpenDiffTheory
loadOpenDiffThyString thyOpts = parseOpenDiffTheoryString (toParserFlags thyOpts)

-- | Load a close theory and only report on well-formedness errors or translation errors
reportOnClosedThyStringWellformedness :: TheoryLoadOptions -> String -> IO String
reportOnClosedThyStringWellformedness thyOpts input =
    case loadOpenThyString thyOpts input of
      Left  err   -> return $ "parse error: " ++ show err
      Right openThy -> do
            transThy <- Sapic.typeTheory openThy
                  >>= Sapic.translate
                  >>= Acc.translate
            transSig <- toSignatureWithMaude (L.get oMaudePath thyOpts) $ get thySignature transThy
            -- report
            let errors = checkWellformedness (removeTranslationItems transThy) transSig
                      ++ Sapic.checkWellformedness openThy
                      ++ Acc.checkWellformedness openThy
            case errors of
                  []     -> return ""
                  report -> do
                    if (L.get oQuitOnWarning thyOpts) then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""
                    return $ " WARNING: ignoring the following wellformedness errors: " ++(renderDoc $ prettyWfErrorReport report)

-- | Load a closed diff theory and report on well-formedness errors.
reportOnClosedDiffThyStringWellformedness :: TheoryLoadOptions -> String -> IO String
reportOnClosedDiffThyStringWellformedness thyOpts input = do
    case loadOpenDiffThyString thyOpts input of
      Left  err   -> return $ "parse error: " ++ show err
      Right thy0 -> do
        thy1 <- return $ addMessageDeductionRuleVariantsDiff thy0
        sig <- toSignatureWithMaude (L.get oMaudePath thyOpts) $ get diffThySignature thy1
        -- report
        case checkWellformednessDiff thy1 sig of
          []     -> return ""
          report -> do
            if (L.get oQuitOnWarning thyOpts) then error "quit-on-warning mode selected - aborting on wellformedness errors." else putStrLn ""
            return $ " WARNING: ignoring the following wellformedness errors: " ++(renderDoc $ prettyWfErrorReport report)

-- | Close a theory according to arguments.
-- closeThy :: TheoryLoadOptions -> OpenTheory -> OpenTranslatedTheory -> IO ClosedTheory
-- closeThy thyOpts openThy transThy = do
--   transThy' <- return $ addMessageDeductionRuleVariants transThy
--   sig <- toSignatureWithMaude (L.get oMaudePath thyOpts) $ get thySignature transThy'
--   return $ closeThyWithMaude sig thyOpts openThy transThy'

-- | Close a theory according to arguments.
closeThyWithMaude :: SignatureWithMaude -> TheoryLoadOptions -> OpenTheory -> OpenTranslatedTheory -> ClosedTheory
closeThyWithMaude sig thyOpts openThy transThy =
      proveTheory (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover $ partialEvaluation closedThy
    where
      -- FIXME: wf-check is at the wrong position here. Needs to be more
      -- fine-grained.
      transThy' = wfCheck openThy transThy
      -- close and prove
      closedThy = closeTheoryWithMaude sig transThy' (L.get oAutoSources thyOpts)
      -- apply partial application
      ----------------------------
      partialEvaluation = case (L.get oPartialEvaluation thyOpts) of
        Just style -> applyPartialEvaluation style (L.get oAutoSources thyOpts)
        Nothing    -> id

      -- wellformedness check
      -----------------------
      wfCheck :: OpenTheory -> OpenTranslatedTheory -> OpenTranslatedTheory
      wfCheck othy tthy =
        noteWellformedness
          (checkWellformedness tthy sig ++ Acc.checkWellformedness othy) transThy (L.get oQuitOnWarning thyOpts)

      -- replace all annotated sorrys with the configured autoprover.
      prover :: Prover
      prover | L.get oProveMode thyOpts =
                  replaceSorryProver $ runAutoProver $ constructAutoProver thyOpts
             | otherwise            = mempty

-- | Close a diff theory according to arguments.
closeDiffThy :: TheoryLoadOptions -> OpenDiffTheory -> IO ClosedDiffTheory
closeDiffThy thyOpts thy0 = do
  sig <- toSignatureWithMaude (L.get oMaudePath thyOpts) $ get diffThySignature thy0
  return $ closeDiffThyWithMaude sig thyOpts thy0

(&&&) :: (t -> Bool) -> (t -> Bool) -> t -> Bool
(&&&) f g x = f x && g x

-- | Close a diff theory according to arguments.
closeDiffThyWithMaude :: SignatureWithMaude -> TheoryLoadOptions -> OpenDiffTheory -> ClosedDiffTheory
closeDiffThyWithMaude sig thyOpts thy0 =
      proveDiffTheory (lemmaSelectorByModule thyOpts &&& lemmaSelector thyOpts) prover diffprover $ partialEvaluation cthy
    where
      -- FIXME: wf-check is at the wrong position here. Needs to be more
      -- fine-grained.
      thy2 = wfCheckDiff thy0
      -- close and prove
      cthy = closeDiffTheoryWithMaude sig (addDefaultDiffLemma thy2) (L.get oAutoSources thyOpts)
      -- apply partial application
      ----------------------------
      partialEvaluation = case (L.get oPartialEvaluation thyOpts) of
        Just style -> applyPartialEvaluationDiff style (L.get oAutoSources thyOpts)
        Nothing    -> id

      -- wellformedness check
      -----------------------
      wfCheckDiff :: OpenDiffTheory -> OpenDiffTheory
      wfCheckDiff thy =
        noteWellformednessDiff
          (checkWellformednessDiff thy sig) thy (L.get oQuitOnWarning thyOpts)

      -- diff prover: replace all annotated sorrys with the configured autoprover.
      diffprover :: DiffProver
      diffprover | L.get oProveMode thyOpts =
                         replaceDiffSorryProver $ runAutoDiffProver $ constructAutoProver thyOpts
                 | otherwise            = mempty

      -- replace all annotated sorrys with the configured autoprover.
      prover :: Prover
      prover | L.get oProveMode thyOpts =
                  replaceSorryProver $ runAutoProver $ constructAutoProver thyOpts
             | otherwise            = mempty

-- | Construct an 'AutoProver' from the given arguments (--bound,
-- --stop-on-trace).
constructAutoProver :: TheoryLoadOptions -> AutoProver
constructAutoProver thyOpts =
    AutoProver (L.get oHeuristic thyOpts)
               (L.get oProofBound thyOpts)
               (L.get oStopOnTrace thyOpts)

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
