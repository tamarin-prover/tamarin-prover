-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Main module for the Tamarin prover.
module Main.Mode.Batch (
    batchMode
  ) where

import Control.Applicative ((<|>))
import Control.Monad (guard, (<=<))
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Bifunctor (bimap)
import Data.List
import System.Console.CmdArgs.Explicit as CmdArgs
import System.Exit (die)
import System.FilePath
import System.Timing (timedIO)
import Extension.Data.Label

import Text.PrettyPrint.Class qualified as Pretty
import Text.Printf (printf)

import Theory hiding (closeTheory)
import Theory.Module
import Theory.Tools.Wellformedness (prettyWfErrorReport)

import Main.Console
import Main.Environment
import Main.TheoryLoader
import Main.Utils

-- | Batch processing mode.
batchMode :: TamarinMode
batchMode = tamarinMode
  "batch"
  "Security protocol analysis and verification."
  setupFlags
  run
  where
    setupFlags defaultMode = defaultMode
      { modeArgs       = ([], Just $ flagArg (updateArg "inFile") "FILES")
      , modeGroupFlags = Group
          { groupUnnamed =
              theoryLoadFlags ++
              -- [ flagNone ["html"] (addEmptyArg "html")
              --     "generate HTML visualization of proofs"

              [ flagNone ["no-compress"] (addEmptyArg "noCompress")
                  "Do not use compressed sequent visualization"

              , flagNone ["parse-only"] (addEmptyArg "parseOnly")
                  "Just parse the input file and pretty print it as-is"
              ] ++
              outputFlags ++
              toolFlags
          , groupHidden = []
          , groupNamed = []
          }
      }

    outputFlags =
      [ flagOpt "" ["output","o"] (updateArg "outFile") "FILE" "Output file"
      , flagOpt "" ["Output","O"] (updateArg "outDir") "DIR"  "Output directory"
      , flagOpt "spthy" ["output-module", "m"] (updateArg "outModule") moduleList
        moduleDescriptions
      ]
    moduleConstructors = enumFrom minBound :: [ModuleType]
    moduleList = intercalate "|" $ map show moduleConstructors
    moduleDescriptions = "What to output:" ++ unwords (map (\x -> "\n -"++description x) moduleConstructors) ++ "."

-- | Process a theory file.
run :: TamarinMode -> Arguments -> IO ()
run thisMode as
  | null inFiles = helpAndExit thisMode (Just "no input files given")
  | argExists "parseOnly" as = do
      res <- mapM (processThy "") inFiles
      let (docs, _) = unzip res

      mapM_ (putStrLn . renderDoc) docs
  | argExists "outModule" as = do
      versionData <- ensureMaudeAndGetVersion as
      res <- mapM (processThy versionData) inFiles
      let (docs, _) = unzip res

      mapM_ (putStrLn . renderDoc) docs
  | otherwise = do
      versionData <- ensureMaudeAndGetVersion as
      resTimed <- mapM (timedIO . processThy versionData) inFiles
      let (docs, reps, times) = unzip3 $ fmap (\((d, r), t) -> (d, r, t)) resTimed

      if writeOutput then do
        let maybeOutFiles = mapM mkOutPath inFiles
        outFiles <- case maybeOutFiles of
          Just f -> pure f
          Nothing -> die "Please specify a valid output file/directory"
        let repsWithInfo = ppRep <$> zip4 inFiles (Just <$> outFiles) (Just <$> times) reps
        let summary = Pretty.vcat $ intersperse (Pretty.text "") repsWithInfo

        mapM_ (\(o, d) -> writeFileWithDirs o (renderDoc d)) (zip outFiles docs)
        putStrLn $ renderDoc $ ppSummary summary
      else do
        let repsWithInfo = ppRep <$> zip4 inFiles (repeat Nothing) (Just <$> times) reps
        let summary = Pretty.vcat $ intersperse (Pretty.text "") repsWithInfo

        mapM_ (putStrLn . renderDoc) docs
        putStrLn $ renderDoc $ ppSummary summary

  where
    ppSummary summary = Pretty.vcat [ Pretty.text ""
                                    , Pretty.text $ replicate 78 '='
                                    , Pretty.text "summary of summaries:"
                                    , Pretty.text ""
                                    , summary
                                    , Pretty.text ""
                                    , Pretty.text $ replicate 78 '=' ]

    ppRep (inFile, outFile, time, summary) =
      Pretty.vcat
        [ Pretty.text $ "analyzed: " ++ inFile
        , Pretty.text ""
        , Pretty.text ""
        , Pretty.nest 2 $ Pretty.vcat
          [ maybe Pretty.emptyDoc (\o -> Pretty.text $ "output:          " ++ o) outFile
          , maybe Pretty.emptyDoc (\t -> Pretty.text $ printf "processing time: %.2fs" (realToFrac t :: Double)) time
          , Pretty.text ""
          , summary
          ]
        ]

    -- handles to arguments
    -----------------------
    inFiles = reverse $ findArg "inFile" as

    thyLoadOptions = case mkTheoryLoadOptions as of
      Left (ArgumentError e) -> error e
      Right opts             -> opts

    -- output generation
    --------------------
    writeOutput = argExists "outFile" as || argExists "outDir" as

    mkOutPath :: FilePath  -- ^ Input file name.
              -> Maybe FilePath  -- ^ Output file name.
    mkOutPath inFile =
      do outFile <- findArg "outFile" as
         guard (outFile /= "")
         pure outFile
      <|>
      do outDir <- findArg "outDir" as
         pure $ mkAutoPath outDir (takeBaseName inFile)

    -- automatically generate the filename for output
    mkAutoPath :: FilePath -> String -> FilePath
    mkAutoPath dir baseName
      | argExists "html" as = dir </> baseName
      | otherwise           = dir </> addExtension (baseName ++ "_analyzed") "spthy"

    -- theory processing functions
    ------------------------------

    processThy :: String -> FilePath -> IO (Pretty.Doc, Pretty.Doc)
    processThy versionData inFile = either handleError pure <=< runExceptT $ do
      srcThy <- liftIO $ readFile inFile
      thy    <- loadTheory thyLoadOptions srcThy inFile

      let sig = either (._thySignature) (._diffThySignature) thy
      sig'   <- liftIO $ toSignatureWithMaude thyLoadOptions._oMaudePath sig

      -- | Pretty print the theory as is without performing any checks.
      if thyLoadOptions._oParseOnlyMode then
        pure $ (, Pretty.emptyDoc) $ either prettyOpenTheory prettyOpenDiffTheory thy

      -- | Translate and check thoery based on specified output module.
      else if isTranslateOnlyMode then do
        (report, thy') <- translateAndCheckTheory versionData thyLoadOptions sig' thy

        let thy'' = bimap (modify thyItems (++ (TextItem <$> formalComments thy')))
                          (modify diffThyItems (++ (DiffTextItem <$> formalComments thy')))
                          thy'

        (, ppWf report) <$> either (liftIO . prettyOpenTheoryByModule thyLoadOptions)
                                   (pure . prettyOpenDiffTheory)
                                   thy''

      -- | Close and potentially prove theory.
      else do
        (report, thy') <- closeTheory versionData thyLoadOptions sig' thy
        pure $
          either (\t -> (prettyClosedTheory t,     ppWf report Pretty.$--$ prettyClosedSummary t))
                 (\d -> (prettyClosedDiffTheory d, ppWf report Pretty.$--$ prettyClosedDiffSummary d))
                 thy'
      where
        formalComments =
          filter (/= ("", "")) . either theoryFormalComments diffTheoryFormalComments

        isTranslateOnlyMode =
          thyLoadOptions._oOutputModule `elem`
            [ ModuleSpthy
            , ModuleSpthyTyped
            , ModuleProVerif
            , ModuleProVerifEquivalence
            , ModuleDeepSec
            ]

        handleError e@(ParserError _) = die $ show e
        handleError (WarningError report) = do
          putStrLn $ renderDoc $ Pretty.vcat $ [ Pretty.text ""
                                               , Pretty.text "WARNING: the following wellformedness checks failed!" ]
                                            ++ [ Pretty.text "" | not $ null report ]
                                            ++ [ prettyWfErrorReport report
                                               , Pretty.text "" ]
          die "quit-on-warning mode selected - aborting on wellformedness errors."

        ppWf []  = Pretty.emptyDoc
        ppWf rep = Pretty.vcat $
          Pretty.text ("WARNING: " ++ show (length rep) ++ " wellformedness check failed!")
          : [ Pretty.text   "         The analysis results might be wrong!" | thyLoadOptions._oProveMode ]
