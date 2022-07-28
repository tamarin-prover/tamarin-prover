{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the Tamarin prover.
module Main.Mode.Batch (
    batchMode
  ) where

import           Control.Basics
import           Data.List
import           Data.Bitraversable              (bisequence)
import           System.Console.CmdArgs.Explicit as CmdArgs
import           System.FilePath
import           System.Timing                   (timed)
import           Extension.Data.Label

import qualified Text.PrettyPrint.Class          as Pretty

import           Theory hiding (closeTheory)

import qualified Sapic
import qualified Export

import           Main.Console
import           Main.Environment
import           Main.TheoryLoader
import           Main.Utils

import           Theory.Module
import           Control.Monad.Except (MonadIO(liftIO), runExceptT)
import           System.Exit (die)
import Theory.Tools.Wellformedness (prettyWfErrorReport)

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
    moduleDescriptions = "What to output:" ++ intercalate " " (map (\x -> "\n -"++description x) moduleConstructors) ++ "."

-- | Process a theory file.
run :: TamarinMode -> Arguments -> IO ()
run thisMode as
  | null inFiles = helpAndExit thisMode (Just "no input files given")
  | argExists "parseOnly" as || argExists "outModule" as = do
      res <- mapM processThy inFiles
      let (thys, _) = unzip res

      mapM_ (putStrLn . renderDoc) thys
      putStrLn ""
  | otherwise = do
      _ <- ensureMaude as
      res <- mapM (timed . processThy) inFiles
      let (thys, times) = unzip res
      let (docs, reps) = unzip thys

      if writeOutput then do
        let maybeOutFiles = sequence $ mkOutPath <$> inFiles
        outFiles <- case maybeOutFiles of
          Just f -> return f
          Nothing -> die "Please specify a valid output file/directory"
        let repsWithInfo = ppRep <$> zip4 inFiles (Just <$> outFiles) times reps
        let summary = Pretty.vcat $ intersperse (Pretty.text "") repsWithInfo

        mapM_ (\(o, d) -> writeFileWithDirs o (renderDoc d)) (zip outFiles docs)
        putStrLn $ renderDoc $ ppSummary summary
      else do
        let repsWithInfo = ppRep <$> zip4 inFiles (repeat Nothing) times reps
        let summary = Pretty.vcat $ intersperse (Pretty.text "") repsWithInfo

        mapM_ (putStrLn . renderDoc) docs
        putStrLn $ renderDoc $ ppSummary summary
  where
    ppSummary summary = Pretty.vcat [ Pretty.text $ ""
                                    , Pretty.text $ replicate 78 '='
                                    , Pretty.text $ "summary of summaries:"
                                    , Pretty.text $ ""
                                    , summary
                                    , Pretty.text $ ""
                                    , Pretty.text $ replicate 78 '=' ]

    ppRep (inFile, outFile, time, summary)=
      Pretty.vcat [ Pretty.text $ "analyzed: " ++ inFile
                  , Pretty.text $ ""
                  , Pretty.text $ ""
                  , Pretty.nest 2 $ Pretty.vcat [
                      maybe Pretty.emptyDoc (\o -> Pretty.text $ "output:          " ++ o) outFile
                    , Pretty.text $ "processing time: " ++ show time
                    , Pretty.text $ ""
                    , summary ] ]

    -- handles to arguments
    -----------------------
    inFiles    = reverse $ findArg "inFile" as

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
               return outFile
            <|>
            do outDir <- findArg "outDir" as
               return $ mkAutoPath outDir (takeBaseName inFile)

    -- automatically generate the filename for output
    mkAutoPath :: FilePath -> String -> FilePath
    mkAutoPath dir baseName
      | argExists "html" as = dir </> baseName
      | otherwise           = dir </> addExtension (baseName ++ "_analyzed") "spthy"

    -- theory processing functions
    ------------------------------
    processThy :: FilePath -> IO (Pretty.Doc, Pretty.Doc)
    processThy inFile = either handleError return <=< runExceptT $ do
      srcThy <- liftIO $ readFile inFile
      thy    <- loadTheory thyLoadOptions srcThy inFile

      if isParseOnlyMode then do
        either (\t -> bisequence (liftIO $ choosePretty t, return Pretty.emptyDoc))
               (\d -> return (prettyOpenDiffTheory d, Pretty.emptyDoc)) thy
      else do
        let sig = either (get thySignature) (get diffThySignature) thy
        sig'   <- liftIO $ toSignatureWithMaude (get oMaudePath thyLoadOptions) sig

        (report, thy') <- closeTheory thyLoadOptions sig' thy
        either (\t -> return (prettyClosedTheory t,     ppWf report Pretty.$--$ prettyClosedSummary t))
               (\d -> return (prettyClosedDiffTheory d, ppWf report Pretty.$--$ prettyClosedDiffSummary d)) thy'
      where
        isParseOnlyMode = get oParseOnlyMode thyLoadOptions

        handleError (ParserError e) = error $ show e
        handleError (WarningError report) = do
          putStrLn $ renderDoc $ Pretty.vcat [ Pretty.text ""
                                             , Pretty.text "WARNING: the following wellformedness checks failed!"
                                             , Pretty.text ""
                                             , prettyWfErrorReport report
                                             , Pretty.text "" ]
          die "quit-on-warning mode selected - aborting on wellformedness errors."

        ppWf []  = Pretty.emptyDoc
        ppWf rep = Pretty.vcat $ Pretty.text ("WARNING: " ++ show (length rep) ++ " wellformedness check failed!")
                             : [ Pretty.text   "         The analysis results might be wrong!" | get oProveMode thyLoadOptions ]

        choosePretty = case get oOutputModule thyLoadOptions of
          Nothing               -> return . prettyOpenTheory  <=< Sapic.warnings -- output as is, including SAPIC elements
          Just ModuleSpthy      -> return . prettyOpenTheory  <=< Sapic.warnings -- output as is, including SAPIC elements
          Just ModuleSpthyTyped -> return . prettyOpenTheory <=< Sapic.typeTheory <=< Sapic.warnings  -- additionally type
          Just ModuleMsr        -> return . prettyOpenTranslatedTheory
            <=< (return . filterLemma (lemmaSelector thyLoadOptions))
            <=< (return . removeTranslationItems)
            <=< Sapic.typeTheory
            <=< Sapic.warnings
          Just ModuleProVerif              -> Export.prettyProVerifTheory (lemmaSelector thyLoadOptions) <=< Sapic.typeTheoryEnv <=< Sapic.warnings
          Just ModuleProVerifEquivalence   -> Export.prettyProVerifEquivTheory <=< Sapic.typeTheoryEnv <=< Sapic.warnings
          Just ModuleDeepSec               -> Export.prettyDeepSecTheory <=< Sapic.typeTheory <=< Sapic.warnings