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
import           Control.DeepSeq                 (force)
import           Control.Exception               (evaluate)
import           Data.List
import           Data.Maybe
import           System.Console.CmdArgs.Explicit as CmdArgs
import           System.FilePath
import           System.Timing                   (timed)
import           Extension.Data.Label

import qualified Text.PrettyPrint.Class          as Pretty

import           Theory
import           Theory.Tools.Wellformedness     (checkWellformednessDiff)

import qualified Sapic
import qualified Export

import           Main.Console
import           Main.Environment
import           Main.TheoryLoader
import           Main.Utils

import           Theory.Module
import           Control.Monad.Except (MonadIO(liftIO), runExcept, runExceptT)
import           System.Exit (die)
-- import           Debug.Trace

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
      mapM_ processThyNew inFiles
      putStrLn ""
  | otherwise  = do
      _ <- ensureMaude as
      putStrLn ""
      summaries <- mapM processThyNew inFiles
      putStrLn ""
      putStrLn $ replicate 78 '='
      putStrLn "summary of summaries:"
      putStrLn ""
      putStrLn $ renderDoc $ Pretty.vcat $ intersperse (Pretty.text "") summaries
      putStrLn ""
      putStrLn $ replicate 78 '='
  where
    -- handles to arguments
    -----------------------
    inFiles    = reverse $ findArg "inFile" as

    thyLoadOptions = case (mkTheoryLoadOptions as) of
      Left (ArgumentError e) -> error e
      Right opts               -> opts

    -- output generation
    --------------------

    dryRun = not (argExists "outFile" as || argExists "outDir" as)

    mkOutPath :: FilePath  -- ^ Input file name.
              -> FilePath  -- ^ Output file name.
    mkOutPath inFile =
        fromMaybe (error "please specify an output file or directory") $
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
    processThyNew :: FilePath -> IO Pretty.Doc
    processThyNew inFile = either (die . show) return <=< runExceptT $ do
      srcThy <- liftIO $ readFile inFile
      res <- loadTheory thyLoadOptions srcThy inFile
      either (return . prettyOpenTheory) (return . prettyOpenDiffTheory) res

    processThy :: FilePath -> IO Pretty.Doc
    processThy inFile
      | argExists "parseOnly" as && argExists "diff" as =
          out (const Pretty.emptyDoc) (return . prettyOpenDiffTheory)   (loadOpenDiffThy thyLoadOptions inFile)
      | argExists "parseOnly" as || argExists "outModule" as =
          out (const Pretty.emptyDoc) choosePretty                      (loadOpenThy thyLoadOptions inFile)
      | argExists "diff" as =
          out ppWfAndSummaryDiff      (return . prettyClosedDiffTheory) (loadClosedDiffThy thyLoadOptions inFile)
      | otherwise = do
          (thy, report) <- loadClosedThyWf thyLoadOptions inFile
          out (ppWfAndSummary report) (return . prettyClosedTheory)     (return thy)
      where
        ppAnalyzed = Pretty.text $ "analyzed: " ++ inFile
        ppWfAndSummary report thy = do
            report
            Pretty.$--$ prettyClosedSummary thy

        ppWfAndSummaryDiff thy = do
            reportWellformednessDoc $ checkWellformednessDiff (openDiffTheory thy) (get diffThySignature thy)
            Pretty.$--$ prettyClosedDiffSummary thy

        choosePretty = case (get oOutputModule thyLoadOptions) of
          ModuleSpthy      -> return . prettyOpenTheory  <=< Sapic.warnings -- output as is, including SAPIC elements
          ModuleSpthyTyped -> return . prettyOpenTheory <=< Sapic.typeTheory <=< Sapic.warnings  -- additionally type
          ModuleMsr        -> return . prettyOpenTranslatedTheory
            <=< (return . (filterLemma $ lemmaSelector thyLoadOptions))
            <=< (return . removeTranslationItems)
            <=< Sapic.typeTheory
            <=< Sapic.warnings
          ModuleProVerif              -> Export.prettyProVerifTheory (lemmaSelector thyLoadOptions) <=< Sapic.typeTheoryEnv <=< Sapic.warnings
          ModuleProVerifEquivalence   -> Export.prettyProVerifEquivTheory <=< Sapic.typeTheoryEnv <=< Sapic.warnings
          ModuleDeepSec               -> Export.prettyDeepSecTheory <=< Sapic.typeTheory <=< Sapic.warnings

        out :: (a -> Pretty.Doc) -> (a -> IO Pretty.Doc) -> IO a -> IO Pretty.Doc
        out summaryDoc fullDoc load
          | dryRun    = do
              thy <- load
              doc <- fullDoc thy
              putStrLn $ renderDoc doc
              return $ ppAnalyzed Pretty.$--$ Pretty.nest 2 (summaryDoc thy)
          | otherwise = do
              putStrLn $ ""
              putStrLn $ "analyzing: " ++ inFile
              putStrLn $ ""
              let outFile = mkOutPath inFile
              (thySummary, t) <- timed $ do
                  thy <- load
                  doc <- fullDoc thy
                  writeFileWithDirs outFile $ renderDoc doc
                  -- ensure that the summary is in normal form
                  evaluate $ force $ summaryDoc thy
              let summary = Pretty.vcat
                    [ ppAnalyzed
                    , Pretty.text $ ""
                    , Pretty.text $ "  output:          " ++ outFile
                    , Pretty.text $ "  processing time: " ++ show t
                    , Pretty.text $ ""
                    , Pretty.nest 2 thySummary
                    ]
              putStrLn $ replicate 78 '-'
              putStrLn $ renderDoc summary
              putStrLn $ ""
              putStrLn $ replicate 78 '-'
              return summary

    {- TO BE REACTIVATED once infrastructure from interactive mode can be used

    -- static html generation
    -------------------------

    generateHtml :: FilePath      -- ^ Input file
                 -> ClosedTheory  -- ^ Theory to pretty print
                 -> IO ()
    generateHtml inFile thy = do
      cmdLine  <- getCommandLine
      time     <- getCurrentTime
      cpu      <- getCpuModel
      template <- getHtmlTemplate
      theoryToHtml $ GenerationInput {
          giHeader      = "Generated by " ++ htmlVersionStr
        , giTime        = time
        , giSystem      = cpu
        , giInputFile   = inFile
        , giTemplate    = template
        , giOutDir      = mkOutPath inFile
        , giTheory      = thy
        , giCmdLine     = cmdLine
        , giCompress    = not $ argExists "noCompress" as
        }

    -}
