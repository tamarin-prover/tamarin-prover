{-# LANGUAGE DeriveDataTypeable #-}
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

import qualified Text.PrettyPrint.Class          as Pretty

import           Theory
import           Theory.Tools.Wellformedness     (checkWellformedness, checkWellformednessDiff)

import           Main.Console
import           Main.Environment
import           Main.TheoryLoader
import           Main.Utils

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
      ]

-- | Process a theory file.
run :: TamarinMode -> Arguments -> IO ()
run thisMode as
  | null inFiles = helpAndExit thisMode (Just "no input files given")
  | otherwise    = do
      _ <- ensureMaude as
      _ <- ensureSapic as
      putStrLn $ ""
      summaries <- mapM processThy $ inFiles
      putStrLn $ ""
      putStrLn $ replicate 78 '='
      putStrLn $ "summary of summaries:"
      putStrLn $ ""
      putStrLn $ renderDoc $ Pretty.vcat $ intersperse (Pretty.text "") summaries
      putStrLn $ ""
      putStrLn $ replicate 78 '='
  where
    -- handles to arguments
    -----------------------
    inFiles    = reverse $ findArg "inFile" as

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

    processThy :: FilePath -> IO (Pretty.Doc)
    processThy inFile
      -- | argExists "html" as =
      --     generateHtml inFile =<< loadClosedThy as inFile
      | (argExists "parseOnly" as) && (argExists "diff" as) =
          out (const Pretty.emptyDoc) prettyOpenDiffTheory   (loadOpenDiffThy   as inFile)
      | argExists "parseOnly" as =
          out (const Pretty.emptyDoc) prettyOpenTheory       (loadOpenThy       as inFile)
      | argExists "diff" as =
          out ppWfAndSummaryDiff      prettyClosedDiffTheory (loadClosedDiffThy as inFile)
      | otherwise        =
          out ppWfAndSummary          prettyClosedTheory     (loadClosedThy     as inFile)
      where
        ppAnalyzed = Pretty.text $ "analyzed: " ++ inFile

        ppWfAndSummary thy =
            case checkWellformedness (openTheory thy) of
                []   -> Pretty.emptyDoc
                errs -> Pretty.vcat $ map Pretty.text $
                          [ "WARNING: " ++ show (length errs)
                                        ++ " wellformedness check failed!"
                          , "         The analysis results might be wrong!" ]
            Pretty.$--$ prettyClosedSummary thy

        ppWfAndSummaryDiff thy =
            -- We need to remove the proto rule labels here to prevent false wellformedness errors
            case checkWellformednessDiff (removeProtoRuleLabels (openDiffTheory thy)) of
                []   -> Pretty.emptyDoc
                errs -> Pretty.vcat $ map Pretty.text $
                          [ "WARNING: " ++ show (length errs)
                                        ++ " wellformedness check failed!"
                          , "         The analysis results might be wrong!" ]
            Pretty.$--$ prettyClosedDiffSummary thy

        out :: (a -> Pretty.Doc) -> (a -> Pretty.Doc) -> IO a -> IO Pretty.Doc
        out summaryDoc fullDoc load
          | dryRun    = do
              thy <- load
              putStrLn $ renderDoc $ fullDoc thy
              return $ ppAnalyzed Pretty.$--$ Pretty.nest 2 (summaryDoc thy)
          | otherwise = do
              putStrLn $ ""
              putStrLn $ "analyzing: " ++ inFile
              putStrLn $ ""
              let outFile = mkOutPath inFile
              (thySummary, t) <- timed $ do
                  thy <- load
                  writeFileWithDirs outFile $ renderDoc $ fullDoc thy
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
