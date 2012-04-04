{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the tamarin prover.
module Main.Mode.Batch (
    batchMode
  ) where

import           Data.List
import           Data.Maybe
import           Control.Basics
import           System.Console.CmdArgs.Explicit as CmdArgs
import           System.FilePath
import           System.Timing (timed)

import qualified Text.Isar as Isar

import           Theory

import           Main.Utils
import           Main.Console
import           Main.Environment
import           Main.TheoryLoader


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
      putStrLn $ ""
      summaries <- mapM processThy $ inFiles
      putStrLn $ ""
      putStrLn $ replicate 78 '='
      putStrLn $ "summary of summaries:"
      putStrLn $ ""
      putStrLn $ renderDoc $ Isar.vcat $ intersperse (Isar.text "") summaries
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

    processThy :: FilePath -> IO (Isar.Doc)
    processThy inFile  
      -- | argExists "html" as = 
      --     generateHtml inFile =<< loadClosedThy as inFile
      | argExists "parseOnly" as =
          out (const Isar.emptyDoc) prettyOpenTheory   (loadOpenThy   as inFile)
      | otherwise        = 
          out prettyClosedSummary   prettyClosedTheory (loadClosedThy as inFile)
      where
        out :: (a -> Isar.Doc) -> (a -> Isar.Doc) -> IO a -> IO Isar.Doc
        out summaryDoc fullDoc load
          | dryRun    = do
              putStrLn =<< (renderDoc <$> fullDoc <$> load)
              return $ Isar.emptyDoc
          | otherwise = do
              putStrLn $ ""
              putStrLn $ "analyzing: " ++ inFile
              putStrLn $ ""
              let outFile = mkOutPath inFile
              (thySummary, t) <- timed $ do
                  thy <- load
                  writeFileWithDirs outFile $ renderDoc $ fullDoc thy
                  return $ summaryDoc thy
              let summary = Isar.vcat
                    [ Isar.text $ "analyzed: " ++ inFile
                    , Isar.text $ ""
                    , Isar.text $ "  output:          " ++ outFile
                    , Isar.text $ "  processing time: " ++ show t
                    , Isar.text $ ""
                    , Isar.nest 2 thySummary
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
