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
import Data.List
import Data.Maybe (isJust)
import System.Console.CmdArgs.Explicit as CmdArgs
import System.Exit (die)
import System.FilePath
import System.Timing (timedIO)
import Data.Bitraversable (Bitraversable(bitraverse))

import Text.PrettyPrint.Class qualified as Pretty
import Text.Printf (printf)

import Theory hiding (closeTheory)
import Theory.Module
import Theory.Tools.Wellformedness (prettyWfErrorReport)

import Main.Console
import Main.Environment
import Main.TheoryLoader
import Main.Utils
import Data.Map qualified as M
import Theory.Constraint.System.Dot
import Text.Dot qualified as D
import Theory.Constraint.System.Graph.Graph
import Theory.Constraint.System.JSON (sequentsToJSONPretty)

import ClosedTheory (prettyPrecomputation,prettyDiffPrecomputation)

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

              , flagNone ["precompute-only"] (addEmptyArg "precomputeOnly")
                  "Just run precomputation and show partial deconstructions"
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
      , flagOpt "spthy" ["output-module", "m"] (updateArg "outModule") moduleList moduleDescriptions
      , flagReq ["output-json","oj"] (updateArg "traceJSON") "FILE" "Serialize found traces as JSON to FILE."
      , flagReq ["output-dot","od"] (updateArg "traceDot") "FILE" "Serialize found traces as dot to FILE."
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
  | argExists "precomputeOnly" as = do
      versionData <- ensureMaudeAndGetVersion as
      res <- mapM (processThy versionData) inFiles
      let (docs, _) = unzip res
      mapM_ (putStrLn . renderDoc) docs
  | argExists "outModule" as = do
      versionData <- ensureMaudeAndGetVersion as
      res <- mapM (processThy versionData) inFiles
      let (docs, _) = unzip res

      if writeOutput then do
        let maybeOutFiles = mapM mkOutPath inFiles
        outFiles <- case maybeOutFiles of
          Just f -> pure f
          Nothing -> die "Please specify a valid output file/directory"
        mapM_ (\(o, d) -> writeFileWithDirs o (renderDoc d)) (zip outFiles docs)
      else do
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
      sig'   <- liftIO $ toSignatureWithMaude thyLoadOptions.maudePath sig

      -- | Pretty print the theory as is without performing any checks.
      if thyLoadOptions.parseOnlyMode then
        pure $ (, Pretty.emptyDoc) $ either prettyOpenTheory prettyOpenDiffTheory thy

      -- | Execute precomputation steps and print the partial deconstructions
      else if thyLoadOptions.precomputeOnlyMode then do
        (report, thy') <- closeTheory versionData thyLoadOptions sig' thy
        case thy' of
          Left thy'' -> do
            pure (ppWf report Pretty.$--$ prettyPrecomputation thy'', ppWf report)
          Right thy'' -> do
            pure (ppWf report Pretty.$--$ prettyDiffPrecomputation thy'', ppWf report)
    
      -- | Translate and check thoery based on specified output module.
      else if isTranslateOnlyMode then do
        (report, thy') <- translateAndCheckTheory versionData thyLoadOptions sig' thy

        -- comment: Not sure why this was needed. It just duplicates all comments in the theory.
        -- let thy'' = bimap (modify thyItems (++ (TextItem <$> formalComments thy')))
        --                   (modify diffThyItems (++ (DiffTextItem <$> formalComments thy')))
        --                   thy'

        (, ppWf report) <$> either (liftIO . prettyOpenTheoryByModule thyLoadOptions)
                                   (pure . prettyOpenDiffTheory)
                                   thy'

      -- | Close and potentially prove theory.
      else do
        (report, thy') <- closeTheory versionData thyLoadOptions sig' thy
        _ <- liftIO $ bitraverse outputTraces (const $ return ()) thy'

        pure $
          either (\t -> (prettyClosedTheory t,     ppWf report Pretty.$--$ prettyClosedSummary t))
                 (\d -> (prettyClosedDiffTheory d, ppWf report Pretty.$--$ prettyClosedDiffSummary d))
                 thy'
      where
        isTranslateOnlyMode = isJust thyLoadOptions.outputModule

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
          : [ Pretty.text   "         The analysis results might be wrong!" | thyLoadOptions.proveMode ]

        -- | Output any found traces of the analyzed theory in dot/JSON format if the corresponing command line option is set.
        -- The output is dumped into a single file per format. Multiple dot graphs are simply concatenated into a single file,
        -- while the JSON schema already allows for multiple graphs.
        outputTraces :: ClosedTheory -> IO ()
        outputTraces thy = do
            let graphOptions = defaultGraphOptions
                dotOptions = defaultDotOptions
                serializeDot (label, system) = D.showDot label $ dotSystemCompact graphOptions dotOptions system
                serializeJSON = sequentsToJSONPretty graphOptions
                labelledSystems = map (\(lemma, proof, system) ->
                  let label = traceOutputLabel graphOptions dotOptions lemma proof in
                  (label, system)) systemsWithMetadata

            case findArg "traceDot" as of
              Nothing -> pure ()
              Just outfile ->
                let serialized = intercalate "\n" $ map serializeDot labelledSystems in
                writeFile outfile serialized

            case findArg "traceJSON" as of
              Nothing -> pure ()
              Just outfile ->
                let serialized = serializeJSON labelledSystems in
                writeFile outfile serialized
          where
            -- | Collect all solved (i.e. a trace was found) systems of the theory along with their
            -- path in the proof and the lemma in which they appear in the given theory.
            systemsWithMetadata :: [(Lemma IncrementalProof, ProofPath, System)]
            systemsWithMetadata = do
              lemma <- getLemmas thy
              let proof = lemma._lProof
              [(lemma, proofPath, system) | (proofPath, system) <- proofSystems proof]

            -- | Collect all solved (i.e. a trace was found) systems of the theory along with their
            -- path in the proof.
            proofSystems :: IncrementalProof -> [(ProofPath, System)]
            proofSystems (LNode (ProofStep (Finished Solved) (Just rootSystem)) _) =  [([], rootSystem)]
            proofSystems (LNode (ProofStep _ _) children) =  
              [(l : ls, system) | (l, subProof) <- M.toList children 
                                , (ls, system) <- proofSystems subProof ]

            -- | Make a label for use in the trace output out of all relevant information for a constraint system.
            traceOutputLabel :: GraphOptions
                             -> DotOptions
                             -> Lemma IncrementalProof
                             -> ProofPath
                             -> String
            traceOutputLabel graphOptions dotOptions lemma proofPath =
              "trace_"
              ++ thy._thyName                              -- Name of the theory in which the constraint system appears.
              ++ "_"
              ++ traceLabelOptions graphOptions dotOptions -- Graph options are included in a short format.
              ++ "_"
              ++ lemma._lName                              -- Name of the lemma in which the constraint system appears.
              ++ intercalate "-" proofPath                 -- Path through the proof where the constraint system is located.

            -- | Format the graph rendering options in a concise way.
            traceLabelOptions :: GraphOptions -> DotOptions -> String
            traceLabelOptions graphOptions dotOptions =
              let s1 = show graphOptions._goSimplificationLevel
                  s2 = if graphOptions._goShowAutoSource then "AS1" else "AS0"
                  s3 = if graphOptions._goClustering then "CL1" else "CL0"
                  s4 = if graphOptions._goAbbreviate then "A1" else "A0"
                  s5 = if graphOptions._goCompress then "C1" else "C0"
                  s6 = case dotOptions._doNodeStyle of
                         FullBoringNodes -> "NF"
                         CompactBoringNodes -> "NB"
              in
                intercalate "-" [s1, s2, s3, s4, s5, s6]
