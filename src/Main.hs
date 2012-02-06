{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the tamarin prover.
module Main where

import           Prelude hiding (id, (.))

import Data.List
import Data.Maybe
import Data.Version (showVersion)
import Data.Monoid
import Data.Char (isSpace, toLower)
import Data.Label

import Control.Basics
import Control.Category
import Control.Exception as E

import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text

import System.Exit
import System.FilePath
import System.Directory
import System.Environment
import System.IO
import System.Process
import System.Timing (timed)

import Extension.Prelude

import qualified Text.Isar as Isar

import Theory
import Theory.Parser
import Theory.Wellformedness

import Paths_tamarin_prover

import Web.Dispatch
import qualified Web.Settings
import qualified Network.Wai.Handler.Warp as Warp (run)

------------------------------------------------------------------------------
-- General definitions for tamarin
------------------------------------------------------------------------------

-- | Program name
programName :: String
programName = "tamarin-prover"

-- | Version string
versionStr :: String
versionStr = unlines
  [ concat
    [ programName
    , " "
    , showVersion version
    , ", (C) Benedikt Schmidt, Simon Meier, ETH Zurich 2010-2012"
    ]
  , ""
  , "This program comes with ABSOLUTELY NO WARRANTY. It is free software, and you"
  , "are welcome to redistribute it according to its LICENCE."
  ]

-- | Line width to use.
lineWidth :: Int
lineWidth = 110

{-
-- | Version string with HTML markup.
htmlVersionStr :: String
htmlVersionStr = concat
    [ link "http://people.inf.ethz.ch/meiersi/espl" programName
    , " "
    , showVersion version
    , ", &copy; "
    , link "https://infsec.ethz.ch/infsec/people/benschmi/index" "Benedikt Schmidt"
    , ", "
    , link "http://people.inf.ethz.ch/meiersi" "Simon Meier"
    , ", ETH Zurich 2010-2012"
    ]
  where
    link href name = 
        "<a href=\"" ++ href ++ "\" target=\"new\">" ++ name ++ "</a>"
-}

------------------------------------------------------------------------------
-- Argument parsing helpers
------------------------------------------------------------------------------

type Arguments = [(String,String)]

argExists :: String -> Arguments -> Bool
argExists a = isJust . findArg a

findArg :: MonadPlus m => String -> Arguments -> m String
findArg a' as = msum [ return v | (a,v) <- as, a == a' ]

getArg :: String -> Arguments -> String
getArg a = 
  fromMaybe (error $ "getArg: argument '" ++ a ++ "' not found") . findArg a

addArg :: String -> String -> Arguments -> Arguments
addArg a v = ((a,v):)

withArguments :: Mode Arguments -> (Arguments -> IO ()) -> IO ()
withArguments argMode io = do
    processArgs argMode >>= run
  where
    run as
      | argExists "help"    as = print $ helpText HelpFormatAll argMode
      | argExists "version" as = putStrLn versionStr
      | otherwise              = io as

updateArg :: String -> String -> Arguments -> Either a Arguments
updateArg a v = Right . addArg a v

addEmptyArg :: String -> Arguments -> Arguments
addEmptyArg a = addArg a ""
    
-- | Main mode.
mainMode :: Mode [(String,String)]
mainMode = 
    -- translateMode { modeGroupModes = toGroup [interactiveMode] }
    translateMode { modeGroupModes = toGroup [intruderMode, interactiveMode] }
  where 

    defaultMode name help = Mode
        { modeGroupModes = toGroup []
        , modeNames      = [name] 
        , modeValue      = [] 
        , modeCheck      = updateArg "mode" name
        , modeReform     = const Nothing-- no reform possibility
        , modeHelp       = help
        , modeHelpSuffix = []
        , modeArgs       = Nothing    -- no positional arguments
        , modeGroupFlags = toGroup [] -- no flags
        }

    translateMode =
      ( defaultMode programName 
          "Parse, translate, and prove security protocols that use modular exponentation."
      )
      { modeCheck      = updateArg "mode" "translate"
      , modeArgs       = Just $ flagArg (updateArg "inFile") "FILES"
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
          , groupNamed =
              [ ("About"
                , [ flagHelpSimple (addEmptyArg "help")
                  , flagVersion (addEmptyArg "version")
                  ] )
              ]
          }
      }


    intruderMode =
      ( defaultMode "intruder" 
          "Compute the variants of the intruder rules for DH."
      )
      { modeArgs = Nothing 
      , modeCheck = updateArg "mode" "intruder"
      , modeGroupFlags = toGroup outputFlags
      }

    outputFlags = 
      [ flagOpt "" ["output","o"] (updateArg "outFile") "FILE" "Output file"
      , flagOpt "" ["Output","O"] (updateArg "outDir") "DIR"  "Output directory"
      ]

    toolFlags = 
      [ flagOpt "dot" ["with-dot"] (updateArg "withDot") "FILE" "Path to GraphViz 'dot' tool"
      , flagOpt "maude" ["with-maude"] (updateArg "withMaude") "FILE"  "Path to 'maude' rewriting tool"
      ]

    interactiveFlags =
      [ flagOpt "" ["port","p"] (updateArg "port") "PORT" "Port to listen on"
      , flagOpt "" ["datadir"]  (updateArg "datadir") "DATADIR" "Directory with data"
      , flagNone ["debug"] (addEmptyArg "debug") "Show server debugging output"
      , flagNone ["autosave"] (addEmptyArg "autosave") "Automatically save proof state"
      , flagNone ["loadstate"] (addEmptyArg "loadstate") "Load proof state if present"
      ] ++
      theoryLoadFlags

    interactiveMode =
      ( defaultMode "interactive"
          "Start a server and edit theories interactively."
      )
      { modeArgs = Just $ flagArg (updateArg "workDir") "WORKDIR"
      , modeCheck = updateArg "mode" "interactive"
      , modeGroupFlags = toGroup interactiveFlags
      }


-- | Disply help message and exit.
errHelpExit :: String -> IO ()
errHelpExit msg = do
  putStrLn $ "error: " ++ msg
  putStrLn $ ""
  putStrLn $ showText (Wrap lineWidth) 
           $ helpText HelpFormatDefault mainMode
  putStrLn $ ""
  examplePath <- getDataFileName "examples"
  putStrLn $ "for example protocol models see: " ++ examplePath
  exitFailure

------------------------------------------------------------------------------
-- Main mode execution
------------------------------------------------------------------------------

-- | Main function.
main :: IO ()
main = 
    withArguments mainMode selectMode
  where
    selectMode as = case findArg "mode" as of
        Just "translate"   -> translate as
        Just "intruder"    -> intruderVariants as
        Just "interactive" -> interactive as
        Just m           -> error $ "main: unknown mode '" ++ m ++ "'"
        Nothing          -> error $ "main: no mode given"
    
-- shared support functions
---------------------------

renderDoc :: Isar.Doc -> String
renderDoc = Isar.renderStyle (Isar.style { Isar.lineLength = lineWidth }) 


------------------------------------------------------------------------------
-- Intruder variants mode execution
------------------------------------------------------------------------------

intruderVariants :: Arguments -> IO ()
intruderVariants as = do
    ensureMaude as
    hnd <- startMaude (maudePath as) dhMaudeSig
    let thy       = dhIntruderTheory hnd
        thyString = renderDoc $ prettyOpenTheory thy
    putStrLn thyString
    writeThy thyString
  where
    -- output generation
    --------------------

    writeThy thyString = case optOutPath of
      Just outPath -> writeFile outPath thyString
      Nothing      -> return ()
    
    -- Output file name, if output is desired.
    optOutPath :: Maybe FilePath
    optOutPath = 
      do outFile <- findArg "outFile" as
         guard (outFile /= "")
         return outFile
      <|>
      do outDir <- findArg "outDir" as
         return $ outDir </> defaultIntrVariantsPath 

defaultIntrVariantsPath :: FilePath
defaultIntrVariantsPath = "intruder_variants_dh.spthy"


------------------------------------------------------------------------------
-- Theory loading: shared between interactive and batch mode
------------------------------------------------------------------------------
    
theoryLoadFlags :: [Flag Arguments]
theoryLoadFlags = 
  [ flagNone ["prove"] (addEmptyArg "addProofs")
      "Try to prove lemmas (implies --variants)"

  , flagOpt "dfs" ["stop-on-attack"] (updateArg "stopOnAttack") "DFS|BFS|NONE"
      "Method to stop proof search if an attack is found (default DFS)"

  , flagOpt "5" ["bound", "b"]   (updateArg "bound") "INT"
      "Bound the depth of the proofs"

  --, flagOpt "" ["intruder","i"] (updateArg "intruderVariants") "FILE"
  --    "Cached intruder rules to use"

  , flagOpt "" ["defines","D"] (updateArg "defines") "STRING"
      "Defined flags for pseudo-preprocessor."
  ]

loadOpenThy :: Arguments -> FilePath -> IO OpenTheory
loadOpenThy = fst . loadThy

loadClosedThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedThy = uncurry (>=>) . loadThy

loadClosedWfThy :: Arguments -> FilePath -> IO ClosedTheory
loadClosedWfThy as file = do
    thy <- loadOpen file
    case checkWellformedness thy of
      []     -> close thy
      report -> error $ renderDoc $ prettyWfErrorReport report
  where
    (loadOpen, close) = loadThy as

loadClosedThyString :: Arguments -> String -> IO ClosedTheory
loadClosedThyString = uncurry (>=>) . loadThyString

-- | Load an open/closed theory from a file.
loadThy :: Arguments -> (FilePath -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadThy as = loadGenericThy (parseOpenTheory (defines as)) as 

-- | Load an open/closed theory from a string.
loadThyString :: Arguments -> (String -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadThyString as = loadGenericThy loader as
  where
    loader str =
      case parseOpenTheoryString (defines as) str of
        Right thy -> return thy
        Left err -> error $ show err 

-- | The defined pre-processor flags in the argument.
defines :: Arguments -> [String]
defines = findArg "defines"

-- | Load an open/closed theory given a loader function.
loadGenericThy :: (a -> IO OpenTheory)
               -> Arguments 
               -> (a -> IO OpenTheory, OpenTheory -> IO ClosedTheory)
loadGenericThy loader as =
    (loader, (closeThy as) <=< tryAddIntrVariants)
  where
    -- intruder variants
    --------------------
    tryAddIntrVariants :: OpenTheory -> IO OpenTheory
    tryAddIntrVariants thy0 = do
      let msig = get (sigpMaudeSig . thySignature) thy0
          thy  = addIntrRuleACs (subtermIntruderRules msig ++ specialIntruderRules) thy0
      if (enableDH msig) then
         do variantsFile <- getDataFileName "intruder_variants_dh.spthy"
            ifM (doesFileExist variantsFile)
                (do intrVariants <- 
                        get thyCache <$> parseOpenTheory (defines as) variantsFile
                    return $ addIntrRuleACs intrVariants thy
                )
                (error $ "could not find intruder message deduction theory '" 
                           ++ variantsFile ++ "'")
         else return thy

-- | Close a theory according to arguments.
closeThy :: Arguments -> OpenTheory -> IO ClosedTheory
closeThy as = 
    fmap (proveTheory prover) . closeTheory (maudePath as) . wfCheck 
  where
    -- handles to relevant arguments
    --------------------------------
    proofBound      = read <$> findArg "bound" as
    requireProofs   = argExists "addProofs" as

    stopOnAttack :: Maybe String
    stopOnAttack = findArg "stopOnAttack" as

    -- wellformedness check
    -----------------------
    wfCheck :: OpenTheory -> OpenTheory
    wfCheck thy = 
      noteWellformedness
        (checkWellformedness thy) thy

    -- protocol transformation
    --------------------------
    prover :: Prover
    prover 
       | requireProofs = cutAttack $ maybe id boundProver proofBound autoProver
       | otherwise     = mempty
       where 
         cutAttack = mapProverProof $ case map toLower <$> stopOnAttack of
           Nothing     -> cutOnAttackDFS
           Just "dfs"  -> cutOnAttackDFS
           Just "none" -> id
           Just "bfs"  -> cutOnAttackBFS
           Just other  -> error $ "unknown stop-on-attack method: " ++ other
       
------------------------------------------------------------------------------
-- Tool paths (shared between interactive and batch mode)
------------------------------------------------------------------------------

-- | Path to maude tool
maudePath :: Arguments -> FilePath
maudePath = fromMaybe "maude" . findArg "withMaude"

-- | Path to dot tool
dotPath :: Arguments -> FilePath
dotPath = fromMaybe "dot" . findArg "withDot"

------------------------------------------------------------------------------
-- Interactive proof mode execution
------------------------------------------------------------------------------

-- | Prove lemmas interactively.
interactive :: Arguments -> IO ()
interactive as
  | null workDir = errHelpExit "no working directory specified"
  | otherwise    = do
      ensureGraphVizDot as
      ensureMaude as
      putStrLn ""
      port <- readPort
      dataDir <- readDataDir
      putStrLn $ intercalate "\n"
        [ "The server is running on localhost with port " ++ show port
        , "Browse to http://localhost:" ++ show port ++ " in order to begin." ]
      withWebUI (head workDir) (argExists "loadstate" as) (argExists "autosave" as)
        (loadClosedWfThy as) (loadClosedThyString as) (closeThy as)
        (argExists "debug" as) (Just dataDir) (Warp.run port)
  where
    -- Handles to arguments
    -----------------------
    workDir = findArg "workDir" as

    -- Datadir argument
    readDataDir =
      case findArg "datadir" as of
        [d] -> return d
        _   -> getDataDir

    -- Port argument
    ----------------
    readPort = do
      let port = findArg "port" as >>= fmap fst . listToMaybe . reads
      when
        (argExists "port" as && isNothing port) 
        (putStrLn $ "Unable to read port from argument `"
                    ++fromMaybe "" (findArg "port" as)++"'. Using default.")
      return $ fromMaybe Web.Settings.defaultPort port

------------------------------------------------------------------------------
-- Translate mode execution
------------------------------------------------------------------------------

-- | Execute a translation.
translate :: Arguments -> IO ()
translate as 
  | null inFiles = errHelpExit "no input files given"
  | otherwise    = do
      ensureMaude as
      putStrLn $ ""
      summaries <- mapM processThy inFiles
      putStrLn $ ""
      putStrLn $ replicate 78 '='
      putStrLn $ "summary of processed files:"
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
        out summaryDoc fullDoc load = do
          res <- try $
            if dryRun 
              then do writeWithSummary putStrLn "<no file written>"
              else do
                putStrLn $ ""
                putStrLn $ "analyzing: " ++ inFile
                putStrLn $ ""
                let outFile = mkOutPath inFile
                summary <- writeWithSummary (writeFile outFile) outFile
                putStrLn $ replicate 78 '-'
                putStrLn $ renderDoc summary
                putStrLn $ ""
                putStrLn $ replicate 78 '-'
                return summary
          case res of
            Right x -> return x
            Left x  -> return $ Isar.vcat $ map Isar.text
                [ "failed to analyze: " ++ inFile
                , ""
                , "  exception:       " ++ show (x :: IOException)
                ]
          where
            writeWithSummary :: (String -> IO ()) -> FilePath -> IO Isar.Doc
            writeWithSummary io outName = do
              (thySummary, t) <- timed $ do
                  thy <- load
                  io $ renderDoc $ fullDoc thy
                  return $ summaryDoc thy
              return $ Isar.vcat
                  [ Isar.text $ "analyzed: " ++ inFile
                  , Isar.text $ ""
                  , Isar.text $ "  output:          " ++ outName
                  , Isar.text $ "  processing time: " ++ show t
                  , Isar.text $ ""
                  , Isar.nest 2 thySummary
                  ]

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

------------------------------------------------------------------------------
-- Utility functions
------------------------------------------------------------------------------

-- | Get the string constituting the command line.
getCommandLine :: IO String
getCommandLine = do
  arguments <- getArgs
  return . concat . intersperse " " $ programName : arguments

-- | Read the cpu info using a call to cat /proc/cpuinfo
getCpuModel :: IO String
getCpuModel = 
  handle handler $ do
    (_, info, _) <- readProcessWithExitCode "cat" ["/proc/cpuinfo"] []
    return $ maybe errMsg
               (("Linux running on an "++) . drop 2 . dropWhile (/=':'))
               (find (isPrefixOf "model name") $ lines info)
  where
  errMsg = "could not extract CPU model"
  handler :: IOException -> IO String
  handler _ = return errMsg

-- | Get the path to the Html template file.
getHtmlTemplate :: IO FilePath
getHtmlTemplate = getDataFileName "HTML_TEMPLATE"


-- | Build the command line corresponding to a program arguments tuple.
commandLine :: String -> [String] -> String
commandLine prog args = concat $ intersperse " " $ prog : args

-- | Test if a process is executable and check its response. This is used to
-- determine the versions and capabilities of tools that we depend on.
testProcess :: (String -> String -> Either String String) 
                              -- ^ Analysis of stdout, stderr. Use 'Left' to report error.
            -> String         -- ^ Test description to display.
            -> FilePath       -- ^ Process to start
            -> [String]       -- ^ Arguments
            -> String         -- ^ Stdin
            -> IO Bool        -- ^ True, if test was successful
testProcess check testName prog args inp = do
    putStr testName
    hFlush stdout
    handle handler $ do
        (exitCode, out, err) <- readProcessWithExitCode prog args inp
        let errMsg reason = do
                putStrLn reason
                putStrLn $ " command: " ++ commandLine prog args
                putStrLn $ " stdin:   " ++ inp
                putStrLn $ " stdout:  " ++ out
                putStrLn $ " stderr:  " ++ err
                return False

        case exitCode of
            ExitFailure code -> errMsg $ "failed with exit code " ++ show code
            ExitSuccess      -> 
              case check out err of
                Left msg     -> errMsg msg
                Right msg    -> do putStrLn msg
                                   return True
  where
    handler :: IOException -> IO Bool
    handler _ = do putStrLn "caught exception while executing:"
                   putStrLn $ commandLine prog args
                   putStrLn $ "with input: " ++ inp
                   return False

-- | Ensure a suitable version of the Graphviz dot tool is installed.
ensureGraphVizDot :: Arguments -> IO ()
ensureGraphVizDot as = do
    putStrLn $ "GraphViz tool: '" ++ dot ++ "'"
    success <- testProcess check " checking version: " dot ["-V"] ""
    unless success $ putStrLn errMsg
  where
    dot = dotPath as
    check _ err
      | "graphviz" `isInfixOf` map toLower err = Right $ init err ++ ". OK."
      | otherwise                              = Left  $ errMsg
    errMsg = unlines
      [ "WARNING:"
      , ""
      , " The dot tool seems not to be provided by Graphviz."
      , " Graph generation might not work."
      , " Please download an official version from:"
      , "         http://www.graphviz.org/"
      ]

-- | Ensure a suitable version of Maude is installed.
ensureMaude :: Arguments -> IO ()
ensureMaude as = do
    putStrLn $ "maude tool: '" ++ maude ++ "'"
    success <- testProcess check " checking version: " maude ["--version"] ""
    unless success $ putStrLn $ errMsg "tool not found / does not work"
  where
    maude = maudePath as
    check out _ 
      | filter (not . isSpace) out == "2.6" = Right "2.6. OK."
      | otherwise                           = Left  $ errMsg $
          " 'maude --version' returned wrong verison '" ++ out ++ "'"

    errMsg reason = unlines
          [ "WARNING:"
          , ""
          , reason
          , " " ++ programName ++ " will likely not work."
          , " Please download 'Core Maude 2.6' from:"
          , "    http://maude.cs.uiuc.edu/download/"
          ]
