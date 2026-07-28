-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Main module for the Tamarin prover.
module Main.Mode.Interactive (
    interactiveMode
  ) where

import Control.Basics
import Control.Exception (IOException, handle)
import Data.Aeson (eitherDecode)
import Data.ByteString.Lazy qualified as BSL
import Data.Char (toLower)
import Data.List
import Data.Maybe
import Data.String (fromString)
import System.Console.CmdArgs.Explicit as CmdArgs
import System.Directory (doesDirectoryExist, doesFileExist, getTemporaryDirectory)
import System.Environment (lookupEnv)
import System.FilePath

import Network.Wai.Handler.Warp (defaultSettings, setHost, setPort)
import Network.Wai.Handler.Warp qualified as Warp
import Web.Dispatch
import Web.Settings qualified
import Web.Types (JSONGraphs, OutputCommand(..), OutputFormat(..))

import Main.Console
import Main.Environment
import Main.TheoryLoader


------------------------------------------------------------------------------
-- Run
------------------------------------------------------------------------------

-- | Batch processing mode.
interactiveMode :: TamarinMode
interactiveMode = tamarinMode
  "interactive"
  "Start a web-server to construct proofs interactively."
  setupFlags
  run
  where
    setupFlags defaultMode = defaultMode
      { modeArgs       = ([], Just $ flagArg (updateArg "workDir") "WORKDIR")
      , modeCheck      = updateArg "mode" "interactive"
      , modeGroupFlags = Group interactiveFlags [] [("About", [helpFlag])]
      }

    interactiveFlags =
      [ flagOpt "" ["port","p"] (updateArg "port") "PORT" "Port to listen on"
      , flagOpt "" ["interface","i"] (updateArg "interface") "INTERFACE"
                "Interface to listen on (use '*4' for all IPv4 interfaces)"
      , flagOpt "" ["image-format"] (updateArg "image-format") "PNG|SVG" "image format used for graphs (default SVG)"
      , flagOpt "" ["load-json"] (updateArg "load-json") "FILE"
                "Load a JSON graph file (see --output-json) for standalone viewing at /loadjson (WORKDIR may be omitted)"
      , flagNone ["debug"] (addEmptyArg "debug") "Show server debugging output"
      , flagNone ["no-logging"] (addEmptyArg "no-logging") "Suppress web server logs."
      -- , flagNone ["autosave"] (addEmptyArg "autosave") "Automatically save proof state"
      -- , flagNone ["loadstate"] (addEmptyArg "loadstate") "Load proof state if present"
      ] ++
      theoryLoadFlags ++
      toolFlags



-- | Start the interactive theorem proving mode.
run :: TamarinMode -> Arguments -> IO ()
run thisMode as = case findArg "workDir" as <|> (takeDirectory <$> findArg "load-json" as) of
  -- WORKDIR may be omitted when --load-json is given: the JSON file's own
  -- directory is used instead, since there is then usually no theory to load.
  Nothing -> helpAndExit thisMode (Just "no working directory specified")
  Just workDir0 -> do
    -- determine working directory
    wdIsFile <- doesFileExist workDir0
    let workDir | wdIsFile  = takeDirectory workDir0
                | otherwise = workDir0
        -- Passing a FILENAME.json positional argument is equivalent to
        -- passing it as --load-json=FILENAME.json.
        isJsonArg = wdIsFile && map toLower (takeExtension workDir0) == ".json"
        loadJsonFileArg = findArg "load-json" as <|> (if isJsonArg then Just workDir0 else Nothing)
    wdIsDir  <- doesDirectoryExist workDir
    if wdIsDir then do
      -- determine caching directory
      tempDir <- getTemporaryDirectory
      winLoginName <- lookupEnv "USERNAME"
      unixLoginName <- lookupEnv "USER"
      let loginName = fromMaybe "" (winLoginName <|> unixLoginName)
          cacheDir = tempDir </> ("tamarin-prover-cache-" ++ loginName)

      -- Load and parse an externally exported JSON graph file, if requested.
      loadedJsonGraphs <- readLoadJsonFileArg loadJsonFileArg

      -- Ensure Maude and get the Version in the arguments (__versionPrettyPrint__)
      version <- ensureMaudeAndGetVersion as

      -- process theories
      _ <- case (readOutputCommand as).ocFormat of
          OutDot  -> ensureGraphVizDot as
          OutJSON -> ensureGraphCommand as

      port <- readPort
      let webUrl = serverUrl port
          -- When viewing an externally loaded JSON file, point the user
          -- directly at /loadjson instead of reporting both the plain
          -- server URL and the /loadjson URL separately.
          readyUrl = maybe webUrl (const $ webUrl ++ "/loadjson") loadedJsonGraphs
      putStrLn $ intercalate "\n"
        [ "The server is starting up on port " ++ show port ++ "."
        , "Browse to " ++ readyUrl ++ " once the server is ready."
        , ""
        , "Loading the security protocol theories '" ++ workDir </> "*.spthy"  ++ "' ..."
        , ""
        ]

      withWebUI
        ("Finished loading theories ... server ready at \n\n    " ++ readyUrl ++ "\n")
        cacheDir
        workDir

        enableLogging
        (argExists "loadstate" as)
        (argExists "autosave" as)

        thyLoadOptions

        (loadTheory thyLoadOptions)
        (closeTheory version thyLoadOptions)

        (argExists "debug" as) (readOutputCommand as) readImageFormat
        (constructAutoProver thyLoadOptions)
        loadedJsonGraphs
        (runWarp port)

    else
      helpAndExit thisMode
        (Just $ "directory '" ++ workDir ++ "' does not exist.")
  where
    enableLogging = not $ argExists "no-logging" as

    thyLoadOptions = case mkTheoryLoadOptions as of
      Left (ArgumentError e) -> error e
      Right opts             -> opts

    -- Load and parse an externally exported JSON graph file (--load-json).
    -----------------------------------------------------------------------
    readLoadJsonFileArg :: Maybe FilePath -> IO (Maybe JSONGraphs)
    readLoadJsonFileArg Nothing = pure Nothing
    readLoadJsonFileArg (Just jsonFile) = do
      exists <- doesFileExist jsonFile
      unless exists $ error $
        "--load-json: file '" ++ jsonFile ++ "' does not exist."
      contents <- BSL.readFile jsonFile
      case eitherDecode contents of
        Left decodeErr -> error $ "--load-json: failed to parse '" ++ jsonFile ++ "': " ++ decodeErr
        Right jgs -> pure $ Just jgs

    -- Port argument
    ----------------
    readPort = do
      let port = findArg "port" as >>= fmap fst . listToMaybe . reads
      when
        (argExists "port" as && isNothing port)
        (putStrLn $ "Unable to read port from argument `"
                    ++ fromMaybe "" (findArg "port" as) ++ "'. Using default.")
      pure $ fromMaybe Web.Settings.defaultPort port

    -- Interface argument, we use 127.0.0.1 as default
    --------------------------------------------------
    interface = fromMaybe "127.0.0.1" $ findArg "interface" as

    readImageFormat =
      case map toLower <$> findArg "image-format" as of
        Just "svg" -> SVG
        Just "png" -> PNG
        Nothing    -> SVG
        Just _     -> error "image-format must be one of PNG|SVG"

    serverUrl port = "http://" ++ address ++ ":" ++ show port
      where
        address | interface `elem` ["*","*4","*6"] = "127.0.0.1"
                | otherwise                        = interface

    runWarp port wapp =
      handle (\e -> err (e::IOException)) $
        Warp.runSettings
          (setHost (fromString interface) $ setPort port defaultSettings)
          wapp

    err e = error $
      "Starting the webserver on "++interface++" failed: \n"
      ++ show e
      ++ "\nNote that you can use '--interface=\"*4\"' for binding to all interfaces."
