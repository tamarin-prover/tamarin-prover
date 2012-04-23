{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the Tamarin prover.
module Main.Mode.Interactive (
    interactiveMode
  ) where

import           Data.List
import           Data.Maybe
import           Control.Basics
import           System.Console.CmdArgs.Explicit as CmdArgs
import           System.FilePath
import           System.Directory (doesFileExist, doesDirectoryExist)

import           Web.Dispatch
import qualified Web.Settings
import qualified Network.Wai.Handler.Warp as Warp
import           Network.Wai.Handler.Warp (defaultSettings, settingsHost
                                          , settingsPort, HostPreference(Host))

import           Main.Console
import           Main.Environment
import           Main.TheoryLoader

import           Paths_tamarin_prover (getDataDir)


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
      -- , flagOpt "" ["datadir"]  (updateArg "datadir") "DATADIR" "Directory with data"
      , flagNone ["debug"] (addEmptyArg "debug") "Show server debugging output"
      -- , flagNone ["autosave"] (addEmptyArg "autosave") "Automatically save proof state"
      -- , flagNone ["loadstate"] (addEmptyArg "loadstate") "Load proof state if present"
      ] ++
      theoryLoadFlags ++
      toolFlags

 

-- | Start the interactive theorem proving mode.
run :: TamarinMode -> Arguments -> IO ()
run thisMode as = case findArg "workDir" as of
    Nothing       -> helpAndExit thisMode
                       (Just "no working directory specified")
    Just workDir0 -> do
      -- determine working directory
      wdIsFile <- doesFileExist workDir0
      let workDir | wdIsFile  = takeDirectory workDir0
                  | otherwise = workDir0
      wdIsDir  <- doesDirectoryExist workDir
      if wdIsDir
        then do
          -- process theories
          _ <- ensureGraphVizDot as
          _ <- ensureMaude as
          putStrLn ""
          port <- readPort
          dataDir <- readDataDir
          let serverUrl = "http://localhost:" ++ show port 
          putStrLn $ intercalate "\n"
            [ "The server is starting up on localhost with port " ++ show port ++ "."
            , "Browse to " ++ serverUrl ++ " once the server is ready."
            , ""
            , "Loading the security protocol theories '" ++ workDir </> "*.spthy"  ++ "' ..."
            ]
          withWebUI 
            ("Finished loading theories ... server ready at \n\n    " ++ serverUrl ++ "\n")
            workDir (argExists "loadstate" as) (argExists "autosave" as)
            (loadClosedWfThy as) (loadClosedThyString as) (closeThy as)
            (argExists "debug" as) dataDir
            (Warp.runSettings
                 (defaultSettings { settingsHost = Host "127.0.0.1",
                                    settingsPort = port}))
        else 
          helpAndExit thisMode
            (Just $ "directory '" ++ workDir ++ "' does not exist.")
  where
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
