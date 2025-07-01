{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module      :  Web.Dispatch
Description :  Yesod dispatch functions and default handlers.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}

module Web.Dispatch
  ( withWebUI
  , ImageFormat(..)
  )
where

import Web.Handler
import Web.Settings
import Web.Types

import Network.Wai
import Yesod.Core
import Yesod.Static qualified

import Control.Concurrent
import Control.Exception qualified as E
import Control.Monad
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Binary qualified as Bin
import Data.ByteString qualified as B
import Data.List
import Data.Map qualified as M
import Data.Maybe
import Data.Text qualified as T
import Data.Time.LocalTime

import System.Directory
import System.Exit
import System.FilePath
import Main.Console (renderDoc)
import Main.TheoryLoader (TheoryLoadError(ParserError, WarningError), TheoryLoadOptions(..))
import Theory
import Theory.Tools.Wellformedness
import Text.PrettyPrint.Class qualified as Pretty
import Text.PrettyPrint.Html

-- | Create YesodDispatch instance for the interface.
-- mkYesodDispatch "WebUIDiff" resourcesWebUI
mkYesodDispatch "WebUI" resourcesWebUI

-- | Static route for favicon file.
faviconRoute :: Yesod.Static.StaticRoute
faviconRoute = Yesod.Static.StaticRoute ["img", "favicon.ico"] []

-- | Favicon handler function (favicon.ico).
getFaviconR :: Handler ()
getFaviconR = redirect (StaticR faviconRoute)

-- | Robots file handler function (robots.txt).
getRobotsR :: Handler RepPlain
getRobotsR = pure $ RepPlain $ toContent ("User-agent: *" :: B.ByteString)

-- | NOTE (SM): See the note on 'staticFiles' below on how to enable dynamic
-- reloading.
staticFiles :: Yesod.Static.Static
staticFiles = $(Yesod.Static.embed "data")

-- | Initialization function for the web application.
withWebUI
  :: String                -- ^ Message to output once the sever is ready.
  -> FilePath              -- ^ Cache directory.
  -> FilePath              -- ^ Working directory.
  -> Bool                  -- ^ Enable server logging.
  -> Bool                  -- ^ Load last proof state if present
  -> Bool                  -- ^ Automatically save proof state
  -> TheoryLoadOptions     -- ^ Options for loading theories
  -> (String -> FilePath -> ExceptT TheoryLoadError IO (Either OpenTheory OpenDiffTheory))
  -- ^ Theory loader (from string).
  -> (SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> ExceptT TheoryLoadError IO (WfErrorReport, Either ClosedTheory ClosedDiffTheory))
  -- ^ Theory closer.
  -> Bool                  -- ^ Show debugging messages?
  -> OutputCommand         -- ^ Path to graph rendering binary (dot or json)
  -- ^ together with indication of choice "dot", "json", ...
  -> ImageFormat           -- ^ The preferred image format
  -> AutoProver            -- ^ The default autoprover.
  -> (Application -> IO b) -- ^ Function to execute
  -> IO b
withWebUI readyMsg cacheDir workDir enableLogging loadState autosave thyOpts
          loadThy closeThy debug outputCmd imageFormat defaultAutoProver f = do
  thy <- getTheos
  threadVar <- newMVar M.empty
  theoryVar <- newMVar thy
  -- NOTE (SM): uncomment this line to load the assets dynamically.
  -- staticFiles     <- Yesod.Static.static "data"
  when autosave $ createDirectoryIfMissing False autosaveDir
  -- Don't create parent dirs, as temp-dir should be created by OS.
  createDirectoryIfMissing False cacheDir
  (`E.finally` shutdownThreads threadVar) $
    f =<< app threadVar theoryVar
  where
    app threadVar theoryVar =
      let webUI = WebUI
                    { workDir
                    , cacheDir
                    , thyOpts
                    , loadThy
                    , closeThy
                    , getStatic = staticFiles
                    , theoryVar
                    , threadVar
                    , autosaveProofstate = autosave
                    , outputCmd
                    , imageFormat
                    , defaultAutoProver
                    , debug
                    }
      in if enableLogging then
        toWaiApp webUI
      else do
        plain <- toWaiAppPlain webUI
        pure $ defaultMiddlewaresNoLogging plain
    autosaveDir = workDir </> autosaveSubdir
    getTheos = do
      existsAutosave <- doesDirectoryExist autosaveDir
      if loadState && existsAutosave then do
        putStrLn "Using persistent server state ... server ready."
        files <- getDirectoryContents autosaveDir
        thys <- forM files $ \fn ->
          case break (`notElem` ['0'..'9']) fn of
            (idx,".img") -> do
              let file = workDir </> autosaveSubdir </> fn
              Just . (read idx,) <$> Bin.decodeFile file
            _            -> pure Nothing
        pure $ M.fromList $ catMaybes thys

      else loadTheories thyOpts readyMsg workDir loadThy closeThy defaultAutoProver

    shutdownThreads thrVar = do
      m <- modifyMVar thrVar $ \m -> pure (M.empty, m)
      putStrLn $ "Server shutdown: " ++ show (M.size m) ++ " threads still running"
      forM (M.toList m) $ \(str, tid) -> do
        putStrLn $ "killing: " ++ T.unpack str
        killThread tid

-- | Load theories from the current directory, generate map.
loadTheories
  :: TheoryLoadOptions
  -> String
  -> FilePath
  -> (String -> FilePath -> ExceptT TheoryLoadError IO (Either OpenTheory OpenDiffTheory))
  -> (SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> ExceptT TheoryLoadError IO (WfErrorReport, Either ClosedTheory ClosedDiffTheory))
  -> AutoProver
  -> IO TheoryMap
loadTheories thOpts readyMsg thDir thLoad thClose autoProver = do
  thPaths <- filter (\n -> any (`isSuffixOf` n) [".spthy", ".sapic"]) <$> getDirectoryContents thDir
  theories <- catMaybes <$> mapM loadThy (zip [1..] (map (thDir </>) thPaths))
  putStrLn readyMsg
  pure $ M.fromList theories
  where
    loadThy (idx, path) = do
      srcThy <- readFile path

      result <- runExceptT $ do
        openThy <- thLoad srcThy path
        let sig = either (._thySignature) (._diffThySignature) openThy
        sig' <- liftIO $ toSignatureWithMaude thOpts.maudePath sig
        thClose sig' openThy

      case result of
        Left (ParserError e) -> do
          putStrLn $ renderDoc $ reportFailure e path
          pure Nothing
        Left (WarningError report) -> do
          putStrLn $ renderDoc $ ppInteractive report path
          die "quit-on-warning mode selected - aborting on wellformedness errors."
        Right (report, thy) -> do
          time <- getZonedTime
          let wfErrors = if null report
                then ""
                else "<div class=\"wf-warning\">"
                     <> "\nWARNING: the following wellformedness checks failed!<br /><br />"
                     <> "\n" <> (renderHtmlDoc . htmlDoc $ prettyWfErrorReport report)
                     <> "\n</div>"
          unless (null report) $ putStrLn $ renderDoc $ ppInteractive report path
          let theoryInfo t = TheoryInfo idx t time Nothing True (Local path) autoProver wfErrors
          pure $ Just (idx, either (Trace . theoryInfo) (Diff . theoryInfo) thy)
      where
        reportFailure err inFile = Pretty.vcat $ Pretty.text <$>
          [ replicate 78 '-'
          , "Unable to load theory file `" ++ inFile ++ "'"
          , replicate 78 '-'
          , ""
          , show err
          , replicate 78 '-'
          , "" ]

        ppInteractive report inFile = Pretty.vcat
          [ Pretty.text $ replicate 78 '-'
          , Pretty.text $ "Theory file '" ++ inFile ++ "'"
          , Pretty.text $ replicate 78 '-'
          , Pretty.text ""
          , Pretty.text "WARNING: ignoring the following wellformedness errors"
          , Pretty.text ""
          , prettyWfErrorReport report
          , Pretty.text $ replicate 78 '-'
          , Pretty.text "" ]
