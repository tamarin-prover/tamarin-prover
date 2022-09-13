{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ViewPatterns          #-}

-- FIXME: See how we can get rid of the Template Haskell induced warning, such
-- that we have the warning again for our code.
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module      :  Web.Dispatch
Description :  Yesod dispatch functions and default handlers.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Maintainer  :  Cedric Staub <cstaub@ethz.ch>
Stability   :  experimental
Portability :  non-portable
-}

module Web.Dispatch
  ( withWebUI
  , ImageFormat(..)
  )
where

import           Theory
import           Web.Handler
import           Web.Settings
import           Web.Types

import           Network.Wai
import           Yesod.Core
import qualified Yesod.Static

import qualified Control.Exception      as E
import qualified Data.Binary            as Bin
import qualified Data.ByteString        as B
import qualified Data.Map               as M
import qualified Data.Text              as T

-- import           Control.Applicative
import           Control.Concurrent
import           Control.Monad
import           Data.List
import           Data.Maybe
import           Data.Time.LocalTime

import           System.Directory
import           System.FilePath
import Control.Monad.Except (ExceptT, runExceptT)
import Main.TheoryLoader (TheoryLoadError (ParserError, WarningError), TheoryLoadOptions, oMaudePath)
import Theory.Tools.Wellformedness
import qualified Data.Label as L
import Main.Console (renderDoc)
import qualified Text.PrettyPrint.Class          as Pretty
import System.Exit
-- import           System.Process

-- | Create YesodDispatch instance for the interface.
-- mkYesodDispatch "WebUIDiff" resourcesWebUI
mkYesodDispatch "WebUI"     resourcesWebUI

-- | Static route for favicon file.
faviconRoute :: Yesod.Static.StaticRoute
faviconRoute = Yesod.Static.StaticRoute ["img", "favicon.ico"] []

-- | Favicon handler function (favicon.ico).
getFaviconR :: Handler ()
getFaviconR = redirect (StaticR faviconRoute)

-- | Robots file handler function (robots.txt).
getRobotsR :: Handler RepPlain
getRobotsR = return $ RepPlain $ toContent ("User-agent: *" :: B.ByteString)

-- | NOTE (SM): See the note on 'staticFiles' below on how to enable dynamic
-- reloading.
staticFiles :: Yesod.Static.Static
staticFiles = $(Yesod.Static.embed "data")

-- | Initialization function for the web application.
withWebUI :: String                          -- ^ Message to output once the sever is ready.
          -> FilePath                        -- ^ Cache directory.
          -> FilePath                        -- ^ Working directory.
          -> Bool                            -- ^ Load last proof state if present
          -> Bool                            -- ^ Automatically save proof state
          -> TheoryLoadOptions               -- ^ Options for loading theories
          -> (String -> FilePath -> ExceptT TheoryLoadError IO (Either OpenTheory OpenDiffTheory))  
          -- ^ Theory loader (from string).
          -> (SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> ExceptT TheoryLoadError IO (WfErrorReport, Either ClosedTheory ClosedDiffTheory))
          -- ^ Theory closer.
          -> Bool                            -- ^ Show debugging messages?
          -> (String, FilePath)              -- ^ Path to graph rendering binary (dot or json)
                                             -- ^ together with indication of choice "dot", "json", ...
          -> ImageFormat                     -- ^ The preferred image format
          -> AutoProver                      -- ^ The default autoprover.
          -> (Application -> IO b)           -- ^ Function to execute
          -> IO b
withWebUI readyMsg cacheDir_ thDir loadState autosave thOpts thLoad thClose debug'
          graphCmd' imgFormat' defaultAutoProver' f
  = do
    thy    <- getTheos
    thrVar <- newMVar M.empty
    thyVar <- newMVar thy
    -- NOTE (SM): uncomment this line to load the assets dynamically.
    -- staticFiles     <- Yesod.Static.static "data"
    when autosave $ createDirectoryIfMissing False autosaveDir
    -- Don't create parent dirs, as temp-dir should be created by OS.
    createDirectoryIfMissing False cacheDir_
    (`E.finally` shutdownThreads thrVar) $
      f =<< toWaiApp WebUI
        { workDir            = thDir
        , cacheDir           = cacheDir_
        , thyOpts            = thOpts
        , loadThy            = thLoad
        , closeThy           = thClose
        , getStatic          = staticFiles
        , theoryVar          = thyVar
        , threadVar          = thrVar
        , autosaveProofstate = autosave
        , graphCmd           = graphCmd'
        , imageFormat        = imgFormat'
        , defaultAutoProver  = defaultAutoProver'
        , debug              = debug'
        }
  where
    autosaveDir = thDir++"/"++autosaveSubdir
    getTheos = do
      existsAutosave <- doesDirectoryExist autosaveDir
      if loadState && existsAutosave
       then do
         putStrLn "Using persistent server state ... server ready."
         files <- getDirectoryContents autosaveDir
         thys <- (`mapM` files) $ \fn ->
                   case break (`notElem` ['0'..'9']) fn of
                     (idx,".img") -> do
                       let file = thDir++"/"++autosaveSubdir++fn
                       Just . (read idx,) <$> Bin.decodeFile file
                     _            -> return Nothing
         return $ M.fromList $ catMaybes thys

       else loadTheories thOpts readyMsg thDir thLoad thClose defaultAutoProver' 

    shutdownThreads thrVar = do
      m <- modifyMVar thrVar $ \m -> return (M.empty, m)
      putStrLn $ "Server shutdown: " ++ show (M.size m) ++ " threads still running"
      forM (M.toList m) $ \(str, tid) -> do
         putStrLn $ "killing: " ++ T.unpack str
         killThread tid

-- | Load theories from the current directory, generate map.
loadTheories :: TheoryLoadOptions
             -> String
             -> FilePath
             -> (String -> FilePath -> ExceptT TheoryLoadError IO (Either OpenTheory OpenDiffTheory))
             -> (SignatureWithMaude -> Either OpenTheory OpenDiffTheory -> ExceptT TheoryLoadError IO (WfErrorReport, Either ClosedTheory ClosedDiffTheory))
             -> AutoProver
             -> IO TheoryMap
loadTheories thOpts readyMsg thDir thLoad thClose autoProver = do
    thPaths <- filter (\n -> (".spthy" `isSuffixOf` n) || (".sapic" `isSuffixOf` n)) <$> getDirectoryContents thDir
    theories <- catMaybes <$> mapM loadThy (zip [1..] (map (thDir </>) thPaths))
    putStrLn readyMsg
    return $ M.fromList theories
  where
    loadThy (idx, path) = do
      srcThy <- readFile path

      result <- runExceptT $ do
        openThy <- thLoad srcThy path
        let sig = either (L.get thySignature) (L.get diffThySignature) openThy
        sig' <- liftIO $ toSignatureWithMaude (L.get oMaudePath thOpts) sig
        thClose sig' openThy

      case result of
        Left (ParserError e) -> do
          putStrLn $ renderDoc $ reportFailure e path
          return Nothing
        Left (WarningError report) -> do
          putStrLn $ renderDoc $ ppInteractive report path
          die "quit-on-warning mode selected - aborting on wellformedness errors."
        Right (report, thy) -> do
          time <- getZonedTime
          unless (null report) $ putStrLn $ renderDoc $ ppInteractive report path
          return $ Just
             ( idx
             , either (\t -> Trace $ TheoryInfo idx t time Nothing True (Local path) autoProver)
                      (\t -> Diff $ DiffTheoryInfo idx t time Nothing True (Local path) autoProver) thy
             )
      where
        reportFailure error inFile = Pretty.vcat [ Pretty.text $ replicate 78 '-'
                                                 , Pretty.text $ "Unable to load theory file `" ++ inFile ++ "'"
                                                 , Pretty.text $ replicate 78 '-'
                                                 , Pretty.text $ ""
                                                 , Pretty.text $ show error
                                                 , Pretty.text $ replicate 78 '-'
                                                 , Pretty.text $ "" ]

        ppInteractive report inFile = Pretty.vcat [ Pretty.text $ replicate 78 '-'
                                                  , Pretty.text $ "Theory file '" ++ inFile ++ "'"
                                                  , Pretty.text $ replicate 78 '-'
                                                  , Pretty.text $ ""
                                                  , Pretty.text $ "WARNING: ignoring the following wellformedness errors"
                                                  , Pretty.text $ ""
                                                  , prettyWfErrorReport report
                                                  , Pretty.text $ replicate 78 '-'
                                                  , Pretty.text $ "" ]