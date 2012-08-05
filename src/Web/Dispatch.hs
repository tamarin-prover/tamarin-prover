{- |
Module      :  Web.Dispatch
Description :  Yesod dispatch functions and default handlers.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Maintainer  :  Cedric Staub <cstaub@ethz.ch>
Stability   :  experimental
Portability :  non-portable
-}

{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, TemplateHaskell, TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- FIXME: See how we can get rid of the Template Haskell induced warning, such
-- that we have the warning again for our code.
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

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
import           Yesod.Static

import qualified Control.Exception      as E
import qualified Data.Binary            as Bin
import qualified Data.ByteString        as B
import qualified Data.Map               as M
import qualified Data.Text              as T

import           Control.Applicative
import           Control.Concurrent
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.List
import           Data.Maybe
import           Data.Time.LocalTime

import           System.Directory
import           System.FilePath

-- | Create YesodDispatch instance for the interface.
-- mkYesodDispatch "WebUI" resourcesWebUI
mkYesodDispatch "WebUI" resourcesWebUI

-- | Static route for favicon file.
faviconRoute :: StaticRoute
faviconRoute = StaticRoute ["img", "favicon.ico"] []

-- | Favicon handler function (favicon.ico).
getFaviconR :: Handler ()
getFaviconR = redirect (StaticR faviconRoute)

-- | Robots file handler function (robots.txt).
getRobotsR :: Handler RepPlain
getRobotsR = return $ RepPlain $ toContent ("User-agent: *" :: B.ByteString)

-- | Initialization function for the web application.
withWebUI :: String                          -- ^ Message to output once the sever is ready.
          -> FilePath                        -- ^ Cache directory.
          -> FilePath                        -- ^ Working directory.
          -> Bool                            -- ^ Load last proof state if present
          -> Bool                            -- ^ Automatically save proof state
          -> (FilePath -> IO ClosedTheory)   -- ^ Theory loader (from file).
          -> (String -> IO (Either String ClosedTheory))
          -- ^ Theory loader (from string).
          -> (OpenTheory -> IO ClosedTheory) -- ^ Theory closer.
          -> Bool                            -- ^ Show debugging messages?
          -> FilePath                        -- ^ Path to static content directory
          -> FilePath                        -- ^ Path to dot binary
          -> ImageFormat                     -- ^ The preferred image format
          -> AutoProver                      -- ^ The default autoprover.
          -> (Application -> IO b)           -- ^ Function to execute
          -> IO b
withWebUI readyMsg cacheDir_ thDir loadState autosave thLoader thParser thCloser debug'
          stPath dotCmd' imgFormat' defaultAutoProver' f
  = do
    thy    <- getTheos
    thrVar <- newMVar M.empty
    thyVar <- newMVar thy
    st     <- static stPath
    when autosave $ createDirectoryIfMissing False autosaveDir
    -- Don't create parent dirs, as temp-dir should be created by OS.
    createDirectoryIfMissing False cacheDir_
    (`E.finally` shutdownThreads thrVar) $
      f =<< toWaiApp WebUI
        { workDir            = thDir
        , cacheDir           = cacheDir_
        , parseThy           = liftIO . thParser
        , closeThy           = thCloser
        , getStatic          = st
        , theoryVar          = thyVar
        , threadVar          = thrVar
        , autosaveProofstate = autosave
        , dotCmd             = dotCmd'
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

       else loadTheories readyMsg thDir thLoader defaultAutoProver'

    shutdownThreads thrVar = do
      m <- modifyMVar thrVar $ \m -> return (M.empty, m)
      putStrLn $ "Server shutdown: " ++ show (M.size m) ++ " threads still running"
      forM (M.toList m) $ \(str, tid) -> do
         putStrLn $ "killing: " ++ T.unpack str
         killThread tid


-- | Load theories from the current directory, generate map.
loadTheories :: String
             -> FilePath
             -> (FilePath -> IO ClosedTheory)
             -> AutoProver
             -> IO TheoryMap
loadTheories readyMsg thDir thLoader autoProver = do
    mkImageDir
    thPaths <- filter (".spthy" `isSuffixOf`) <$> getDirectoryContents thDir
    theories <- catMaybes <$> mapM loadThy (zip [1..] (map (thDir </>) thPaths))
    putStrLn readyMsg
    return $ M.fromList theories
  where
    -- Create image directory
    mkImageDir = do
      let dir = thDir </> imageDir
      existsDir <- doesDirectoryExist dir
      unless existsDir (createDirectory dir)

    -- Load theories
    loadThy (idx, path) = E.handle catchEx $ do
        thy <- thLoader path
        time <- getZonedTime
        return $ Just
          ( idx
          , TheoryInfo idx thy time Nothing True (Local path) autoProver
          )
      where
        -- Exception handler (if loading theory fails)
        catchEx :: E.SomeException -> IO (Maybe (TheoryIdx, TheoryInfo))
        catchEx e = do
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Unable to load theory file `" ++ path ++ "'"
          putStrLn $ replicate 78 '-'
          print e
          return Nothing
