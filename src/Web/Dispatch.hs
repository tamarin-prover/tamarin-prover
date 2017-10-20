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
  , withWebUIDiff
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
import           System.Process

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
          -> (FilePath -> IO ClosedTheory)   -- ^ Theory loader (from file).
          -> (String -> IO (Either String ClosedTheory))
          -- ^ Theory loader (from string).
          -> (String -> IO String)           -- ^ Report on wellformedness.
          -- -> (OpenTheory -> IO ClosedTheory) -- ^ Theory closer.
          -> Bool                            -- ^ Show debugging messages?
          -> (String, FilePath)              -- ^ Path to graph rendering binary (dot or json)
                                             -- ^ together with indication of choice "dot", "json", ...
          -> ImageFormat                     -- ^ The preferred image format
          -> AutoProver                      -- ^ The default autoprover.
          -> (Application -> IO b)           -- ^ Function to execute
          -> Bool
          -> IO b
withWebUI readyMsg cacheDir_ thDir loadState autosave thLoader thParser thWellformed debug'
          graphCmd' imgFormat' defaultAutoProver' f sapic
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
        , diffParseThy       = error "not in diff mode!"
        , parseThy           = liftIO . thParser
        , thyWf              = liftIO . thWellformed
        , getStatic          = staticFiles
        , theoryVar          = thyVar
        , threadVar          = thrVar
        , autosaveProofstate = autosave
        , graphCmd           = graphCmd'
        , imageFormat        = imgFormat'
        , defaultAutoProver  = defaultAutoProver'
        , debug              = debug'
        , isDiffTheory       = False
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

       else loadTheories readyMsg thDir thLoader defaultAutoProver' sapic

    shutdownThreads thrVar = do
      m <- modifyMVar thrVar $ \m -> return (M.empty, m)
      putStrLn $ "Server shutdown: " ++ show (M.size m) ++ " threads still running"
      forM (M.toList m) $ \(str, tid) -> do
         putStrLn $ "killing: " ++ T.unpack str
         killThread tid

-- | Initialization function for the web application.
withWebUIDiff :: String                      -- ^ Message to output once the sever is ready.
          -> FilePath                        -- ^ Cache directory.
          -> FilePath                        -- ^ Working directory.
          -> Bool                            -- ^ Load last proof state if present
          -> Bool                            -- ^ Automatically save proof state
          -> (FilePath -> IO ClosedDiffTheory)   -- ^ Theory loader (from file).
          -> (String -> IO (Either String ClosedDiffTheory))
          -- ^ Theory loader (from string).
          -> (String -> IO String)           -- ^ Report on wellformedness.
          -- -> (OpenTheory -> IO ClosedTheory) -- ^ Theory closer.
          -> Bool                            -- ^ Show debugging messages?
          -> FilePath                        -- ^ Path to dot binary
          -> ImageFormat                     -- ^ The preferred image format
          -> AutoProver                      -- ^ The default autoprover.
          -> (Application -> IO b)           -- ^ Function to execute
          -> IO b
withWebUIDiff readyMsg cacheDir_ thDir loadState autosave thLoader thParser thWellformed debug'
          dotCmd' imgFormat' defaultAutoProver' f
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
        , parseThy           = error "in diff mode!"
        , diffParseThy       = liftIO . thParser
        , thyWf              = liftIO . thWellformed
        , getStatic          = staticFiles
        , theoryVar          = thyVar
        , threadVar          = thrVar
        , autosaveProofstate = autosave
        , graphCmd           = ("dot",dotCmd')
        , imageFormat        = imgFormat'
        , defaultAutoProver  = defaultAutoProver'
        , debug              = debug'
        , isDiffTheory       = True
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

       else loadDiffTheories readyMsg thDir thLoader defaultAutoProver'

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
             -> Bool
             -> IO TheoryMap
loadTheories readyMsg thDir thLoader autoProver sapic = do
    sapicPaths <- filter (".sapic" `isSuffixOf`) <$> getDirectoryContents thDir
    when sapic $ mapM_ runSapic (map (thDir </>) sapicPaths)
    thPaths <- filter (".spthy" `isSuffixOf`) <$> getDirectoryContents thDir
    theories <- catMaybes <$> mapM loadThy (zip [1..] (map (thDir </>) thPaths))
    putStrLn readyMsg
    return $ M.fromList theories
  where
    -- run Sapic
    runSapic :: String -> IO ()
    runSapic path = 
        E.handle catchEx $ callCommand $ "sapic " ++ path ++ " > " ++ spthyfile
      where
        -- Exception handler (if loading theory fails)
        catchEx :: E.SomeException -> IO ()
        catchEx e = do
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Unable to run SAPIC on theory file `" ++ path ++ "'"
          putStrLn $ replicate 78 '-'
          print e
        spthyfile = (take ((length path) - 6) path) ++ ".spthy" 
      
    -- Load theories
    loadThy (idx, path) = E.handle catchEx $ do
        thy <- thLoader path
        time <- getZonedTime
        return $ Just
          ( idx
          , Trace $ TheoryInfo idx thy time Nothing True (Local path) autoProver
          )
      where
        -- Exception handler (if loading theory fails)
        catchEx :: E.SomeException -> IO (Maybe (TheoryIdx, EitherTheoryInfo))
        catchEx e = do
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Unable to load theory file `" ++ path ++ "'"
          putStrLn $ replicate 78 '-'
          print e
          return Nothing

-- | Load theories from the current directory, generate map.
loadDiffTheories :: String
             -> FilePath
             -> (FilePath -> IO ClosedDiffTheory)
             -> AutoProver
             -> IO TheoryMap
loadDiffTheories readyMsg thDir thLoader autoProver = do
    thPaths <- filter (".spthy" `isSuffixOf`) <$> getDirectoryContents thDir
    theories <- catMaybes <$> mapM loadThy (zip [1..] (map (thDir </>) thPaths))
    putStrLn readyMsg
    return $ M.fromList theories
  where
    -- Load theories
    loadThy (idx, path) = E.handle catchEx $ do
        thy <- thLoader path
        time <- getZonedTime
        return $ Just
          ( idx
          , Diff $ DiffTheoryInfo idx thy time Nothing True (Local path) autoProver
          )
      where
        -- Exception handler (if loading theory fails)
        catchEx :: E.SomeException -> IO (Maybe (TheoryIdx, EitherTheoryInfo))
        catchEx e = do
          putStrLn ""
          putStrLn $ replicate 78 '-'
          putStrLn $ "Unable to load theory file `" ++ path ++ "'"
          putStrLn $ replicate 78 '-'
          print e
          return Nothing
