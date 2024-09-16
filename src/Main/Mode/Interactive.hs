{-# LANGUAGE OverloadedStrings #-}
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
import Web.Types (OutputCommand(..), OutputFormat(..))

import Main.Console
import Main.Environment
import Main.TheoryLoader

import qualified Data.ByteString.Char8 as BS
import Network.Wai
import Network.Wai.Middleware.HttpAuth
import Network.Wai.Handler.WarpTLS (runTLS)
import Network.Wai.Handler.WarpTLS.Internal
import Network.TLS (supportedHashSignatures, Version(..))
import Network.TLS.Extra.Cipher (ciphersuite_strong_det)
import Data.Default.Class (def)

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
      , flagOpt "" ["tls-key"] (updateArg "tls-key") "path/to/privatekey.pem"
                "HTTPS-only mode: Private key"
      , flagOpt "" ["tls-cert"] (updateArg "tls-cert") "path/to/certificate.pem"
                "HTTPS-only mode: Certificate"
      , flagOpt "" ["auth-username"] (updateArg "auth-username") "USERNAME"
                "HTTP Basic Auth: username for GUI access (HTTPS-only mode must be enabled)"
      , flagOpt "" ["auth-password"] (updateArg "auth-password") "PASSWORD"
                "HTTP Basic Auth: password for GUI access (HTTPS-only mode must be enabled)"
      , flagOpt "" ["image-format"] (updateArg "image-format") "PNG|SVG" "image format used for graphs (default PNG)"
      , flagNone ["debug"] (addEmptyArg "debug") "Show server debugging output"
      , flagNone ["no-logging"] (addEmptyArg "no-logging") "Suppress web server logs."
      -- , flagNone ["autosave"] (addEmptyArg "autosave") "Automatically save proof state"
      -- , flagNone ["loadstate"] (addEmptyArg "loadstate") "Load proof state if present"
      ] ++
      theoryLoadFlags ++
      toolFlags



-- | Start the interactive theorem proving mode.
run :: TamarinMode -> Arguments -> IO ()
run thisMode as = case findArg "workDir" as of
  Nothing -> helpAndExit thisMode (Just "no working directory specified")
  Just workDir0 -> do
    -- determine working directory
    wdIsFile <- doesFileExist workDir0
    let workDir | wdIsFile  = takeDirectory workDir0
                | otherwise = workDir0
    wdIsDir  <- doesDirectoryExist workDir
    if wdIsDir then do
      -- determine caching directory
      tempDir <- getTemporaryDirectory
      winLoginName <- lookupEnv "USERNAME"
      unixLoginName <- lookupEnv "USER"
      let loginName = fromMaybe "" (winLoginName <|> unixLoginName)
          cacheDir = tempDir </> ("tamarin-prover-cache-" ++ loginName)

      -- Ensure Maude and get the Version in the arguments (__versionPrettyPrint__)
      version <- ensureMaudeAndGetVersion as

      -- process theories
      _ <- case (ocFormat $ readOutputCommand as) of
          OutDot  -> ensureGraphVizDot as
          OutJSON -> ensureGraphCommand as

      port <- readPort

      tlsPrivateKeyPath <- readTLSPrivateKeyPath
      tlsCertificatePath <- readTLSCertificatePath

      -- Determine if TLS is enabled
      let isTLS = not (null tlsCertificatePath) && not (null tlsPrivateKeyPath)

      basicAuthUsername <- readBasicAuthUsername
      basicAuthPassword <- readBasicAuthPassword

      let webUrl = serverUrl port isTLS
      putStrLn $ intercalate "\n"
        [ "The server is starting up on port " ++ show port ++ "."
        , "Browse to " ++ webUrl ++ " once the server is ready."
        , ""
        , "Loading the security protocol theories '" ++ workDir </> "*.spthy"  ++ "' ..."
        , ""
        ]

      withWebUI
        ("Finished loading theories ... server ready at \n\n    " ++ webUrl ++ "\n")
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
        (runWarp port basicAuthUsername basicAuthPassword)

    else
      helpAndExit thisMode
        (Just $ "directory '" ++ workDir ++ "' does not exist.")
  where
    enableLogging = not $ argExists "no-logging" as

    thyLoadOptions = case mkTheoryLoadOptions as of
      Left (ArgumentError e) -> error e
      Right opts             -> opts

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
        Nothing    -> PNG
        Just _     -> error "image-format must be one of PNG|SVG"
    
    -- Generate server URL with scheme based on TLS configuration
    -------------------------------------------------------------
    serverUrl :: Int -> Bool -> String
    serverUrl port isTLS = scheme ++ address ++ ":" ++ show port
      where
        scheme = if isTLS then "https://" else "http://"
        address | interface `elem` ["*","*4","*6"] = "127.0.0.1"
                | otherwise                        = interface

    -- HTTP Basic Auth username and password arguments
    --------------------------------------------------
    readBasicAuthUsername :: IO String
    readBasicAuthUsername = do
      let username = fromMaybe "" (findArg "auth-username" as)
      when (argExists "auth-username" as && null username) $ do
        putStrLn "Error: The --auth-username flag cannot be empty."
        helpAndExit thisMode (Just "No username provided for authentication.")
      pure username
    
    readBasicAuthPassword :: IO String
    readBasicAuthPassword = do
      let password = fromMaybe "" (findArg "auth-password" as)
      when (argExists "auth-password" as && null password) $ do
        putStrLn "Error: The --auth-password flag cannot be empty."
        helpAndExit thisMode (Just "No password provided for authentication.")
      pure password

    authSettings :: AuthSettings
    authSettings = "Tamarin prover interactive mode" { authIsProtected = needsAuth }

    needsAuth :: Request -> IO Bool
    needsAuth _ = return True

    basicAuthMiddleware :: String -> String -> Middleware
    basicAuthMiddleware basicAuthUsername basicAuthPassword =
      basicAuth (\u p -> return $ u == BS.pack basicAuthUsername && p == BS.pack basicAuthPassword) authSettings

    -- Function to apply basic authentication middleware if needed
    applyBasicAuthIfProvided :: String -> String -> Application -> Application
    applyBasicAuthIfProvided username password wapp =
      if not (null username) && not (null password)
        then basicAuthMiddleware username password wapp
        else wapp


    -- TLS certificate and private key path arguments
    -------------------------------------------------
    readTLSCertificatePath :: IO String
    readTLSCertificatePath = do
      let certificate = fromMaybe "" (findArg "tls-cert" as)
      when (argExists "tls-cert" as && null certificate) $ do
        putStrLn "Error: The --tls-cert flag cannot be empty."
        helpAndExit thisMode (Just "No path to TLS certificate provided.")
      pure certificate
    
    readTLSPrivateKeyPath :: IO String
    readTLSPrivateKeyPath = do
      let privateKey = fromMaybe "" (findArg "tls-key" as)
      when (argExists "tls-key" as && null privateKey) $ do
        putStrLn "Error: The --tls-key flag cannot be empty."
        helpAndExit thisMode (Just "No path to TLS private key provided.")
      pure privateKey

    -- TLS settings for HTTPS-only interactive mode access
    ------------------------------------------------------
    tlsCustomSettings :: IO TLSSettings
    tlsCustomSettings = do
      tlsCertificatePath <- readTLSCertificatePath
      tlsPrivateKeyPath <- readTLSPrivateKeyPath

      pure $ TLSSettings
        { certSettings = CertFromFile tlsCertificatePath [] tlsPrivateKeyPath
        , onInsecure = DenyInsecure "This server only accepts secure HTTPS connections."
        , tlsLogging = def
        , tlsAllowedVersions = [TLS13]
        , tlsCiphers = ciphersuite_strong_det
        , tlsWantClientCert = False
        , tlsServerHooks = def
        , tlsServerDHEParams = Nothing
        , tlsSessionManagerConfig = Nothing
        , tlsCredentials = Nothing
        , tlsSessionManager = Nothing
        , tlsSupportedHashSignatures = supportedHashSignatures def
        }
    
    fetchTLSSettings :: IO (Maybe TLSSettings)
    fetchTLSSettings = do
      certificate <- readTLSCertificatePath
      privateKey <- readTLSPrivateKeyPath
      if not (null certificate) && not (null privateKey)
        then do
          -- Load TLS settings if both certificate and key paths are provided
          tlsSettings <- tlsCustomSettings
          pure (Just tlsSettings)
        else
          -- Return Nothing if either certificate or key is missing
          pure Nothing

    -- Main function to run the web server with TLS or plain settings
    runWarp :: Int -> String -> String -> Application -> IO ()
    runWarp port basicAuthUsername basicAuthPassword wapp = handle (\e -> err (e :: IOException)) $ do
      -- Fetch TLS settings (if provided)
      maybeTLSSettings <- fetchTLSSettings

      -- Check if TLS is available
      case maybeTLSSettings of
        -- If TLS settings are provided, run with TLS
        Just tlsSettings -> do
          let appWithAuthIfProvided = applyBasicAuthIfProvided basicAuthUsername basicAuthPassword wapp
          let settings = setHost (fromString interface) $ setPort port defaultSettings
          runTLS tlsSettings settings appWithAuthIfProvided

        -- If TLS settings are not provided, check for basic authentication
        Nothing -> do
          if not (null basicAuthUsername) || not (null basicAuthPassword)
            then
              -- Exit if basic authentication is provided but TLS is missing
              helpAndExit thisMode (Just "Basic Authentication requires TLS. Provide both --tls-cert and --tls-key.")
            else
              -- Run without TLS and without authentication
              Warp.runSettings
                (setHost (fromString interface) $ setPort port defaultSettings)
                wapp

    err e = error $
      "Starting the webserver on "++interface++" failed: \n"
      ++ show e
      ++ "\nNote that you can use '--interface=\"*4\"' for binding to all interfaces."
