{- |
Module      :  Web.Settings
Description :  Various default parameters and settings.
Copyright   :  (c) 2011 Cedric Staub
License     :  GPL-3

Maintainer  :  Cedric Staub <cstaub@ethz.ch>
Stability   :  experimental
Portability :  non-portable
-}

module Web.Settings where

-- | Default port to listen on.
defaultPort :: Int
defaultPort = 3001

-- | Location of static files on the system.
defaultStaticDir :: FilePath
defaultStaticDir = "data"

-- | The base path (URL) for serving static files.
staticRoot :: String
staticRoot = "/static"

-- | Subdirectory to use for images.
imageDir :: FilePath
imageDir = "img"

-- | Filename for persistent state
autosaveSubdir :: FilePath
autosaveSubdir = "tamarin-prover-autosave/"
