module Paths_tamarin_prover (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,9,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "./"
libdir     = "./"
datadir    = "data"
libexecdir = "./"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catchIO (getEnv "tamarin_prover_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "tamarin_prover_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "tamarin_prover_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "tamarin_prover_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
