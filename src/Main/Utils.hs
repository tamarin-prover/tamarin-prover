-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Various utility functions for interacting with the user.
module Main.Utils (
    -- * File handling
    writeFileWithDirs

  ) where


import System.FilePath
import System.Directory


------------------------------------------------------------------------------
-- File Handling
------------------------------------------------------------------------------

-- | Write a file and ensure that its containing directory exists.
writeFileWithDirs :: FilePath -> String -> IO ()
writeFileWithDirs file output = do
    createDirectoryIfMissing True (takeDirectory file)
    writeFile file output

