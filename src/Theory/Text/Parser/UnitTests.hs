-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Unit tests for checking that all examples parse properly.
module Theory.Text.Parser.UnitTests (

   testParseFile
 , testParseDirectory
 ) where

import           Test.HUnit

import           Control.Basics

import           System.Directory
import           System.FilePath

import           Theory             (prettyOpenTheory)
import           Theory.Text.Parser
import           Theory.Text.Pretty (render)

-- | Test wether a given file exists, can be parsed, and can still be parsed
-- after being pretty printed.
testParseFile :: FilePath -> Test
testParseFile inpFile = TestLabel inpFile $ TestCase $ do
    thyString <- readFile inpFile
    thy  <- parse "original file:"         thyString
    thy' <- parse "pretty printed theory:" (render $ prettyOpenTheory thy)
    assertEqual "parse . pretty" thy thy'
  where
    parse msg str = case parseOpenTheoryString [] str  of
        Left err  -> do assertFailure $ withLineNumbers $ indent $ show err
                        return (error "testParseFile: not used")
        Right thy -> do return thy
      where
        indent = unlines . map (' ' :) . lines
        withLineNumbers err =
            unlines $ zipWith (\i l -> nr (show i) ++ l) [(1::Int)..] ls
                      ++ ["", "Parse error when parsing the " ++ msg, err]
          where
            ls   = lines str
            n    = length (show (length ls))
            nr i = replicate (1 + max 0 (n - length i)) ' ' ++ i ++ ": "

-- | Create the test whether 'testParseFile' succeeds on all @*.spthy@ files
-- in a given directory and all its subdirectories of depth n.
testParseDirectory :: Int -> FilePath -> IO [Test]
testParseDirectory n dir
  | n < 0     = return []
  | otherwise = do
      rawContents <- getDirectoryContents dir
      let contents = [ dir </> content
                     | content <- rawContents
                     , content /= ".", content /= ".." ]
      subDirs     <- filterM doesDirectoryExist contents
      innerTests  <- mapM (testParseDirectory (n - 1)) subDirs
      let tests = [ file
                  | file <- contents, takeExtension file == ".spthy" ]
      mapM_ (putStrLn . (" peparing: " ++)) tests
      return $ map testParseFile tests ++ map TestList innerTests


