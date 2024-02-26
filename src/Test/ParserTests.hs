-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
--
-- Unit tests for checking that all examples parse properly.
module Test.ParserTests (
   testParseFile
 , testParseDirectory
 ) where

import Test.HUnit

import Control.Basics

import System.Directory
import System.FilePath

import Theory
import Theory.Text.Parser
import Theory.Text.Pretty (render)
import Main.TheoryLoader (addMessageDeductionRuleVariants)

-- | Test wether a given file exists, can be parsed, and can still be parsed
-- after being pretty printed.
testParseFile
  :: Maybe (FilePath, Prover)
  -- ^ Path to maude and prover for testing whether proof parsing
  -- works properly.
  -> FilePath
  -- ^ File on which to test parsing (and proving)
  -> Test
testParseFile optionalProver inpFile = TestLabel inpFile $ TestCase $ do
  thyString <- readFile inpFile
  thy0      <- parse "original file:" thyString
  -- add proofs and pretty print closed theory, if desired
  (thy, thyPretty) <- case optionalProver of
    Nothing ->
      pure (thy0, prettyOpenTheory thy0)
    Just (maudePath, prover) -> do
      closedThy <- proveTheory (const True) prover <$> closeTheory maudePath (removeTranslationItems thy0) False
      pure (normalizeTheory $ openTheory closedThy, prettyClosedTheory closedThy)
  thy' <- parse "pretty printed theory:" (render thyPretty)
  unless (thy == thy') $ do
    let (diff1, diff2) =
            unzip $ dropWhile (uncurry (==)) $ zip (show thy) (show thy')
    assertFailure $ unlines
      [ "Original theory",            "", render (prettyOpenTheory thy), ""
      , "Pretty printed and parsed" , "", render (prettyOpenTheory thy'), ""
      , "Original theory (diff)",            "", indent diff1, ""
      , "Pretty printed and parsed (diff)" , "", indent diff2, "", "DIFFER"
      ]
  where
    indent = unlines . map (' ' :) . lines

    parse msg str = case parseOpenTheoryString [] str  of
      Left err  -> do
        _ <- assertFailure $ withLineNumbers $ indent $ show err
        pure (error "testParseFile: dead code")
      Right thy -> pure $ (normalizeTheory . openTranslatedTheory) (addMessageDeductionRuleVariants (removeTranslationItems thy))
      where
        withLineNumbers err =
          unlines $ zipWith (\i l -> nr (show i) ++ l) [(1::Int)..] ls
                    ++ ["", "Parse error when parsing the " ++ msg, err]
          where
            ls   = lines str
            n    = length (show (length ls))
            nr i = replicate (1 + max 0 (n - length i)) ' ' ++ i ++ ": "

-- | Create the test whether 'testParseFile' succeeds on all @*.spthy@ files
-- in a given directory and all its subdirectories of depth n.
testParseDirectory
  :: (FilePath -> Test)  -- ^ Test creation function.
  -> Int                 -- ^ Maximal depth of traversal.
  -> FilePath            -- ^ Starting directory.
  -> IO [Test]
testParseDirectory mkTest n dir
  | n < 0     = pure []
  | otherwise = do
    rawContents <- getDirectoryContents dir
    let contents = [ dir </> content
                   | content <- rawContents
                   , content /= ".", content /= ".." ]
    subDirs     <- filterM doesDirectoryExist contents
    innerTests  <- mapM (testParseDirectory mkTest (n - 1)) subDirs
    let tests = [ file
                | file <- contents, takeExtension file == ".spthy" ]
    mapM_ (putStrLn . (" peparing: " ++)) tests
    pure $ map mkTest tests ++ map TestList innerTests
