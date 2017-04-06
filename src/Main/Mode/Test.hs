{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Self-test mode for the Tamarin prover.
module Main.Mode.Test (
    testMode
  ) where

import           System.Console.CmdArgs.Explicit as CmdArgs
import           System.Exit
import           Test.HUnit                      (Counts(..), runTestTT)

import           Main.Console
import           Main.Environment

import qualified Term.UnitTests                  as Term (tests)
-- import qualified Test.ParserTests                as Parser


-- | Self-test mode.
testMode :: TamarinMode
testMode = tamarinMode
    "test"
    ("Self-test the " ++ programName ++ " installation.")
    setupFlags
    run
  where
    setupFlags defaultMode = defaultMode
      { modeArgs       = ([], Just $ flagArg (updateArg "inFile") "FILES")
      , modeGroupFlags = Group
          { groupUnnamed = toolFlags
          , groupHidden  = []
          , groupNamed   = [("About", [helpFlag])]
          }
      }

-- | Run the self-test.
run :: TamarinMode -> Arguments -> IO ()
run _thisMode as = do
    putStrLn $ "Self-testing the " ++ programName ++ " installation."
    nextTopic "Testing the availability of the required tools"
    successMaude <- ensureMaude as
    _ <- ensureSapic as
#ifndef NO_GUI
    putStrLn ""
    successGraphVizDot <- ensureGraphVizDot as
#else
    let successGraphVizDot = True
#endif
    {- FIXME (SM): move test-suite into its own .cabal section.
     - I've disabled this part when I've moved to embedding all data files to
     - simplify packaging.
     - (2015-04-13)

    --------------------------------------------------------------------------
    nextTopic "Testing the parser on our examples"
    examplePath   <- getDataFileName "examples"
    let mkParseTest = Parser.testParseFile Nothing
    parseTests    <- Parser.testParseDirectory mkParseTest 2 examplePath
    successParser <- runUnitTest $ TestList parseTests

    --------------------------------------------------------------------------
    nextTopic "Testing the prover on some of our examples"

    let heuristic  = roundRobinHeuristic [SmartRanking False]
        autoProver = AutoProver heuristic Nothing CutDFS
        prover = Just ( maudePath as
                      , replaceSorryProver $ runAutoProver autoProver
                      )
        mkProverTest file = do
            fullFile <- getDataFileName file
            return $ Parser.testParseFile prover fullFile

    nslEx    <- mkProverTest "examples/classic/NSLPK3.spthy"
    loopEx   <- mkProverTest "examples/loops/Minimal_Loop_Example.spthy"
    diffieEx <- mkProverTest "examples/csf12/JKL_TS1_2008_KI.spthy"

    successProver <- runUnitTest $ TestList [ nslEx, loopEx, diffieEx ]
    -}

    --------------------------------------------------------------------------
    nextTopic "Testing the unification infrastructure"
    successTerm  <- runUnitTest =<< Term.tests (maudePath as)

    --------------------------------------------------------------------------
    -- FIXME: Implement regression testing.
    --
    
    nextTopic "TEST SUMMARY"
    let success = and [ successMaude, successGraphVizDot
                      , successTerm] -- , successParser, successProver ]
    if success
      then do putStrLn $ "All tests successful."
              putStrLn $ "The " ++ programName ++ " should work as intended."
              putStrLn $ "\n           :-) happy proving (-:\n"
              exitSuccess
      else do putStrLn $ "\nWARNING: Some tests failed."
              putStrLn $ "The " ++ programName ++ " might NOT WORK AS INTENDED.\n"
              exitFailure
  where
    nextTopic msg = putStrLn $ "\n*** " ++ msg ++ " ***"

    runUnitTest test = do
        Counts _ _ termErrs termFails <- runTestTT test
        let success = termErrs == 0 && termFails == 0
        return success
