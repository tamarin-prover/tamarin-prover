{-# LANGUAGE CPP, DeriveDataTypeable #-}
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
import           Test.HUnit (Counts(..))

import           Main.Console
import           Main.Environment

import qualified Term.UnitTests as TestTerm (main)


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
#ifndef NO_GUI
    putStrLn ""
    successGraphVizDot <- ensureGraphVizDot as
#else
    let successGraphVizDot = True
#endif
    nextTopic "Testing the unification infrastructure"
    Counts _ _ termErrs termFails <- TestTerm.main (maudePath as)
    let successTerm = termErrs == 0 && termFails == 0
        success = and [successMaude, successGraphVizDot, successTerm]

    -- FIXME: Implement regression testing.
    --
    nextTopic "TEST SUMMARY"
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
