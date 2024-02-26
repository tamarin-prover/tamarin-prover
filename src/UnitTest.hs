module Main where

import Test.HUnit
import qualified Term.UnitTests as TU
import qualified Theory.UnitTests as THU

import System.Environment

mainUnit :: IO Counts
mainUnit = runTestTT $ TestList $
  [-- TU.testsSubs
    TU.testsSubsts
--, TU.testsCompareVar
  , TU.testsNorm
--, TU.testsUnify
  , TU.testsTerm
  , TU.testsMatching
--, TU.testsTrivial
  , THU.testsEquationStore
  ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["variants"] -> TU.mainVariants
    _            -> mainUnit >> pure ()
