-- Check that releasing cached proof states preserves valid annotations.
module Test.ProofTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Extension.Data.Label qualified as L
import Data.Maybe (fromJust)
import Test.HUnit
import Theory
import Theory.Text.Parser

tests :: FilePath -> IO Test
tests maudePath = do
    parsed <- either (fail . show) pure $ parseOpenTheoryString [] traceModel
    thy <- closeTheory maudePath (removeTranslationItems parsed) False
    parsedDiff <- either (fail . show) pure $ parseOpenDiffTheoryString [] diffModel
    diffThy <- closeDiffTheory maudePath (addDefaultDiffLemma parsedDiff) False
    pure $ TestList $ concat
        [ [ TestLabel ("trace annotations: " ++ label) $ TestCase $ do
                let proved = proveTheory (const True) (runAutoProverWith retention aut) thy
                forM_ (theoryLemmas proved) $ \lem -> do
                    prf <- evaluate $ force $ L.get lProof lem
                    let ctxt = getProofContext lem proved
                        sys = fromJust $ psInfo $ root prf
                        checked = checkProof ctxt (\_ s -> sorry Nothing (Just s)) 0 sys prf
                        comparisons = foldProof (compareAnnotation . psInfo) checked
                    assertAnnotations (L.get lName lem) comparisons
          , TestLabel ("equivalence annotations: " ++ label) $ TestCase $ do
                let proved = proveDiffTheory (const True)
                        (runAutoProverWith retention aut) (runAutoDiffProverWith retention aut) diffThy
                assertBool "an equivalence lemma was generated" $
                    not $ null $ diffTheoryDiffLemmas proved
                forM_ (diffTheoryDiffLemmas proved) $ \lem -> do
                    prf <- evaluate $ force $ L.get lDiffProof lem
                    let ctxt = getDiffProofContext lem proved
                        sys = fromJust $ dpsInfo $ root prf
                        checked = fromJust $ runDiffProver
                            (checkAndExtendDiffProver $ sorryDiffProver Nothing)
                            ctxt 0 sys prf
                        compareState step =
                            let (ann, path) = dpsInfo step
                            in [Just ann == (dpsInfo . root <$> atPathDiff checked path)]
                        comparisons = foldDiffProof compareState (insertPathsDiff prf)
                    assertAnnotations (L.get lDiffName lem) comparisons
          ]
        | retention <- [RetainProofStates, ReleaseProofStates]
        , (cut, bound) <- [(CutDFS, Nothing), (CutBFS, Nothing),
                          (CutSingleThreadDFS, Nothing), (CutNothing, Nothing),
                          (CutAfterSorry, Nothing), (CutDFS, Just 2)]
        , let aut = AutoProver Nothing Nothing bound cut False
              label = show (retention, cut, bound)
        ]
  where
    -- The checker can add omitted alternatives to a cut proof. Compare every
    -- original annotation; those new alternatives have no original annotation.
    compareAnnotation (Just original, replayed) = [original == replayed]
    compareAnnotation (Nothing, _) = []
    assertAnnotations name comparisons = do
        assertBool (name ++ ": exercised child states") (length comparisons > 1)
        assertBool (name ++ ": annotations match independent proof replay")
            (and comparisons)

traceModel :: String
traceModel = unlines
    [ "theory ProofStates begin"
    , "rule Left: [] --[Step('left')]-> []"
    , "rule Right: [] --[Step('right')]-> []"
    , "lemma witness: exists-trace \"Ex x #i. Step(x) @ i\""
    , "lemma attack: \"All x #i. Step(x) @ i ==> x = 'left'\""
    , "lemma verified: \"All x #i. Step(x) @ i ==> x = 'left' | x = 'right'\""
    , "end"
    ]

diffModel :: String
diffModel = unlines
    [ "theory DiffProofStates begin"
    , "rule Mark: [] --[Step(diff('left','right'))]-> []"
    , "end"
    ]
