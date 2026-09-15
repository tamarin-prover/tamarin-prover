-- Check that releasing cached proof states preserves the complete proof.
-- Demand annotations after search, then compare with a run that retains states.
module Test.ProofTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Extension.Data.Label qualified as L
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
                let proofs retention = map (L.get lProof) $ theoryLemmas $
                        proveTheory (const True) (runAutoProverWith retention aut) thy
                    reconstructed = proofs ReleaseProofStates
                assertBool "trace lemmas were generated" (not $ null reconstructed)
                -- Finish search without forcing state annotations. Comparing the
                -- complete proofs then checks lazy replay against retained states.
                _ <- evaluate $ force $ map (mapProofInfo (const ())) reconstructed
                assertEqual "proofs and annotations match retained search"
                    (proofs RetainProofStates) reconstructed
          , TestLabel ("equivalence annotations: " ++ label) $ TestCase $ do
                let proofs retention = map (L.get lDiffProof) $ diffTheoryDiffLemmas $
                        proveDiffTheory (const True)
                            (runAutoProverWith retention aut)
                            (runAutoDiffProverWith retention aut) diffThy
                    reconstructed = proofs ReleaseProofStates
                assertBool "an equivalence lemma was generated" (not $ null reconstructed)
                _ <- evaluate $ force $ map (mapDiffProofInfo (const ())) reconstructed
                assertEqual "proofs and annotations match retained search"
                    (proofs RetainProofStates) reconstructed
          ]
        | cut <- [CutDFS, CutBFS, CutSingleThreadDFS, CutNothing, CutAfterSorry]
        , bound <- [Nothing, Just 0, Just 1, Just 2]
        , let aut = AutoProver Nothing Nothing bound cut False
              label = show (cut, bound)
        ]

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
