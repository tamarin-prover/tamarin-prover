-- | Small semantic checks for mirror restriction evaluation.
module Test.DiffTests (tests) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Extension.Data.Label as L
import Data.Maybe (isJust)
import Test.HUnit

import ClosedTheory
import Prover
import OpenTheory
import Rule
import Theory.Model
import Theory.Constraint.System
import Theory.Text.Parser
import TheoryObject
import Theory.Tools.IntruderRules
import Theory.Constraint.Solver.Contradictions
import Theory.Constraint.Solver.ProofMethod

tests :: FilePath -> IO Test
tests maude = pure $ TestList
    [ TestLabel "Distinct mirror rule instances" $ TestCase $ mirrorNodes maude
    , TestLabel "Complete a shared attacker input" $ TestCase $ inputRecipe maude
    ]

mirrorNodes :: FilePath -> IO ()
mirrorNodes maude = do
    input <- either (assertFailure . show) pure $ parseOpenDiffTheoryString [] $ unlines
      [ "theory MirrorNodes begin"
      , "builtins: multiset"
      , "rule P: [] --> [!F('a' ++ 'b')]"
      , "rule R: [!F(x ++ y)] --[A()]-> [G(x)]"
      , "diffLemma D:"
      , "end" ]
    thy <- closeDiffTheory maude input False
    let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
        pc = eitherProofContext ctxt RHS
        inst name = fst $ someRuleACInstAvoiding
          (fmap ProtoInfo $ L.get cprRuleAC $ head
            [r | r <- leftTheoryRules thy, getRuleName (L.get cprRuleE r) == name]) ([] :: [LVar])
        ground ru = apply (substFromList
          [(v, pubTerm (if lvarName v == "x" then "a" else "b")) | v <- frees ru]) ru
        node i = LVar "n" LSortNode i
        original = L.set sNodes (M.fromList
            [(node 0, inst "P"), (node 1, ground (inst "R")), (node 2, ground (inst "R"))]) $
          L.set sEdges (S.fromList
            [Edge (node 0, ConcIdx 0) (node i, PremIdx 0) | i <- [1,2]]) $
          emptySystem RawSource True
        mirrors = getMirrorDG ctxt LHS original
        -- The two consumers have identical actions, but may have different
        -- conclusions. Only some mirror assignments force distinct nodes.
        equality = GAto $ fmap (fmapTerm (fmap Free)) $
          EqE (varTerm (node 1)) (varTerm (node 2))
        verdict m = fst $ doRestrictionsHold pc m [equality] True
        failures = filter ((== TFalse) . verdict) mirrors
        unresolved = filter ((== TUnknown) . verdict) mirrors
        system = L.set dsSide (Just LHS) $ L.set dsSystem (Just original) emptyDiffSystem
        restricted = L.set dpcRestrictions [(RHS, [equality])] ctxt
    assertEqual "four correct mirrors" (4, True) (length mirrors, all isCorrectDG mirrors)
    assertEqual "one action vector" 1 $
      S.size $ S.fromList [M.map (L.get rActs) (L.get sNodes m) | m <- mirrors]
    assertEqual "different node-equality results" (2, 2) (length failures, length unresolved)
    -- Put a definite failure first: action-only deduplication then discarded
    -- the unresolved alternative and incorrectly returned TFalse.
    assertEqual "retain unresolved alternatives" TUnknown $
      fst $ evaluateRestrictions restricted system (failures ++ unresolved) True

-- The attacker sends z and compares the reply to that same z. The left
-- returns z and the right returns h(z), so completing z with a public name
-- is an admitted distinguishing recipe. Its two KU premises must stay tied
-- to the same input node when the evaluator grounds the original graph.
inputRecipe :: FilePath -> IO ()
inputRecipe maude = do
 input <- either (assertFailure . show) pure $ parseOpenDiffTheoryString [] $ unlines
   ["theory InputRecipe begin", "functions: h/1", "rule P: [In(x)] --> [Out(diff(x,h(x)))]", "diffLemma D:", "end"]
 thy <- closeDiffTheory maude (addIntrRuleLabels $ addIntrRuleACsDiffBoth (specialIntruderRules False) $ addIntrRuleACsDiffBothDiff (specialIntruderRules True) input) False
 let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
     proto = fst $ someRuleACInstAvoiding (fmap ProtoInfo $ L.get cprRuleAC $ head (leftTheoryRules thy)) ([] :: [LVar])
     z :: LNTerm
     z = varTerm $ LVar "z" LSortMsg 0
     p = apply (substFromList [(v,z) | v <- frees proto]) proto
     n = LVar "n" LSortNode
     ku = kuFact z
     kd = Fact KDFact S.empty [z]
     inf = Fact InFact S.empty [z]
     outf = Fact OutFact S.empty [z]
     intr i ps cs as = Rule (IntrInfo i) ps cs as []
     original = L.set sNodes (M.fromList [(n 1,intr ISendRule [ku] [inf] []),(n 2,p),(n 3,intr IRecvRule [outf] [kd] []),(n 4,intr IEqualityRule [ku,kd] [] [])]) $
       L.set sEdges (S.fromList [Edge (n 1,ConcIdx 0) (n 2,PremIdx 0),Edge (n 2,ConcIdx 0) (n 3,PremIdx 0),Edge (n 3,ConcIdx 0) (n 4,PremIdx 1)]) $
       L.set sLessAtoms (S.fromList [LessAtom (n 0) (n 1) Adversary,LessAtom (n 0) (n 4) Adversary]) $
       -- A progressed proof has solved formulas; otherwise isFinished treats
       -- even this populated graph as an initial system.
       L.set sSolvedFormulas (S.singleton gtrue) $
       L.set sNextGoalNr 8 $
       L.set sGoals (M.singleton (ActionG (n 0) ku) (GoalStatus False 7 True)) $ emptySystem RawSource True
     sys = L.set dsSide (Just LHS) $ L.set dsSystem (Just original) emptyDiffSystem
     mirrors = getMirrorDG ctxt LHS original
     pc = eitherProofContext ctxt LHS
     recipeEdges = S.fromList
       [Edge (n 0,ConcIdx 0) (n 1,PremIdx 0), Edge (n 0,ConcIdx 0) (n 4,PremIdx 0)]
     certify completed
       | admitted completed = [MirrorAdmitted completed]
       | otherwise          = [MirrorUnresolved]
     admitted completed = M.member (n 0) (L.get sNodes completed)
       && isCorrectDG (L.modify sEdges (S.union recipeEdges) completed)
       && M.elems (L.get sGoals completed) == [GoalStatus True 7 True]
       && not (contradictorySystem pc completed)
     result context = fst $ evaluateRestrictionsFor MirrorAttack certify context sys mirrors False
 assertBool "one open attacker input" $ openGoalsAreAttackerInputs original
 let sharedNode = L.modify sGoals
       (M.insert (ActionG (n 0) (kuFact (varTerm (LVar "other" LSortMsg 1))))
         (GoalStatus False 1 False)) original
 assertBool "different inputs cannot use one pub node" $
   not (openGoalsAreAttackerInputs sharedNode)
 assertEqual "same symbolic recipe has no mirror" 0 $ length mirrors
 assertEqual "complete the admitted distinguishing recipe" TFalse $ result ctxt
 -- Exercise production admission, including ordinary simplification. A
 -- completed input with a stale variable goal is reopened by substGoals.
 let attackSystem = L.set dsProofType (Just RuleEquivalence) $
       L.set dsCurrentRule (Just "P") sys
 assertBool "ordinary admission preserves the completed input" $
   isJust (execDiffProofMethod ctxt DiffAttack attackSystem)
 assertEqual "reject an inadmissible original" TUnknown $
   result (L.set dpcRestrictions [(LHS, [gfalse])] ctxt)
 -- The same graph against the same rule family has a matching recipe.
 let same = L.set dpcPCRight (L.get dpcPCLeft ctxt) ctxt
 assertEqual "retain a matching recipe" TTrue $ fst $
   evaluateRestrictionsFor MirrorAttack certify same sys (getMirrorDG same LHS original) False
