-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
module Theory.UnitTests where

import           Term.Builtin.Convenience
import           Theory.Tools.IntruderRules

{-
-- EquationStore
----------------------------------------------------------------------


testsEquationStore :: Test
testsEquationStore = TestLabel "Tests for EquationStore" $
  TestList
    [ -- testEqual "filterMostGeneral" (filterMostGeneral [s1,s2,s3]) [s1,s3]
--      testTrue "Simplification" test_eqstore_0
      testEqual "" emptyEqStore
        (evalFresh (execStateT (whileTrue $ simp1)
          (EqStore emptySubstVFree (Conj [Disj [substFromList VFresh [(lx1, x3)]]]))) (freshFromUsed []))
    , uncurry (testEqual "Simplification") test_eqstore_1
    , uncurry (testEqual "Simplification") test_eqstore_2
    , uncurry (testEqual "Simplification") test_eqstore_3
    ]
 where
--  s1 = substFromList VFresh [(lv1, p1 # v4),      (lv2, v3)]
--  s2 = substFromList VFresh [(lv1, p2 # p1 # p6), (lv2, p3)] -- subsumed by s1 mod AC
--  s3 = substFromList VFresh [(lv1, v5 # v4 # p6), (lv2, p4)] -- not subsumed

-- Equation Store
----------------------------------------------------------------------

{-
test_eqstore_0 :: Bool
test_eqstore_0 = all snd $ map (\(s0,s') -> let s = restrict (dom s') (s0 `composeVFresh` csubst) in
                               ((s,s'),s1 `eqSubstSubs` s')) $ zip substs [s1,s2,s3]
 where s1 = substFromList VFresh [(lx1, pair(pair(x1,x2),f1)), (lx2, x6), (lx3, x6),
                                    (lx5, x6) , (lx7, expo(pair(x1,x2),f1))]
       s2 = substFromList VFresh [(lx1, pair(pair(f1,p1),f2)), (lx2, x5), (lx3, x5),
                                    (lx4, x5) , (lx7, expo(pair(x1,x2),f1))]
       s3 = substFromList VFresh [(lx1, pair(pair(p1,f1),f2)), (lx2, x7), (lx3, x7),
                                    (lx6, x7) , (lx7, expo(pair(x1,x2),f1))]
       EqStore csubst (Conj [Disj substs]) =
           evalFresh (simp (EqStore emptySubstFree (Conj [Disj [s1,s2,s3]])))
                     (freshFromUsed (lvars [s1,s2,s3]))
-}

test_eqstore_1 :: (EqStore, EqStore)
test_eqstore_1 =
  ( EqStore csubst (Conj [Disj [s1',s2',s3']])
  , evalFresh (execStateT (whileTrue $ simp1) (EqStore emptySubstVFree (Conj [Disj [s1,s2,s3]])))
              (freshFromUsed (lvars [s1,s2,s3])))
  -- abstract the common pair x1, identify x2 and x3
 where s1  = substFromList VFresh [(lx1, pair(pair(x1,x2),f1)),  (lx2, x6), (lx3, x6), (lx5, x6) ]
       s2  = substFromList VFresh [(lx1, pair(p1,f2)),           (lx2, x5), (lx3, x5), (lx4, x5) ]
       s3  = substFromList VFresh [(lx1, pair(p1,f2)),           (lx2, x7), (lx3, x7), (lx6, x7) ]

       s1' = substFromList VFresh [(lx8, pair(x16,x17)), (lx5,x15), (lx9, f1), (lx11, x15) ]
       s2' = substFromList VFresh [(lx8, p1), (lx9, f2), (lx4, x13), (lx11, x13) ]
       s3' = substFromList VFresh [(lx8, p1), (lx9, f2), (lx6, x13), (lx11, x13) ]

       csubst = substFromList VFree [(lx1, pair(x8, x9)), (lx2, varTerm $ LVar "x" 11),
                                     (lx3, varTerm $ LVar "x" 11) ]
       [x13,_x14,x15,x16,x17] = [ varTerm $ LVar "x" i | i <- [13..17]]
       lx11 = LVar "x" 11

test_eqstore_2 :: ([LSubst VFree], [LSubst VFree])
test_eqstore_2 =
  ( [substFromList VFree [(lx1, pair(x2,x3))], substFromList VFree [(lx2,f1)]]
  , evalFresh (simpAbstract (Disj [s1,s2])) (freshFromUsed [lx1]))
 where s1 = substFromList VFresh [(lx1, pair(pair(x1,x2),f1)), (lx2, f1), (lx3,x3)]
       s2 = substFromList VFresh [(lx1, pair(p1,f2)),          (lx2, f1), (lx3, x3)]

test_eqstore_3 :: ([LSubst VFree], [LSubst VFree])
test_eqstore_3 =
  ([substFromList VFree [(lx2,x8), (lx3,x8)]]
  , evalFresh (simpIdentify (Disj [s1,s2,s3])) (freshFromUsed (lvars [s1,s2,s3])))
 where s1 = substFromList VFresh [(lx1, pair(pair(x1,x2),f1)), (lx2, x6), (lx3, x6), (lx5, x6) ]
       s2 = substFromList VFresh [(lx1, pair(p1,f2)), (lx2, x5), (lx3, x5), (lx4, x5) ]
       s3 = substFromList VFresh [(lx1, pair(p1,f2)), (lx2, x7), (lx3, x7), (lx6, x7) ]


-- Rule Variants
----------------------------------------------------------------------

testProtoRule :: ProtoRule
testProtoRule = Rule (NProtoRuleInfo (ProtoRule "Proto1") [])
                [ Fact (ProtoFact "Foo")
                       [hash( expo (p1, (fr x1) # y1) ) , pubTerm "u"],
                  Fact (ProtoFact "Bar") [varTerm (LVar "z" 2), freshTerm "freshname"],
                  Fact FreshFact [x1], Fact FreshFact [y1]]
                []

{-
iso_I_3:
      [ iso_I_2( I, R, ni, hkr ) ]
      -->
      [ iso_I_3( I, R, ni, hkr ),
        SeKeyI( hkr^fr(ni), <pb(I), pb(R), 'g'^fr(ni), hkr> ),
        Send( <pb(I), encA{<hkr, 'g'^fr(ni), pb(R)>}sk(pb(I))> ) ]
-}

testProtoRule2 :: ProtoRule
testProtoRule2 = Rule (NProtoRuleInfo (ProtoRule "Proto1") [])
                [ Fact (ProtoFact "SeKeyI") [ x3 , expo(vhkr, hash(x1) ) ],
                  Fact (ProtoFact "iso_I_2") [vhkr]]
                []
 where vhkr = varTerm $ LVar "hkr" 0

test_rulevariants_1 :: IO ()
test_rulevariants_1 = do
  putStrLn $ render $ prettyProtoRule $ testProtoRule2
  putStrLn $ render $ prettyProofRule $ variantsProtoRule testProtoRule2

{-
-- | Test for simpCommonEquations, first and third equation should be removed from both.
--   TODO: remove norm after deciding on how to handle normaliztion wrt. AC
testDisj_Common_1 :: Disj LSubst
testDisj_Common_1 = Disj $ map normSubst
  [ substFromList [(lv1, p1), (lv2, p2), (lv3, p4 # p5)]
  , substFromList [(lv1, p1), (lv2, p3), (lv3, p5 # p4)] ]

test_factorSubstDisjunction_1 :: Maybe (LSubst, Disj LSubst)
test_factorSubstDisjunction_1 = factorSubstDisjunction testDisj_Common_1

-- | Test for simpCommonEquations, first and third equation should be removed from both.
--   TODO: remove norm after deciding on how to handle normaliztion wrt. AC
testRemoveRenamings_Common_1 :: Disj LSubst
testRemoveRenamings_Common_1 = Disj $ map substFromList
  [ [(lv1, v4), (lv2, v5), (lv3, p4 # p5)]
  , [(lv1, v4), (lv2, v5), (lv3, p6 # p4)] ]

test_RemoveRenamings_1 :: Maybe (LSubst, Disj LSubst)
test_RemoveRenamings_1 = factorSubstDisjunction testRemoveRenamings_Common_1

-- | There is no common renaming, so nothing should be removed
--test_RemoveRenamings_2 :: Bool
test_RemoveRenamings_2 = simpRemoveCommonRenamings disj == Nothing
 where disj = Disj $ map substFromList
              [ [(lv1, v4), (lv2, v4), (lv3, v4)],
                [(lv1, v4), (lv2, v4), (lv3, v5)],
                [(lv1, v4), (lv2, v4), (lv3, p1)] ]

-- | Test for variable identification, v1 and v2 should be
--   identified.
testDisj_Identify_1 :: Maybe (LSubst, Disj LSubst)
testDisj_Identify_1 = factorSubstDisjunction $ substDisjIdentify

testDisj_Identify_2 :: Maybe (LSubst, Disj LSubst)
testDisj_Identify_2 = simpIdentifyVars $ substDisjIdentify

substDisjIdentify :: Disj (Subst Name LVar)
substDisjIdentify = Disj $ map substFromList
  [ [(lv1, v4), (lv2, v4), (lv3, v4)],
    [(lv1, v4), (lv2, v4), (lv3, v5)],
    [(lv1, v4), (lv2, v4), (lv3, p1)] ]


-- | Test for abstraction, factor out assignment for "y"
testDisj_AbstractOuterMost :: Disj LSubst
testDisj_AbstractOuterMost = Disj $ map substFromList
  [ [(lv1, p1 # p2),      (lv2, p1 # p2)],
    [(lv1, p3 # p4),      (lv2, p3 # p4)],
    [(lv1, expo (p1,p5)), (lv2, p5 # (p6 # p7))]]

-}
-}
-- Tests/Experiments
----------------------------------------------------------------------

{-
         m2              m1   m2
     ---------- hash    ---------- pair
        h(m2)            <m1,m2>
        ------------------------ encS
           encS(<m1,m2>,m2)
-}
test_recipe_2 :: Bool
test_recipe_2 = (encTerm (hashTerm y1) (pairTerm y0 y1)) ==  reci
 where
  encTerm k m = Op2 EncS k m
  pairTerm a b = Op2 Pair a b
  hashTerm a = Op1 Hash a
  m1 = varTerm (LVar "m1" LSortMsg 0)
  m2 = varTerm (LVar "m2" LSortMsg 0)

  hm2 = hashTerm m2
  pm1m2 = pairTerm m1 m2

  hRule = Rule (IntrRuleACStandard (hashTerm y0)    Constr) [msgFact m2] [msgFact hm2]
  pRule = Rule (IntrRuleACStandard (pairTerm y0 y1) Constr) [msgFact m1, msgFact m2] [msgFact pm1m2]
  eRule = Rule (IntrRuleACStandard (encTerm y0 y1)  Constr) [msgFact hm2, msgFact pm1m2] [msgFact (encTerm hm2 pm1m2)]

  reci = recipe eRule [(pRule, 1, eRule), (hRule, 0, eRule)]

{-
         <m1,m2>              <m1,m2>
     -------------- hash    ---------- fst
        h(<m1,m2>)              m1
        ------------------------------ encS
           encS(<m1,m2>,m1)

  <m1,m2> message premise for both hash and fst. But
  hash premise must come from Pair and fst premises
  cannot come from Pair => we cannot identify the two
  by using the same variable.
-}
test_recipe_3 :: Bool
test_recipe_3 = encTerm (hashTerm y1) (fstTerm y0) == reci
 where
  m1 = varTerm (LVar "m1" LSortMsg 0)
  m2 = varTerm (LVar "m2" LSortMsg 0)
  encTerm k m = Op2 EncS k m
  pairTerm a b = Op2 Pair a b
  hashTerm a = Op1 Hash a
  fstTerm a = Op1 Fst a

  h = hashTerm pm1m2
  pm1m2 = pairTerm m1 m2

  hRule   = Rule (IntrRuleACStandard (hashTerm y0) Constr)   [msgFact pm1m2] [msgFact h]
  fstRule = Rule (IntrRuleACStandard (fstTerm y0) Constr)    [msgFact pm1m2] [msgFact m1]
  eRule   = Rule (IntrRuleACStandard (encTerm y0 y1) Constr) [msgFact h, msgFact m1] [msgFact (encTerm h m1)]

  reci = recipe eRule [(fstRule, 1, eRule), (hRule, 0, eRule)]
