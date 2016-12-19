{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
-- |
-- Copyright   : (c) 2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Unit tests for the functions dealing with term algebra and related notions.
module Term.UnitTests -- (tests)
 where

import Term.Substitution
import Term.Subsumption
import Term.Builtin.Convenience
import Term.Unification
import Term.Rewriting.Norm
import Term.Narrowing.Variants
import Term.Positions

import Text.PrettyPrint.Class

import Data.List
import Data.Maybe
import Prelude
import Test.HUnit
import Control.Monad.Reader
-- import Data.Monoid


testEqual :: (Eq a, Show a) => String -> a -> a -> Test
testEqual t a b = TestLabel t $ TestCase $ assertEqual t b a

testTrue :: String -> Bool -> Test
testTrue t a = TestLabel t $ TestCase $ assertBool t a

-- *****************************************************************************
-- Tests for Matching
-- *****************************************************************************

testsMatching :: MaudeHandle -> Test
testsMatching hnd = TestLabel "Tests for Matching" $
    TestList
      [ testTrue "a" (propMatchSound hnd f1 f2)
      , testTrue "b" (propMatchSound hnd (pair(f1,inv(f2))) (pair(f1,inv(f2))))
      , testTrue "c" (propMatchSound hnd t1 t2)
      , testTrue "d" (propMatchSound hnd (x1 # f1) f1)
      , testTrue "e" $ null (solveMatchLNTerm (pair(x1,x2) `matchWith` pair(x1,x1)) `runReader` hnd)
      ]
  where
    t1 = expo (inv(pair(f1,f2)), f2 # (inv f2) # f3 # f4 # f2)
    t2 = expo (inv(pair(f1,f2)), f3 # (inv f2) # f2 # x1 # f5 # f2)

propMatchSound :: MaudeHandle -> LNTerm -> LNTerm -> Bool
propMatchSound mhnd t1 p = all (\s -> applyVTerm s t1 == applyVTerm s p) substs
  where substs = solveMatchLNTerm (t1 `matchWith` p) `runReader` mhnd



-- *****************************************************************************
-- Tests for Unification
-- *****************************************************************************

testsUnify :: MaudeHandle -> Test
testsUnify mhnd = TestLabel "Tests for Unify" $
    TestList
      [ testTrue "a" (propUnifySound mhnd (pair(f1,inv(f2))) (pair(f1,inv(f2))))
      , testTrue "b" (propUnifySound mhnd t1 t2)
      , testTrue "c" (propUnifySound mhnd u1 u2)
      , testTrue "d" (propUnifySound mhnd (sdec(x1,y1)) (sdec(senc(x2,x3), x4)))
      , testTrue "e" (propUnifySound mhnd (fAppEMap (p2,x1)) (fAppEMap (p1,x2)))
    ]
  where
    t1 = expo (inv(pair(f1,f2)), f2 *: (inv f2) *: f3 *: f4 *: x2)
    t2 = expo (inv(pair(f1,f2)), f3 *: (inv f2) *: f2 *: f4 *: f5 *: f2)
    u1 = (f2 *: (inv f2) *: f3 *: f4 *: x2)
    u2 = (f3 *: (inv f2) *: f2 *: f4 *: f5 *: f2)

propUnifySound :: MaudeHandle -> LNTerm -> LNTerm -> Bool
propUnifySound hnd t1 t2 = all (\s -> let s' = freshToFreeAvoiding s [t1,t2] in
                                  applyVTerm s' t1 == applyVTerm s' t2) substs
                               && not (null substs)
  where
    substs = unifyLNTerm [Equal t1 t2] `runReader` hnd


-- *****************************************************************************
-- Tests for Substitutions
-- *****************************************************************************

testsSubst :: Test
testsSubst = TestLabel "Tests for Substitution" $
    TestList
      [ -- introduce renaming for x3
        testEqual "a" (substFromListVFresh [(lx1, p1), (lx2, x6), (lx3,x6), (lx5, p1)])
                      (composeVFresh (substFromListVFresh [(lx5, p1)])
                                     (substFromList [(lx1, x5), (lx2, x3)]))
        -- rename (fresh) x6 in s1b and do not mix up with x6 in s3f
      , testEqual "b" s1b_o_s3f (composeVFresh s1b s3f)
        -- drop x1 |-> p1 mapping from s1b, but apply to x2 |-> pair(x3,x1) in s3f
      , testEqual "c" s1b_o_s4f (composeVFresh s1b s4f)
      , testEqual "d" s4f_o_s3f (compose s4f s3f)
      , testEqual "e" (substFromList [(lx1,f1), (lx2,f1)])
                      (mapRange (const f1) s4f)
      , testTrue  "f" (isRenaming (substFromListVFresh [(lx1,x3), (lx2,x2), (lx3,x1)]))

      , testEqual "g" (substFromListVFresh [(lx1, f1)])
                      (extendWithRenaming [lx1] (substFromListVFresh [(lx1, f1)]))

      , testEqual "h" (substFromListVFresh [(lx2, x1), (lx1, x2)])
                      (extendWithRenaming [lx1] (substFromListVFresh [(lx2, x1)]))
      -- trivial, increase coverage
      , testTrue "i" ((>0) . length $ show s1b)
      , testTrue "j" ((>0) . length $ (render $ prettyLSubstVFresh s1b))
      , testTrue "k" (not . null $ domVFresh s1b)
      , testTrue "l" (not . null $ varsRangeVFresh s1b)
      , testTrue "m" ((>0) . length $ show $ substToListOn [lx1] s4f)
      , testTrue "n" ((<100) . size $ emptySubst)
      , testTrue "o" ((<10000) . size $ s1b)
      , testTrue "p" ((<100) . size $ emptySubstVFresh)
      ]
  where
    s1b       = substFromListVFresh [(lx1, p1), (lx2, x6), (lx3, x6), (lx4, f1)]
    s3f       = substFromList [(lx8, x6), (lx2, pair(x2,x1))]
    s1b_o_s3f = substFromListVFresh -- x2 not identified with x8
                  [(lx1, p1), (lx2, pair(x9, p1)), (lx3, x9), (lx4, f1), (lx6, x10), (lx8, x10)]
    s4f       = substFromList [(lx1, x6), (lx2, pair(x3,x1))]
    s1b_o_s4f = substFromListVFresh
                  [(lx1, x8), (lx2, pair(x7, p1)), (lx3, x7), (lx4, f1), (lx6, x8)]

    s4f_o_s3f = substFromList [(lx1, x6), (lx2, pair(pair(x3,x1),x6)), (lx8, x6)]
    x15 = varTerm $ LVar "x" LSortMsg 15
    x13 = varTerm $ LVar "x" LSortMsg 13
    x20 = varTerm $ LVar "x" LSortMsg 20
    x22 = varTerm $ LVar "x" LSortMsg 22

-- *****************************************************************************
-- Tests for Subsumption
-- *****************************************************************************

testsSubs :: MaudeHandle -> Test
testsSubs mhnd = TestLabel "Tests for Subsumption" $ TestList
    [ tct Nothing f1 f2
    , tct (Just EQ) x1   x2
    , tct (Just LT) x1   (x1 *: x1)
    , tct (Just GT) (x1 *: x1) x1
    , tct (Just GT) (pair(f1 *: f2,f1)) (pair(f2 *: f1,x2))
    , testEqual "a" [substFromList [(lx2, pair(x6,x7)), (lx3, p1)]]
                    (factorSubstVia [lx1]
                                    (substFromList [(lx1,pair(pair(x6,x7),p1))])
                                    (substFromList [(lx1,pair(x2,x3))]) `runReader` mhnd)

    , testEqual "b" [substFromList [(lx2, pair(x6,x7)), (lx3, p1), (lx5, f1), (lx6,f2)]]
                    (factorSubstVia [lx1, lx5, lx6]
                       (substFromList [(lx1,pair(pair(x6,x7),p1)), (lx5,f1), (lx6,f2)])
                       (substFromList [(lx1,pair(x2,x3))]) `runReader` mhnd)

    , testTrue "c" (eqTermSubs p1 p1 `runReader` mhnd)
    ]
  where
     tct res e1 e2 =
         testEqual ("termCompareSubs "++ppLTerm e1++" "++ppLTerm e2) res (compareTermSubs e1 e2 `runReader` mhnd)

ppLTerm :: LNTerm -> String
ppLTerm = render . prettyNTerm

ppLSubst :: LNSubst -> String
ppLSubst = render . prettyLNSubst

-- *****************************************************************************
-- Tests for Norm
-- *****************************************************************************

testsNorm :: MaudeHandle -> Test
testsNorm hnd = TestLabel "Tests for normalization" $ TestList
    [ tcn normBigTerm  bigTerm
    , tcn (expo(f3,f1  *:  f4))
          (expo(expo(f3,f4),f1 *: f1 *: f2 *: inv (inv (inv f1)) *: one *: expo(inv f2,one)))
    , tcn (mult [f1, f1, f2]) (f1  *:  (f1  *:  f2))
    , tcn (inv (f1  *:  f2)) (inv f2  *:  inv f1)
    , tcn (f1  *:  inv f2) (f1  *:  inv f2)
    , tcn (one::LNTerm) one
    , tcn x6 (expo(expo(x6,inv x3),x3))

--    , testEqual "a" (normAC (p3 *: (p1 *: p2))) (mult [p1, p2, p3])
--    , testEqual "b" (normAC (p3 *: (p1 *: inv p3))) (mult [p1, p3, inv p3])
--    , testEqual "c" (normAC ((p1 *: p2) *: p3)) (mult [p1, p2, p3])
--    , testEqual "d" (normAC t1) (mult [p1, p2, p3, p4])
--    , testEqual "e" (normAC ((p1 # p2) *: p3)) (p3 *: (p1 # p2))
--    , testEqual "f" (normAC (p3 *: (p1 # p2))) (p3 *: (p1 # p2))
--    , testEqual "g" (normAC ((p3 *: p4) *: (p1 # p2))) (mult [p3, p4, p1 # p2])
    ]
  where
    tcn e1 e2 = testEqual ("norm "++ppLTerm e2) e1 (norm' e2 `runReader` hnd)
    t1 = (p1 *: p2) *: (p3 *: p4)

-- *****************************************************************************
-- Tests for Term
-- *****************************************************************************

testsTerm :: Test
testsTerm = TestLabel "Tests for Terms" $ TestList
    [ uncurry (testEqual "Terms: propSubtermReplace") (propSubtermReplace bigTerm [1,0]) ]

propSubtermReplace :: Ord a => Term a -> Position -> (Term a, Term a)
propSubtermReplace t p = (t,(t `replacePos` (t `atPos` p,p)))

bigTerm :: LNTerm
bigTerm = pair(pk(x1),
               expo(expo (inv x3,
                          x2 *: x4 *: f1 *: one *: inv (f3 *: f4) *: f3 *: f4 *: inv one),
                    inv(expo(x2,one)) *: f2))

normBigTerm :: LNTerm
normBigTerm = pair(pk(x1),expo(inv x3,mult [f1, f2, x4]))

tcompare :: MaudeHandle -> Test
tcompare hnd =
    TestLabel "Tests for variant order" $ TestList
      [ testTrue "a" (run $ isNormalInstance t su1 su2)
      , testTrue "b" $ not (run $ isNormalInstance t su1 su3)

      , testTrue "c" $ (run $ leqSubstVariant t su5 su4)
      , testTrue "d" $ not (run $ leqSubstVariant t su6 su4)

      , testEqual "e" (run $ compareSubstVariant t su4 su4) (Just EQ)
      , testEqual "f" (run $ compareSubstVariant t su5 su4) (Just LT)
      , testEqual "g" (run $ compareSubstVariant t su4 su5) (Just GT)
      , testEqual "h" (run $ compareSubstVariant t su6 su4) Nothing
      ]
  where
    run :: WithMaude a -> a
    run m = runReader m hnd
    t  = pair(inv(x1) *: x2, inv(x3) *: x2)
    su1 = substFromList [(lx1, x2)]
    su2 = substFromList [(lx2, p1)]
    su3 = substFromList [(lx3, x2)]
    su4 = substFromListVFresh [(lx1, x4), (lx2, x4)]
    su5 = substFromListVFresh [(lx1, p1), (lx2, p1)]
    su6 = substFromListVFresh [(lx1, x4), (lx2, x4), (lx3, x4)]

testsVariant :: MaudeHandle -> Test
testsVariant hnd =
    TestLabel "Tests for variant computation" $ TestList
      [ testEqual "a" (computeVariantsCheck (sdec(x1, p1)) `runReader` hnd)
                      (toSubsts [ []
                                , [(lx1, senc(x1, p1))] ])

      , testEqual "b" (computeVariantsCheck (x1  *:  p1) `runReader` hnd)
                      (toSubsts [ []
                                , [(lx1, one)]
                                , [(lx1, inv(p1))]
                                , [(lx1, inv(p1 *: x1))]
                                , [(lx1, x1 *: inv(p1))]
                                , [(lx1, x1 *:  inv(p1 *: x2))]
                                ])

      , testTrue "e" $ not (checkComplete (sdec(x1, p1)) (toSubsts [[]]) `runReader` hnd)
      , testTrue "f" $ (checkComplete (sdec(x1, p1)) (toSubsts [[], [(lx1, senc(x1,p1))]])
                        `runReader` hnd)
      ]
  where
    toSubsts = map substFromListVFresh

testsSimple :: MaudeHandle -> Test
testsSimple _hnd =
    TestLabel "Tests for simple functions" $ TestList
      [ testTrue "" (size [bigTerm] > 0) ]

-- | All unification infrastructure unit tests.
tests :: FilePath -> IO Test
tests maudePath = do
    mhnd <- startMaude maudePath allMaudeSig
    return $ TestList [ testsVariant mhnd
                      , tcompare mhnd
                      , testsSubs mhnd
                      , testsTerm
                      , testsSubst
                      , testsNorm mhnd
                      , testsUnify mhnd
                      , testsSimple mhnd
                      , testsMatching mhnd
                      ]

-- | Maude signatures with all builtin symbols.
allMaudeSig :: MaudeSig
allMaudeSig = mconcat
    [ bpMaudeSig, msetMaudeSig
    , pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, hashMaudeSig ]


-- testing in ghci
----------------------------------------------------------------------------------

te :: LNTerm
te  = pair(inv(x1) *: x2, inv(x3) *: x2)

sub4, sub6 :: LNSubstVFresh
sub4 = substFromListVFresh [(lx1, x4), (lx2, x4)]
sub6 = substFromListVFresh [(lx1, x4), (lx2, x4), (lx3, x4)]

sub4', sub6' :: LNSubst
sub4' = freshToFreeAvoiding sub4 te
sub6' = freshToFreeAvoiding sub6 te

tevs :: [LVar]
tevs = frees te

runTest :: WithMaude a -> IO a
runTest m = do
    hnd <- startMaude "maude" allMaudeSig
    return $ m `runReader` hnd

{-

runTest $ matchLNTerm [ pair(xor [x5,x6],xor [x4,x5,x6]) `MatchWith` pair(x5,xor [x5,x4]) ]

should be matchable if next matchable also

runTest $ matchLNTerm [ pair(xor [x5,x6],xor [x4,x5,x6]) `MatchWith` pair(x5,xor [x5,x6]) ]

-}

-- convenience abbreviations
----------------------------------------------------------------------------------

pair, expo :: (Term a, Term a) -> Term a
expo = fAppExp
pair = fAppPair

inv :: Term a -> Term a
inv = fAppInv

union, mult :: Ord a => [Term a] -> Term a
union = fAppAC Union
mult  = fAppAC Mult

one :: Term a
one = fAppOne
