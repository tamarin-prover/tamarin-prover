{-# LANGUAGE GADTs, FlexibleContexts, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Subsumption of terms and substitutions.
module Term.Subsumption (
    compareTermSubs
  , eqTermSubs

  , factorSubstVia
--  , factorSubstOnVFresh

  -- * canonical representations for substitutions
  --   modulo renaming
  , canonizeSubst

  -- * for testing only
  , varOccurences
) where

import Term.Term
import Term.LTerm
import Term.Unification
import Term.Positions

import Extension.Prelude
-- import Utils.Misc

import Control.Basics

----------------------------------------------------------------------
-- Subsumption order on terms and substitutions
----------------------------------------------------------------------

-- | Compare terms @t1@ and @t2@ with respect to the subsumption order modulo AC.
compareTermSubs :: LNTerm -> LNTerm -> WithMaude (Maybe Ordering)
compareTermSubs t1 t2 = do
    check <$> matchLNTerm [t1 `MatchWith` t2] <*> matchLNTerm [t2 `MatchWith` t1]
  where
    check []    []    = Nothing
    check (_:_) []    = Just GT
    check []    (_:_) = Just LT
    check (_:_) (_:_) = Just EQ

-- | Returns True if @s1@ and @s2@ are equal with respect to the subsumption order modulo AC.
eqTermSubs :: LNTerm -> LNTerm -> WithMaude Bool
eqTermSubs s1 s2 = (== Just EQ) <$> compareTermSubs s1 s2 

-- | @factorSubstOn s1 s2 vs@ factors the free substitution @s1@
--   through free substitution @s2@ on @vs@,
--   i.e., find a complete set of free substitutions s such that for all
--   vars @x `elem` vs@:
--   >  applyVTerm s1 x =AC= applyVTerm s (applyVTerm s2 x).
factorSubstVia :: [LVar] -> LNSubst -> LNSubst -> WithMaude [LNSubst]
factorSubstVia vs s1 s2 =
    matchLNTerm (zipWith MatchWith (substToListOn vs s1) (substToListOn vs s2))

{-
-- | @factorSubstOnVFresh s1 s2 vs@ factors the fresh substitution @s1@
--   through the free substitution @s2@ on @vs@,
--   i.e., it returns a complete set of fresh substitutions s such that
--   s1 is equivalent to s.s2 modulo renaming.
factorSubstViaVFresh :: [LVar] -> LNSubstVFresh -> LNSubst 
                    -> WithMaude [LNSubstVFresh]
factorSubstViaVFresh vs s1_0 s2 = do
    matchers <- matchLNTerm (zipWith MatchWith l1 l2)
    return $ do
        s <- matchers
        when (not $ varsRange s `subsetOf` varsRange s1) $
            error $ "factorSubstOnVFresh " ++ show s1 ++ " " ++ show s2 
                    ++ " => " ++ show s ++ " contains new variables"
        return $ freeToFreshRaw s
  where
    s1 = freshToFreeAvoiding s1_0 (vs, varsRange s2)
    l1 = substToListOn vs s1
    l2 = substToListOn vs s2
-}

----------------------------------------------------------------------
-- Equality of substitutions modulo AC and renaming
----------------------------------------------------------------------

-- | Returns a substitution that is equivalent modulo renaming to the given substitution.
canonizeSubst :: LNSubstVFresh -> LNSubstVFresh
canonizeSubst subst =
    mapRangeVFresh (applyVTerm renaming) subst
  where
    vrangeSorted = sortOn (varOccurences subst) (varsRangeVFresh subst)
    renaming = substFromList $
                 zipWith (\lv i -> (lv, varTerm $ LVar "x" (lvarSort lv) i))
                         vrangeSorted [1..]

-- | @varOccurences v t@ returns a sorted list of positions where the
--   variable @v@ occurs in @t@. The function returns the same result for
--   terms that are equal modulo AC since the flattened term representation
--   is used.
varOccurences :: LNSubstVFresh -> LVar  -> [[Position]]
varOccurences subst v = map (go []) $ rangeVFresh subst
  where
    go pos (viewTerm -> Lit (Var v')) | v == v' = [pos]
                          | otherwise = []
    go _   (viewTerm -> Lit (Con _))  = []
    go pos (viewTerm -> FApp (AC _) as) = concatMap (go (0:pos)) as
    go pos (viewTerm -> FApp _ as) =
        concat (zipWith (\i -> go (i:pos)) [0 .. ] as)