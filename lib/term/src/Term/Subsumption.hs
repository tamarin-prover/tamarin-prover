{-# LANGUAGE ViewPatterns #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Subsumption of terms and substitutions.
module Term.Subsumption (
    compareTermSubs
  , eqTermSubs

  , factorSubstVia

  -- * Canonical representations for substitutions
  --   modulo renaming
  , canonizeSubst

  -- * for testing only
  , varOccurences
) where

-- import Control.Basics

-- import Data.Monoid

import Extension.Prelude

import Term.LTerm
import Term.Unification


----------------------------------------------------------------------
-- Subsumption order on terms and substitutions
----------------------------------------------------------------------

-- | Compare terms @t1@ and @t2@ with respect to the subsumption order modulo AC.
compareTermSubs :: LNTerm -> LNTerm -> WithMaude (Maybe Ordering)
compareTermSubs t1 t2 = do
    check <$> solveMatchLNTerm (t1 `matchWith` t2)
          <*> solveMatchLNTerm (t2 `matchWith` t1)
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
    solveMatchLNTerm (mconcat matches)
  where
    matches :: [Match LNTerm]
    matches = zipWith matchWith (substToListOn vs s1) (substToListOn vs s2)

----------------------------------------------------------------------
-- Equality of substitutions modulo AC and renaming
----------------------------------------------------------------------

-- | Returns a substitution that is equivalent modulo renaming to the given substitution.
canonizeSubst :: LNSubstVFresh -> LNSubstVFresh
canonizeSubst subst =
    mapRangeVFresh (applyVTerm renaming) subst
  where
    occs         = varOccurences $ rangeVFresh subst
    vrangeSorted = sortOn (`lookup` occs) (varsRangeVFresh subst)
    renaming = substFromList $
                 zipWith (\lv i -> (lv, varTerm $ LVar "x" (lvarSort lv) i))
                         vrangeSorted [1..]