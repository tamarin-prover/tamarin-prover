{-# LANGUAGE PatternGuards, FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- This module implements normalization with respect to AC.
module Term.Rewriting.NormAC (
    (==#)
  , termFlatten
  , normAC
) where

import Term.Term

import Data.List ( sort )

-- Normalization modulo AC = flatten + sort
----------------------------------------------------------------------

-- | @termFlatten t@ converts a term @t@ to its flat representation, i.e.,
--   AC-operator applications are replaced by n-ary, non-nested
--   AC-operator applications.
termFlatten :: (Ord a) => Term a -> Term a
termFlatten t =
    go t
  where
    go (Lit l) = Lit l
    go (FApp (AC o) as) = FApp (AC o) (concatMap collectOTerms (map go as))
      where
        collectOTerms (FApp (AC o') ts) | o == o' = ts
        collectOTerms a                           = [a]
    go (FApp o as)      = FApp o (map go as)

-- | @normAC t@ normalizes the term @t@ wrt. to the equations AC,
-- i.e., by flattening and sorting wrt. Ord.
normAC :: (Ord t) => Term t -> Term t
normAC = foldTerm Lit (\o -> FApp o . sortAC o) . termFlatten
  where
    sortAC (AC _) as = sort as
    sortAC _      as = as

-- | @a ==# b@ returns @True@ if @a@ is equal @b@ modulo AC.
(==#) :: (Ord a) => Term a -> Term a -> Bool
a ==# b = normAC a == normAC b

