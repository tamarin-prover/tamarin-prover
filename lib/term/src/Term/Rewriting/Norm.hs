{-# LANGUAGE PatternGuards, FlexibleContexts #-}

-- | This module implements normalization with respect to DH u AC using class
--   rewriting and an ad-hoc function that uses the @TermAC@ representation
--   of terms modulo AC. 
module Term.Rewriting.Norm (
    norm
  , norm'
  , nf
  , nf'
  , nfSubstVFresh'
  , normSubstVFresh'
) where

import Term.Term
import Term.LTerm
import Term.Rewriting.NormAC
import Term.Substitution
import Term.Maude.Process

import Control.Basics
import Control.Monad.Reader

import System.IO.Unsafe (unsafePerformIO)

-- Normalization using Maude
----------------------------------------------------------------------

-- | @norm t@ normalized the term @t@ using Maude.
norm :: (Show (Lit c LVar), Ord c, IsConst c)
     => (c -> LSort) -> VTerm c LVar -> WithMaude (VTerm c LVar)
norm _      t@(Lit _) = return t
norm sortOf t         = reader $ \hnd -> normAC $ unsafePerformIO $ normViaMaude hnd sortOf t

norm' :: LNTerm -> WithMaude LNTerm
norm' = norm sortOfName

-- | @nf t@ returns @True@ if the term @t@ is in normal form.
nf :: (Show (Lit c LVar), Ord c, IsConst c)
   => (c -> LSort) -> VTerm c LVar -> WithMaude Bool
nf sortOf t = (t ==#) <$>  norm sortOf t

nf' :: LNTerm -> WithMaude Bool
nf' = nf sortOfName

-- Normalization 
----------------------------------------------------

-- | @nfSubst s@ returns @True@ if the substitution @s@ is in normal form.
nfSubstVFresh' ::  LNSubstVFresh -> WithMaude Bool
nfSubstVFresh' s = reader $ \hnd -> all (\t -> runReader (nf' t) hnd) (rangeVFresh s)

{-
-- | @normSubst s@ normalizes the substitution @s@.
normSubst :: (IsConst c, IsVar v, Show (Lit c v)) => Subst c v -> Subst c v
normSubst s = mapRange norm s

-}

-- | @normSubst s@ normalizes the substitution @s@.
normSubstVFresh' :: LNSubstVFresh -> WithMaude LNSubstVFresh
normSubstVFresh' s = reader $ \hnd -> mapRangeVFresh (\t -> norm' t `runReader` hnd) s