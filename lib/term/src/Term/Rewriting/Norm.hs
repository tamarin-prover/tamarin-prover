{-# LANGUAGE PatternGuards, FlexibleContexts, ExplicitForAll, ScopedTypeVariables #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- This module implements normalization with respect to DH u AC using class
-- rewriting and an ad-hoc function that uses the @TermAC@ representation of
-- terms modulo AC. 
module Term.Rewriting.Norm (
--    norm
   norm'
--   , nf
  , nf'
  , nfSubstVFresh'
  , normSubstVFresh'
  , maybeNotNfSubterms
) where

import Term.Term
import Term.LTerm
import Term.Rewriting.NormAC
import Term.Substitution
import Term.Maude.Types
import Term.Maude.Process
import Term.SubtermRule
import Term.Unification

import Utils.Misc

import Control.Basics
import Control.Monad.Reader

import Data.List

import System.IO.Unsafe (unsafePerformIO)

-- Normalization using Maude
----------------------------------------------------------------------

-- | @norm t@ normalizes the term @t@ using Maude.
norm :: (Show (Lit c LVar), Ord c, IsConst c)
     => (c -> LSort) -> LTerm c -> WithMaude (LTerm c)
norm _      t@(Lit _) = return t
norm sortOf t         = reader $ \hnd -> normAC $ unsafePerformIO $ normViaMaude hnd sortOf t

-- | @norm' t@ normalizes the term @t@ using Maude.
norm' :: LNTerm -> WithMaude LNTerm
norm' = norm sortOfName

-- | @nf t@ returns @True@ if the term @t@ is in normal form.
nf :: forall c. (Show (Lit c LVar), Ord c, IsConst c)
   => (c -> LSort) -> LTerm c -> WithMaude Bool
nf sortOf t0 = reader $ \hnd -> check hnd
  where
    check hnd = go t0
      where
        -- AC operator must have more than one arguments
        go t@(FApp (AC _) ts) | length ts < 2
          = error $ "nf': unexpected AC operator with less than two arguments: `"++ show t++"'"

        -- irreducible function symbols
        go (FApp (NonAC o) ts) | o `elem` irreducible                    = all go ts

        -- exponentiation
        go (FApp (NonAC o1) [ FApp (NonAC o2) _, _])
          | dh && o1 == expSym && o2 == expSym                           = False
        go (FApp (NonAC o1) [ _, FApp (NonAC o2) []])
          | dh && o1 == expSym && o2 == oneSym                           = False
        go (FApp (NonAC o1) [(FApp (NonAC o2) _)])
          | dh && o1 == invSym && o2 == invSym                           = False
        go (FApp (NonAC o1) [(FApp (AC Mult) ts)])
          | dh && o1 == invSym && any isInv ts                           = False

        -- subterm rules
        go t@(FApp (NonAC _) _) | any (struleApplicable t) strules       = False

        -- multiplication
        go (FApp (AC Mult) ts)
          | one `elem` ts || any isMult ts || invalidMult ts             = False

        -- xor
        go (FApp (AC Xor) ts)
          | zero `elem` ts || any isXor ts || not (noDuplicates ts)      = False

        go (FApp _ ts)                                                   = all go ts
        go (Lit _ )                                                      = True

        struleApplicable t (StRule lhs rhs) =
            case matchLTerm sortOf [t `MatchWith` toLTerm lhs] `runReader` hnd of
              []  -> False
              _:_ -> case rhs of
                       RhsPosition _ -> True
                       RhsGround   s -> not (t == toLTerm s)
                           -- reducible, but RHS might be already equal to t

        invalidMult ts = case partition isInv ts of
            ([],_)           -> False
            ([ FApp _oinv [ FApp (AC Mult) ifactors ] ], factors) ->
                (ifactors \\ factors /= ifactors)
                || (factors \\ ifactors /= factors)
            ([ FApp _oinv [t] ], factors) -> t `elem` factors
            (_:_:_, _)       -> True
            _ -> False

        isMult (FApp (AC Mult) _) = True
        isMult _                  = False

        isXor (FApp (AC Xor) _) = True
        isXor _                 = False

        isInv  (FApp (NonAC o) _) | o == invSym = True
        isInv  _                                = False

        toLTerm :: LNTerm -> LTerm c
        toLTerm (FApp o ts)   = FApp o (map toLTerm ts)
        toLTerm (Lit (Var v)) = Lit (Var v)
        toLTerm t@(Lit _)       = error $ "toLTerm: impossible, unexpected constant in `"
                                          ++show t++"'"

        msig        = mhMaudeSig hnd
        strules     = stRules msig
        irreducible = irreducibleFunSig msig
        dh          = enableDH msig
        one         = FApp (NonAC oneSym) []
        zero        = FApp (NonAC zeroSym) []


-- | @nf' t@ returns @True@ if the term @t@ is in normal form.
nf' :: LNTerm -> WithMaude Bool
nf' = nf sortOfName

-- | @nfViaMaude t@ returns @True@ if the term @t@ is in normal form.
nfViaMaude :: (Show (Lit c LVar), Ord c, IsConst c)
           => (c -> LSort) -> LTerm c -> WithMaude Bool
nfViaMaude sortOf t = (t ==#) <$> norm sortOf t

-- | @nfCompare t@ performs normal-form checks using maude and the haskell function
--   and fails if the results differ.
_nfCompare :: (Show (Lit c LVar), Ord c, IsConst c)
           => (c -> LSort) -> LTerm c -> WithMaude Bool
_nfCompare sortOf t0 = reader $ \hnd ->
    case ((nfViaMaude sortOf t0) `runReader` hnd, (nfViaMaude sortOf t0) `runReader` hnd) of
        (x, y) | x == y -> x
        (x, y) ->
          error $ "nfCompare: Maude disagrees with haskell nf: "++ show t0
                  ++" maude: " ++ show x ++ "haskell: "++show y


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

-- | Returns all subterms that may be not in normal form.
maybeNotNfSubterms :: MaudeSig -> LNTerm -> [LNTerm]
maybeNotNfSubterms msig t0 = go t0
  where irreducible = irreducibleFunSig msig
        go (Lit _)                                    = []
        go (FApp (NonAC o) as) | o `elem` irreducible = concatMap go as
        go t                                          = [t]
