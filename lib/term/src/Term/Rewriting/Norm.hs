{-# LANGUAGE PatternGuards, FlexibleContexts, ExplicitForAll #-}
{-# LANGUAGE ScopedTypeVariables, ViewPatterns #-}
  -- spurious warnings for view patterns
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
  , nf'
  , nfSubstVFresh'
  , normSubstVFresh'
  , maybeNotNfSubterms
) where

import Term.Term
import Term.LTerm
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
norm _      t@(viewTerm -> Lit _) = return t
norm sortOf t         = reader $ \hnd -> unsafePerformIO $ normViaMaude hnd sortOf t

-- | @norm' t@ normalizes the term @t@ using Maude.
norm' :: LNTerm -> WithMaude LNTerm
norm' = norm sortOfName


-- | @nf t@ returns @True@ if the term @t@ is in normal form.
nfViaHaskell :: forall c. (Show (Lit c LVar), Ord c, IsConst c)
   => (c -> LSort) -> LTerm c -> WithMaude Bool
nfViaHaskell sortOf t0 = reader $ \hnd -> check hnd
  where
    check hnd = go t0
      where
        -- AC operator must have more than one arguments
        go t@(viewTerm -> FApp (AC _) ts) | length ts < 2
          = error $ "nf': unexpected AC operator with less than two arguments: `"++ show t++"'"

        -- irreducible function symbols
        go (viewTerm -> FApp (NonAC o) ts) | o `elem` irreducible                    = all go ts

        -- exponentiation
        go (viewTerm -> FApp (NonAC o1) [ viewTerm -> FApp (NonAC o2) _, _])
          | dh && o1 == expSym && o2 == expSym                           = False
        go (viewTerm -> FApp (NonAC o1) [ _, viewTerm -> FApp (NonAC o2) []])
          | dh && o1 == expSym && o2 == oneSym                           = False
        go (viewTerm -> FApp (NonAC o1) [(viewTerm -> FApp (NonAC o2) _)])
          | dh && o1 == invSym && o2 == invSym                           = False
        go (viewTerm -> FApp (NonAC o1) [(viewTerm -> FApp (AC Mult) ts)])
          | dh && o1 == invSym && any isInverse ts                       = False

        -- subterm rules
        go t@(viewTerm -> FApp (NonAC _) _) | any (struleApplicable t) strules       = False

        -- multiplication
        go (viewTerm -> FApp (AC Mult) ts)
          | one `elem` ts || any isProduct ts || invalidMult ts          = False

        -- xor
        go (viewTerm -> FApp (AC Xor) ts)
          | zero `elem` ts || any isXor ts || not (noDuplicates ts)      = False

        go (viewTerm -> FApp _ ts)                                       = all go ts
        go (viewTerm -> Lit _ )                                          = True

        go _impossible = error "nfViaHaskell: impossible"

        struleApplicable t (StRule lhs rhs) =
            case matchLTerm sortOf [t `MatchWith` toLTerm lhs] `runReader` hnd of
              []  -> False
              _:_ -> case rhs of
                       RhsPosition _ -> True
                       RhsGround   s -> not (t == toLTerm s)
                           -- reducible, but RHS might be already equal to t

        invalidMult ts = case partition isInverse ts of
            ([],_)           -> False
            ([ viewTerm -> FApp _oinv [ viewTerm -> FApp (AC Mult) ifactors ] ], factors) ->
                (ifactors \\ factors /= ifactors)
                || (factors \\ ifactors /= factors)
            ([ viewTerm -> FApp _oinv [t] ], factors) -> t `elem` factors
            (_:_:_, _)       -> True
            _ -> False

        toLTerm :: LNTerm -> LTerm c
        toLTerm t = case viewTerm t of
            FApp o ts   -> unsafefApp o (map toLTerm ts)
            Lit (Var v) -> lit (Var v)
            Lit _       -> error $ "toLTerm: impossible, unexpected constant in `"
                                                ++show t++"'"

        msig        = mhMaudeSig hnd
        strules     = stRules msig
        irreducible = irreducibleFunSig msig
        dh          = enableDH msig
        one         = fApp (NonAC oneSym) []
        zero        = fApp (NonAC zeroSym) []

-- | @nf' t@ returns @True@ if the term @t@ is in normal form.
nf' :: LNTerm -> WithMaude Bool
nf' = nf sortOfName

-- | @nfViaMaude t@ returns @True@ if the term @t@ is in normal form.
nfViaMaude :: (Show (Lit c LVar), Ord c, IsConst c)
           => (c -> LSort) -> LTerm c -> WithMaude Bool
nfViaMaude sortOf t = (t ==) <$> norm sortOf t


-- | @nfCompare t@ performs normal-form checks using maude and the haskell function
--   and fails if the results differ.
_nfCompare :: (Show (Lit c LVar), Ord c, IsConst c)
           => (c -> LSort) -> LTerm c -> WithMaude Bool
_nfCompare sortOf t0 = reader $ \hnd ->
    case ((nfViaMaude sortOf t0) `runReader` hnd, (nfViaHaskell sortOf t0) `runReader` hnd) of
        (x, y) | x == y -> x
        (x, y) ->
          error $ "nfCompare: Maude disagrees with haskell nf: "++ show t0
                  ++" maude: " ++ show x ++ "haskell: "++show y

nf :: (Show (Lit c LVar), Ord c, IsConst c)
   => (c -> LSort) -> LTerm c -> WithMaude Bool
nf = nfViaHaskell


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
        go (viewTerm -> Lit _)                                    = []
        go (viewTerm -> FApp (NonAC o) as) | o `elem` irreducible = concatMap go as
        go t                                                      = [t]
