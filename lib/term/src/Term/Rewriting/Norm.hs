{-# LANGUAGE ExplicitForAll      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
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

import           Term.LTerm
import           Term.Maude.Process
import           Term.Maude.Signature
import           Term.Substitution
import           Term.SubtermRule
import           Term.Unification

import           Utils.Misc

import           Control.Basics
import           Control.Monad.Reader

import           Data.List
import qualified Data.Set             as S

import           System.IO.Unsafe     (unsafePerformIO)

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


-- | @nfViaHaskell t@ returns @True@ if the term @t@ is in normal form.
nfViaHaskell :: LNTerm -> WithMaude Bool
nfViaHaskell t0 = reader $ \hnd -> check hnd
  where
    check hnd = go t0
      where
        go t = case viewTerm2 t of
            -- irreducible function symbols
            FAppNonAC o ts | o `S.member` irreducible -> all go ts
            FList ts                                  -> all go ts
            FPair t1 t2                               -> go t1 && go t2
            One                                       -> True
--            Empty                                     -> True
            Zero                                      -> True
            Lit2 _                                    -> True
            -- subterm rules
            FAppNonAC _ _ | setAny (struleApplicable t) strules     -> False
            -- exponentiation
            FExp (viewTerm2 -> FExp _ _) _                  | dh -> False
            FExp _                       (viewTerm2 -> One) | dh -> False
            -- inverses
            FInv (viewTerm2 -> FInv _)   | dh                     -> False
            FInv (viewTerm2 -> FMult ts) | dh && any isInverse ts -> False
            FInv (viewTerm2 -> One)      | dh                     -> False
            -- multiplication
            FMult ts | fAppOne `elem` ts  || any isProduct ts || invalidMult ts   -> False
            -- xor
            FXor ts | fAppZero `elem` ts || any isXor ts || not (noDuplicates ts) -> False
            -- multiset union
--            FUnion ts | fAppEmpty `elem` ts || any isUnion ts                     -> False

            -- topmost position not reducible, check subterms
            FExp        t1 t2 -> go t1 && go t2
            FInv        t1    -> go t1
            FMult       ts    -> all go ts
            FXor        ts    -> all go ts
            FUnion      ts    -> all go ts
            FAppNonAC _ ts    -> all go ts

        struleApplicable t (StRule lhs rhs) =
            case solveMatchLNTerm (t `matchWith` lhs) `runReader` hnd of
              []  -> False
              _:_ -> case rhs of
                       RhsPosition _ -> True
                       RhsGround   s -> not (t == s)
                           -- reducible, but RHS might be already equal to t

        invalidMult ts = case partition isInverse ts of
            ([],_)     -> False
            ([ viewTerm2 -> FInv (viewTerm2 -> FMult ifactors) ], factors) ->
                (ifactors \\ factors /= ifactors) || (factors \\ ifactors /= factors)
            ([ viewTerm2 -> FInv t ], factors) -> t `elem` factors
            (_:_:_, _) -> True
            _          -> False

        msig        = mhMaudeSig hnd
        strules     = stRules msig
        irreducible = irreducibleFunctionSymbols msig
        dh          = enableDH msig


-- | @nf' t@ returns @True@ if the term @t@ is in normal form.
nf' :: LNTerm -> WithMaude Bool
nf' = nfViaHaskell

-- | @nfViaMaude t@ returns @True@ if the term @t@ is in normal form.
nfViaMaude :: (Show (Lit c LVar), Ord c, IsConst c)
           => (c -> LSort) -> LTerm c -> WithMaude Bool
nfViaMaude sortOf t = (t ==) <$> norm sortOf t


-- | @nfCompare t@ performs normal-form checks using maude and the haskell function
--   and fails if the results differ.
_nfCompare' :: LNTerm -> WithMaude Bool
_nfCompare' t0 = reader $ \hnd ->
    case ((nfViaMaude sortOfName t0) `runReader` hnd, (nfViaHaskell t0) `runReader` hnd) of
        (x, y) | x == y -> x
        (x, y) ->
          error $ "nfCompare: Maude disagrees with haskell nf: "++ show t0
                  ++" maude: " ++ show x ++ " haskell: "++show y


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
  where irreducible = irreducibleFunctionSymbols msig
        go (viewTerm -> Lit _)                                        = []
        go (viewTerm -> FApp (NonAC o) as) | o `S.member` irreducible = concatMap go as
        go t                                                          = [t]
