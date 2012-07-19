{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, ViewPatterns #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- AC unification based on maude and free unification.
module Term.Unification (
  -- * Unification modulo AC
    unifyLTerm
  , unifyLNTerm
  , unifiableLNTerms

  , unifyLTermFactored
  , unifyLNTermFactored

  -- * matching modulo AC
  -- ** Constructing matching problems
  , matchLVar

  -- ** Solving matching problems
  , solveMatchLTerm
  , solveMatchLNTerm

  -- * Handles to a Maude process
  , MaudeHandle
  , WithMaude
  , startMaude
  , getMaudeStats
  , mhMaudeSig
  , mhFilePath

  -- * Maude signatures
  , MaudeSig
  , enableDH
  , enableXor
  , enableMultiset
  , minimalMaudeSig
  , dhMaudeSig
  , xorMaudeSig
  , msetMaudeSig
  , pairMaudeSig
  , symEncMaudeSig
  , asymEncMaudeSig
  , signatureMaudeSig
  , hashMaudeSig
  , rrulesForMaudeSig
  , allFunctionSymbols
  , stRules
  , irreducibleFunctionSymbols
  , addFunctionSymbol
  , addStRule

  -- * Convenience exports
  , module Term.Substitution
  , module Term.Rewriting.Definitions
) where

import           Control.Applicative
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.Error
import           Control.Monad.State
import qualified Data.Map as M
import           Data.Map (Map)

import           System.IO.Unsafe (unsafePerformIO)

import           Term.Rewriting.Definitions
import           Term.Substitution
import qualified Term.Maude.Process as UM
import           Term.Maude.Process
                   (MaudeHandle, WithMaude, startMaude, getMaudeStats, mhMaudeSig, mhFilePath)
import           Term.Maude.Signature
import           Debug.Trace.Ignore
-- import qualified Debug.Trace as DT

-- Unification modulo AC
----------------------------------------------------------------------

-- | @unifyLTerm sortOf eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLTermFactored :: (IsConst c , Show (Lit c LVar), Ord c)
                   => (c -> LSort)
                   -> [Equal (LTerm c)]
                   -> WithMaude (LSubst c, [SubstVFresh c LVar])
unifyLTermFactored sortOf eqs = reader $ \h -> (\res -> trace (unlines $ ["unifyLTerm: "++ show eqs, "result = "++  show res]) res) $ do
    solve h $ execRWST unif sortOf M.empty
  where
    unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
    solve _ Nothing         = (emptySubst, [])
    solve _ (Just (m, []))  = (substFromMap m, [emptySubstVFresh])
    solve h (Just (m, leqs)) =
        (subst, unsafePerformIO (UM.unifyViaMaude h sortOf $
                                     map (applyVTerm subst <$>) leqs))
      where subst = substFromMap m


-- | @unifyLTerm sortOf eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLNTermFactored :: [Equal LNTerm]
                    -> WithMaude (LNSubst, [SubstVFresh Name LVar])
unifyLNTermFactored = unifyLTermFactored sortOfName

-- | @unifyLNTerm eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLTerm :: (IsConst c , Show (Lit c LVar), Ord c)
           => (c -> LSort)
           -> [Equal (LTerm c)]
           -> WithMaude [SubstVFresh c LVar]
unifyLTerm sortOf eqs = flattenUnif <$> unifyLTermFactored sortOf eqs


-- | @unifyLNTerm eqs@ returns a complete set of unifiers for @eqs@ modulo AC.
unifyLNTerm :: [Equal LNTerm] -> WithMaude [SubstVFresh Name LVar]
-- unifyLNTerm eqs = reader $ \hnd -> (\res -> DT.trace (show ("unify", res, eqs)) res) $ unifyLTerm sortOfName eqs `runReader` hnd
unifyLNTerm = unifyLTerm sortOfName

-- | 'True' iff the terms are unifiable.
unifiableLNTerms :: LNTerm -> LNTerm -> WithMaude Bool
unifiableLNTerms t1 t2 = (not . null) <$> unifyLNTerm [Equal t1 t2]

-- | Flatten a factored substitution to a list of substitutions.
flattenUnif :: IsConst c => (LSubst c, [LSubstVFresh c]) -> [LSubstVFresh c]
flattenUnif (subst, substs) =  (\res -> trace (show ("flattenUnif",subst, substs,res )) res) $ map (`composeVFresh` subst) substs

-- Matching modulo AC
----------------------------------------------------------------------

-- | Match an 'LVar' term to an 'LVar' pattern.
matchLVar :: LVar -> LVar -> Match (LTerm c)
matchLVar t p = varTerm t `matchWith` varTerm p

-- | @solveMatchLNTerm sortOf eqs@ returns a complete set of matchers for
-- @eqs@ modulo AC.
solveMatchLTerm :: (IsConst c , Show (Lit c LVar), Ord c)
           => (c -> LSort)
           -> Match (LTerm c)
           -> WithMaude [Subst c LVar]
solveMatchLTerm sortOf matchProblem =
    case flattenMatch matchProblem of
      Nothing -> pure []
      Just ms -> reader $ matchTerms ms
  where
    trace' res = trace
      (unlines $ ["matchLTerm: "++ show matchProblem, "result = "++  show res])
      res

    matchTerms ms hnd =
        trace' $ case runState (runErrorT match) M.empty of
          (Left NoMatcher, _)  -> []
          (Left ACProblem, _)  ->
              unsafePerformIO (UM.matchViaMaude hnd sortOf matchProblem)
          (Right (), mappings) -> [substFromMap mappings]
      where
        match = forM_ ms $ \(t, p) -> matchRaw sortOf t p


-- | @solveMatchLNTerm eqs@ returns a complete set of matchers for @eqs@
-- modulo AC.
solveMatchLNTerm :: Match LNTerm -> WithMaude [Subst Name LVar]
solveMatchLNTerm = solveMatchLTerm sortOfName

-- Free unification with lazy AC-equation solving.
--------------------------------------------------------------------

type UnifyRaw c = RWST (c -> LSort) [Equal (LTerm c)] (Map LVar (VTerm c LVar)) Maybe

-- | Unify two 'LTerm's with delayed AC-unification.
unifyRaw :: IsConst c => LTerm c -> LTerm c -> UnifyRaw c ()
unifyRaw l0 r0 = do
    mappings <- get
    sortOf <- ask
    l <- gets ((`applyVTerm` l0) . substFromMap)
    r <- gets ((`applyVTerm` r0) . substFromMap)
    guard (trace (show ("unifyRaw", mappings, l ,r)) True)
    case (viewTerm l, viewTerm r) of
       (Lit (Var vl), Lit (Var vr))
         | vl == vr  -> return ()
         | otherwise -> case (lvarSort vl, lvarSort vr) of
             (sl, sr) | sl == sr                 -> if vl < vr then elim vr l
                                                    else elim vl r
             _        | sortGeqLTerm sortOf vl r -> elim vl r
             -- If unification can succeed here, then it must work by
             -- elimating the right-hand variable with the left-hand side.
             _                                   -> elim vr l

       (Lit (Var vl),  _            ) -> elim vl r
       (_,             Lit (Var vr) ) -> elim vr l
       (Lit (Con cl),  Lit (Con cr) ) -> guard (cl == cr)
       (FApp (NonAC lfsym) largs, FApp (NonAC rfsym) rargs) ->
           guard (lfsym == rfsym && length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       (FApp List largs, FApp List rargs) ->
           guard (length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       -- NOTE: We assume here that terms of the form mult(t) never occur.
       (FApp (AC lacsym) _, FApp (AC racsym) _) ->
           guard (lacsym == racsym) >> tell [Equal l r]  -- delay unification

       -- all unifiable pairs of term constructors have been enumerated
       _                      -> mzero -- no unifier
  where
    elim v t
      | v `occurs` t = mzero -- no unifier
      | otherwise    = do
          sortOf <- ask
          guard  (sortGeqLTerm sortOf v t)
          modify (M.insert v t . M.map (applyVTerm (substFromList [(v,t)])))


data MatchFailure = NoMatcher | ACProblem

instance Error MatchFailure where
    strMsg _ = NoMatcher

-- | Ensure that the computed substitution @sigma@ satisfies
-- @t ==_AC apply sigma p@ after the delayed equations are solved.
matchRaw :: IsConst c
         => (c -> LSort)
         -> LTerm c -- ^ Term @t@
         -> LTerm c -- ^ Pattern @p@.
         -> ErrorT MatchFailure (State (Map LVar (VTerm c LVar))) ()
matchRaw sortOf t p = do
    mappings <- get
    guard (trace (show (mappings,t,p)) True)
    case (t, p) of
      (_, viewTerm -> Lit (Var vp)) ->
          case M.lookup vp mappings of
              Nothing             -> do
                unless (sortGeqLTerm sortOf vp t) $
                    throwError NoMatcher
                modify (M.insert vp t)
              Just tp | t == tp  -> return ()
                      | otherwise -> throwError NoMatcher

      (viewTerm -> Lit (Con ct),  viewTerm -> Lit (Con cp)) -> guard (ct == cp)
      (viewTerm -> FApp (NonAC tfsym) targs, viewTerm -> FApp (NonAC pfsym) pargs) ->
           guard (tfsym == pfsym && length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (viewTerm -> FApp List targs, viewTerm -> FApp List pargs) ->
           guard (length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (viewTerm -> FApp (AC _) _, viewTerm -> FApp (AC _) _) -> throwError ACProblem

      -- all matchable pairs of term constructors have been enumerated
      _                      -> throwError NoMatcher


-- | @sortGreaterEq v t@ returns @True@ if the sort ensures that the sort of @v@ is greater or equal to
--   the sort of @t@.
sortGeqLTerm :: IsConst c => (c -> LSort) -> LVar -> LTerm c -> Bool
sortGeqLTerm st v t = do
    case (lvarSort v, sortOfLTerm st t) of
        (s1, s2) | s1 == s2     -> True
        -- Node is incomparable to all other sorts, invalid input
        (LSortNode,  _        ) -> errNodeSort
        (_,          LSortNode) -> errNodeSort
        (s1, s2)                -> sortCompare s1 s2 `elem` [Just EQ, Just GT]
  where
    errNodeSort = error $
        "sortGeqLTerm: node sort misuse " ++ show v ++ " -> " ++ show t
