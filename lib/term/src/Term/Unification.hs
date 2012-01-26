{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Term.Unification (
  -- * Unification modulo AC
    unifyLTerm
  , unifyLNTerm

  -- * matching modulo AC
  , matchLTerm
  , matchLNTerm

  , unifyLTermFactored
  , unifyLNTermFactored

  -- * Handles to a Maude process
  , MaudeHandle
  , WithMaude
  , startMaude
  , getMaudeStats
  , mhMaudeSig
  , mhFilePath

  -- * Maude signatures
  , MaudeSig(..)
  , emptyMaudeSig
  , dhMaudeSig
  , xorMaudeSig
  , msetMaudeSig
  , pairMaudeSig
  , symEncMaudeSig
  , asymEncMaudeSig
  , signatureMaudeSig
  , hashMaudeSig
  , allMaudeSig
  , rrulesForMaudeSig
  , funSigForMaudeSig


  -- * Convenience exports
  , module Term.Substitution
) where

import           Control.Applicative
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.Error
import           Control.Monad.State
import           Data.List
import qualified Data.Map as M
import           Data.Map (Map)

import           System.IO.Unsafe (unsafePerformIO)

import           Term.Rewriting.NormAC ( (==#) )
import           Term.Substitution
import qualified Term.Maude.Process as UM
import           Term.Maude.Process
                   (MaudeHandle, WithMaude, startMaude, getMaudeStats, mhMaudeSig, mhFilePath)
import           Term.Maude.Types
                   (MaudeSig(..), emptyMaudeSig, allMaudeSig, rrulesForMaudeSig,
                    funSigForMaudeSig, dhMaudeSig, xorMaudeSig, msetMaudeSig,
                    pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig,
                    hashMaudeSig)

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
unifyLNTerm = unifyLTerm sortOfName


-- | Flatten a factored substitution to a list of substitutions.
flattenUnif :: IsConst c => (LSubst c, [LSubstVFresh c]) -> [LSubstVFresh c]
flattenUnif (subst, substs) =  (\res -> trace (show ("flattenUnif",subst, substs,res )) res) $ map (`composeVFresh` subst) substs

-- Matching modulo AC
----------------------------------------------------------------------


-- | @matchLNTerm sortOf eqs@ returns a complete set of matchers for @eqs@ modulo AC.
matchLTerm :: (IsConst c , Show (Lit c LVar), Ord c)
           => (c -> LSort)
           -> [Match (LTerm c)]
           -> WithMaude [Subst c LVar]
matchLTerm sortOf eqs =
    reader $ \h -> (\res -> trace (unlines $ ["matchLTerm: "++ show eqs, "result = "++  show res]) res) $
        case runState (runErrorT match) M.empty of
          (Left NoMatch,_)    -> []
          (Left ACProblem, _) -> unsafePerformIO (UM.matchViaMaude h sortOf eqs)
          (Right _, mappings) -> [substFromMap mappings]
  where
    match = sequence [ matchRaw sortOf t p | MatchWith t p <- eqs ]


-- | @matchLNTerm eqs@ returns a complete set of matchers for @eqs@ modulo AC.
matchLNTerm :: [Match LNTerm] -> WithMaude [Subst Name LVar]
matchLNTerm = matchLTerm sortOfName

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
    case (l, r) of
       (Lit (Var vl), Lit (Var vr))
         | vl == vr  -> return ()
         | otherwise -> case (lvarSort vl, lvarSort vr) of
             (sl, sr) | sl == sr                 -> if vl < vr then elim vr l 
                                                    else elim vl r
             _        | sortGeqLTerm sortOf vl r -> elim vl r
             -- If unification can succeed here, then it must work by
             -- elimating the right-hand variable with the left-hand side.
             _                                     -> elim vr l

       (Lit (Var vl),  _            ) -> elim vl r
       (_,             Lit (Var vr) ) -> elim vr l
       (Lit (Con cl),  Lit (Con cr) ) -> guard (cl == cr)
       (FApp (NonAC lfsym) largs, FApp (NonAC rfsym) rargs) ->
           guard (lfsym == rfsym && length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       (FApp List largs, FApp List rargs) ->
           guard (length largs == length rargs)
           >> sequence_ (zipWith unifyRaw largs rargs)
       -- NOTE: We assume here that terms of the form mult(t) =AC t never occur.
       (FApp (AC _) _, FApp (AC _) _) -> tell [Equal l r]  -- delay unification

       -- all unifiable pairs of term constructors have been enumerated
       _                      -> mzero -- no unifier
  where
    elim v t 
      | v `occurs` t = mzero -- no unifier
      | otherwise    = do
          sortOf <- ask
          guard  (sortGeqLTerm sortOf v t)
          modify (M.insert v t . M.map (applyVTerm (substFromList [(v,t)])))


data MatchFailure = NoMatch | ACProblem

instance Error MatchFailure where
    strMsg _ = NoMatch

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
      (_, Lit (Var vp)) ->
          case M.lookup vp mappings of
              Nothing             -> do
                unless (sortGeqLTerm sortOf vp t) $
                    throwError NoMatch
                modify (M.insert vp t)
              Just tp | t ==# tp  -> return ()
                      | otherwise -> throwError NoMatch

      (Lit (Con ct),  Lit (Con cp)) -> guard (ct == cp)
      (FApp (NonAC tfsym) targs, FApp (NonAC pfsym) pargs) ->
           guard (tfsym == pfsym && length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (FApp List targs, FApp List pargs) ->
           guard (length targs == length pargs)
           >> sequence_ (zipWith (matchRaw sortOf) targs pargs)
      (FApp (AC _) _, FApp (AC _) _) -> throwError ACProblem

      -- all matchable pairs of term constructors have been enumerated
      _                      -> throwError NoMatch


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