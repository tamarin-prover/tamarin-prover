{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving, TypeSynonymInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2011, 2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
-- Ensuring consistency of a constraint system (sequent) with guarded trace
-- formulas.
module Theory.Proof.SolveGuarded (
    saturateGuarded
  , openDisjunctionGoals
  , openImplicationGoals

  -- * Literal formula constants
  , gfalse
  ) where

import           Theory.Proof.Guarded
import           Theory.Atom
import           Term.LTerm

import           Theory.Proof.Types

import           Data.Typeable
import           Data.Data
import           Data.Maybe (catMaybes)
import qualified Data.Set as S

import           Control.Basics
import           Control.Monad.State hiding (get)
import           Control.Monad.Fresh
import           Control.Monad.Reader

import           Extension.Data.Label

-- Terms, facts, and formulas with skolem constants
---------------------------------------------------

-- | A constant type that supports names and skolem constants.
data SkConst = SkName  Name
             | SkConst LVar
             deriving( Eq, Ord, Show, Data, Typeable )

type SkTerm    = VTerm SkConst LVar
type SkFact    = Fact SkTerm
type SkSubst   = Subst SkConst LVar
type SkGuarded = LGuarded SkConst

-- | A term with skolem constants and bound variables
type BSkTerm   = VTerm SkConst BLVar

-- | An term with skolem constants and bound variables
type BSkAtom   = Atom BSkTerm

instance IsConst SkConst

-- | @saturateGuarded seq@ returns @Nothing@ if @sFormulas seq@ is already
-- saturated and saturated it otherwise. Additionally, the equalities in the
-- saturation are removed and returned separately. @sSolvedFormulas seq@ is
-- used to determine which formulas are considered 'solved'.
saturateGuarded :: MonadFresh m
                => MaudeHandle
                -> Sequent
                -> m (Maybe ([Equal LNTerm], Sequent))
                   -- ^ return the new solved, unsolved, and equalities sets
saturateGuarded hnd se0 = do
    (eqs, se) <- (`runStateT` se0) $ do
        do existentials <- S.filter isExGuarded <$> getM sFormulas
           newExs       <- mapM solveExistential $ S.toList existentials
           modM sFormulas       (S.union $ S.fromList newExs)
           modM sSolvedFormulas (S.union existentials)

        do conjs <- S.filter isConjunction <$> getM sFormulas
           let newConjs = [ gf | GConj (Conj gfs) <- S.toList conjs, gf <- gfs ]
           modM sFormulas       (S.union $ S.fromList newConjs)
           modM sSolvedFormulas (S.union conjs)

        do gfs  <- S.toList <$> getM sFormulas
           lems <- S.toList <$> getM sLemmas
           let clauses = filter isAllGuarded $ gfs ++ lems
               newSuccs = [ gf | cl <- clauses
                               , gf <- solveImplication hnd se0 cl ]
           modM sFormulas (S.union $ S.fromList newSuccs)

        -- solve all atoms in guarded formulas by moving them to the graph
        fms <- S.toList <$> getM sFormulas
        eqs <- fmap catMaybes $ forM fms $ \fm -> case fm of
          GAto ato -> do
            modM sSolvedFormulas (S.insert fm)
            case bvarToLVar ato of
              EqE s t -- only add non-trivial equalities
                | not (s == t) -> return $ Just $ Equal s t
                | otherwise     -> return Nothing
              EdgeA (viewTerm -> Lit (Var i), v) (viewTerm -> Lit (Var j), u) -> do
                modM sEdges $ S.insert $ Edge (i, v) (j, u)
                return Nothing
              EdgeA _ _ ->
                error $ "saturateGuarded: ill-formed edge atom: " ++ show ato
              ato' ->
                modM sAtoms (S.insert ato') >> return Nothing

          _ -> return Nothing

        -- remove solved formulas from open formulas.
        solved <- getM sSolvedFormulas
        modM sFormulas (`S.difference` solved)

        -- return new equality and less atoms
        return eqs

    -- check if there was a change.
    if (null eqs && get sFormulas       se0 == get sFormulas       se
                 && get sSolvedFormulas se0 == get sSolvedFormulas se)
      then return Nothing
      else return (Just (eqs, se))

-- | @solveExistential ex@ converts the existentially quantified variables into
-- free variables.
solveExistential :: MonadFresh m => LNGuarded -> m LNGuarded
solveExistential gf0 = do
  Just (_, gf) <- openExGuarded gf0
  return gf

-- | @solveImplication se imp@ returns the list of guarded formulas that are
-- implied by @se@.
solveImplication :: MaudeHandle -> Sequent -> LNGuarded -> [LNGuarded]
solveImplication hnd se gf = 
    map (unskolemizeLNGuarded . flip applySkGuarded suc) substs
  where
   (suc,substs) = satisfyingSubsts hnd se gf

-- | @satisfyingSubsts se gf@ returns all satisfying substitutions for the
-- antecedent of gf. This function expects a clause gf and fails with an error
-- otherwise.
satisfyingSubsts :: MaudeHandle -> Sequent -> LNGuarded -> (SkGuarded, [SkSubst])
satisfyingSubsts hnd se gf0 =
    ( succedent
    , candidateSubsts emptySubst [ (i,f) | (Action i f) <- antecedent ]
    )
  where
    -- skolemize and open guarded all-quantification
    gf                                = skolemizeGuarded gf0
    Just (_ss, antecedent, succedent) = openAllGuarded gf `evalFresh` avoid gf

    -- the actions present in the sequent
    sequentActions = 
        ((skolemizeTerm . varTerm) *** skolemizeFact) <$> sActions se

    -- candidate substitutions such that the antecedent is implied by @se@
    candidateSubsts subst []     = do
        guard (all (atomHolds subst) antecedent) 
        return subst
    candidateSubsts subst (a:as) = do
        seAct  <- sequentActions
        subst' <- (`runReader` hnd) $ matchAction seAct (applySkAction subst a)
        candidateSubsts (compose subst' subst) as
  
    -- cache predicates
    dedBefore = deducibleBefore se
    hapBefore = happensBefore se

    atomHolds subst ato = case unskolemizeTerm . applySkTerm subst <$> ato of
        Action _ _                                               -> True     -- correct by construction
        EqE t s                                                  -> t == s   -- compare terms modulo AC
        Last i                                                   -> Last i `S.member` get sAtoms se
        DedBefore t (viewTerm -> Lit (Var i))                    -> t `dedBefore` i
        Less (viewTerm -> Lit (Var i)) (viewTerm -> Lit (Var j)) -> i `hapBefore` j
        EdgeA (viewTerm -> Lit (Var i), v) (viewTerm -> Lit (Var j), u) -> 
            Edge (i, v) (j, u) `S.member` get sEdges se
        -- play it safe and sound: all other atoms don't hold
        _                                                        -> False


-- Find open goals
------------------

-- | All open disjunction goals.
--
-- We assume that solved formulas have been removed from sFormulas
openDisjunctionGoals :: Sequent -> [Goal]
openDisjunctionGoals se = do
  GDisj d <- filter (/= gfalse) $ S.toList $ get sFormulas se
  return $ DisjG d

-- | Consequents of clauses that could be added to the sequent.
openImplicationGoals :: MaudeHandle -> Sequent -> [Goal]
openImplicationGoals hnd se = do
    clause <- filter isAllGuarded $ S.toList $ get sFormulas se
    conseq <- solveImplication hnd se clause
    guard $ 
        all (conseq `S.notMember`) [get sSolvedFormulas se, get sFormulas se]
    return $ ImplG conseq


-- Skolemization of terms without bound variables.
-------------------------------------------------- skolemizeTerm :: VTerm Name LVar -> SkTerm

skolemizeTerm :: LNTerm -> SkTerm
skolemizeTerm = fmapTerm conv
 where
  conv :: Lit Name LVar -> Lit SkConst LVar
  conv (Var v) = Con (SkConst v)
  conv (Con n) = Con (SkName n)

skolemizeFact :: LNFact -> Fact SkTerm
skolemizeFact = fmap skolemizeTerm

skolemizeAtom :: BLAtom -> BSkAtom
skolemizeAtom = fmap skolemizeBTerm

skolemizeGuarded :: LNGuarded -> SkGuarded
skolemizeGuarded = mapGuardedAtoms (const skolemizeAtom)

unskolemizeTerm :: SkTerm -> VTerm Name LVar
unskolemizeTerm t = fmapTerm conv t
 where
  conv :: Lit SkConst LVar -> Lit Name LVar
  conv (Con (SkConst x)) = Var x
  conv (Var v)           = error $ "unskolemizeBTerm: free variable " ++
                                   show v++" found in "++show t
  conv (Con (SkName n))  = Con n

applySkTerm :: SkSubst -> SkTerm -> SkTerm
applySkTerm subst t = applyVTerm subst t

applySkFact :: SkSubst -> SkFact -> SkFact
applySkFact subst = fmap (applySkTerm subst) 

applySkAction :: SkSubst -> (SkTerm,SkFact) -> (SkTerm,SkFact)
applySkAction subst (t,f) = (applySkTerm subst t, applySkFact subst f)


-- Skolemization of terms wit bound variables.
----------------------------------------------

skolemizeBTerm :: VTerm Name BLVar -> BSkTerm
skolemizeBTerm = fmapTerm conv
 where
  conv :: Lit Name BLVar -> Lit SkConst BLVar
  conv (Var (Free x))  = Con (SkConst x)
  conv (Var (Bound b)) = Var (Bound b)
  conv (Con n)         = Con (SkName n)

unskolemizeBTerm :: BSkTerm -> VTerm Name BLVar
unskolemizeBTerm t = fmapTerm conv t
 where
  conv :: Lit SkConst BLVar -> Lit Name BLVar
  conv (Con (SkConst x)) = Var (Free x)
  conv (Var (Bound b))   = Var (Bound b)
  conv (Var (Free v))    = error $ "unskolemizeBTerm: free variable " ++
                                   show v++" found in "++show t
  conv (Con (SkName n))  = Con n

unskolemizeBLAtom :: BSkAtom -> BLAtom
unskolemizeBLAtom = fmap unskolemizeBTerm

unskolemizeLNGuarded :: SkGuarded -> LNGuarded
unskolemizeLNGuarded = mapGuardedAtoms (const unskolemizeBLAtom)

applyBSkTerm :: SkSubst -> VTerm SkConst BLVar -> VTerm SkConst BLVar
applyBSkTerm subst t = go t
      where
        go (viewTerm -> Lit l)     = applyBLLit l
        go (viewTerm -> FApp o as) = fApp o (map go as)
        applyBLLit :: Lit SkConst BLVar -> VTerm SkConst BLVar
        applyBLLit l@(Var (Free v)) =
            maybe (lit l) (fmapTerm (fmap Free)) (imageOf subst v)
        applyBLLit l                = lit l

applyBSkAtom :: SkSubst -> Atom (VTerm SkConst BLVar) -> Atom (VTerm SkConst BLVar)
applyBSkAtom subst = fmap (applyBSkTerm subst)

applySkGuarded :: SkSubst -> LGuarded SkConst -> LGuarded SkConst
applySkGuarded subst = mapGuardedAtoms (const $ applyBSkAtom subst)

-- Matching
-----------

matchAction :: (SkTerm, SkFact) ->  (SkTerm, SkFact) -> WithMaude [SkSubst]
matchAction (i1,Fact f1 t1) (i2,Fact f2 t2)
  | f1 == f2 && length t1 == length t2
  = matchLTerm sortOfSkol (zipWith MatchWith (i1:t1) (i2:t2))
  | otherwise = return []
 where
  sortOfSkol (SkName  n)  = sortOfName n
  sortOfSkol (SkConst v)  = lvarSort v


{-
-- Test
-------

parseFormula = get lFormulaE . either (error "parsing failed") id . parseLemma

t1 = parseFormula
       "lemma test1:\
        \ \"\
        \ All y z #i #j. (A(y)@#j & B(z)@#i) ==> (C(y,z) @ #i) & (D(y,z) @ #j) \
        \ \""

t2 = parseFormula
       "lemma test1:\
        \ \"\
        \ All y #i #j. (A(y)@#j & B(y1)@#i) ==> (C(y) @ #i) & (D(y) @ #j) \
        \ \""

--        \  All x #i.  A(x)@i ==> Ex y #j. B(y)@j\


gas = [(skolemizeTerm $ i1, skolemizeFact $ Fact (ProtoFact "A") [y1]),
       (skolemizeTerm $ i1, skolemizeFact $ Fact (ProtoFact "B") [y1]),
       (skolemizeTerm $ i2, skolemizeFact $ Fact (ProtoFact "B") [y3])
      ]

t1_g = fromJust $ convert False t1
t2_g = fromJust $ convert False t2

t3 = putStrLn $ render $ prettyGuarded $ t1_g

t4 = mapM_ (putStrLn . render . prettyGuarded) $ solveImplication t1_g gas
-}
