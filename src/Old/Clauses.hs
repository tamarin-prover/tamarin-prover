{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, TemplateHaskell #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Support for reasoning with and about constrained clauses.
module Theory.Proof.Clauses (

  -- * Queries on generalized atoms
    generalAtom

  -- * Queries on constrained clauses
  , generalized
  , trivialConstraints

  -- ** Construction
  , clauseFromFormula
  , clauseFromLemma

  -- * Simple prove queries on sequents
  , rawLessRel
  , rawReverseLessRel
  , proveLess
  , proveCyclic

  -- * Unification of clauses with the graph part of the sequent
  , ClConst(..)
  , ClTerm
  , ClSubst
  , proveCoveredGraphClause
  , resolveCoveredGraphClause

  -- * Lemmas
  , usableLemma

  ) where

import Prelude hiding (negate)

import Safe
import Data.Maybe
import Data.List                 as L
import qualified Data.Set        as S
import qualified Data.Map        as M
import qualified Data.DAG.Simple as D
import Data.Traversable as T (mapM)
import Data.Foldable    as F (any, all)
import Data.Label
import Data.Generics (Data, Typeable)

import Control.Basics
import Control.Monad.State hiding (get, modify)
import qualified Control.Monad.State as MS
import Control.Monad.Writer (runWriterT, WriterT, tell)
import Control.Monad.Bind
import Control.Monad.Disj

import Extension.Prelude

import Theory.Proof.Types

----------------------------------------------------------------------
-- Generalized atoms
----------------------------------------------------------------------

-- | True iff the constrained atom is an arbitrary formula.
generalAtom :: CAtom -> Bool
generalAtom (CFormula _) = True
generalAtom (CAtom _)    = False


----------------------------------------------------------------------
-- Constrained Clauses
----------------------------------------------------------------------


-- Queries
----------

-- | @generalized cl@ iff @cl@ contains an arbitrary formula as an atom.
generalized :: CClause -> Bool
generalized cl = 
    F.any generalAtom (get cAnte cl) || 
    F.any generalAtom (get cSucc cl)

-- | @trivialConstraints cl@ iff all constraints of @cl@ map an existential
-- variable to a single universal variable.
trivialConstraints :: CClause -> Bool
trivialConstraints =
    L.all check . substToList . get cConstrs
  where
    check (_, Lit (Var (LVar _ _ _))) = True
    check _                           = False

-- | True iff the clause has a succedent that could possibly be used to enrich
-- the graph part of a sequent; i.e., has the form
--
-- > constrs || ante ==> Ex x1..xk. ato1 /\ .. /\ aton
--
-- with @frees(succ) <= frees(ante) `union` frees(constrs)@.
--
-- Note that the above form includes the case of an empty succedent.
--
hasCoveredGraphSuccedent :: CClause -> Bool
hasCoveredGraphSuccedent (CClause constrs ant suc) = 
    checkSucc (getDisj suc) && 
    L.all (`S.member` covered) (freesList suc)
  where
    covered = S.fromList $ varsRange constrs ++ freesList ant

    checkSucc []            = True
    checkSucc [CAtom _]     = True
    checkSucc [CFormula fm] = checkFormula fm
    checkSucc _             = False

    checkFormula (Qua Ex _ fm) = checkFormula fm
    checkFormula fm            = F.all isAtom $ toplevelConjs fm

    isAtom (Ato _) = True
    isAtom _       = False

-- | True iff converting the lemma to a clause yields a 'usableClause'.
-- | True iff the clause is usable for the under-approximation to first-order
-- logic reasoning we are currentlye using; i.e., trie to directly derive the
-- empty clause or extend the graph part with a previously unprovable atom.
usableLemma :: LFormula -> Bool
usableLemma = hasCoveredGraphSuccedent . clauseFromLemma


-- Construction
---------------

-- | Convert a formula @fm@ of the form
--
-- > fm = All x1..xk. not(a1) \/ .. \/ not(an) \/ s1 \/ .. \/ sm
--
-- to constrained clause of the form
--
-- > frees(fm) ~> freshVars || a1, ..., an ==> s1, ..., sm
--
clauseFromFormula :: LFormula -> CClause
clauseFromFormula fm0 = 
    (`evalFresh` nothingUsed) $ do
        let absFree v = ((,) v . Lit . Var) <$> freshLVar (lvarName v) (lvarSort v)
        subst0 <- T.mapM absFree (frees fm0)
        let fm = apply (substFromList VFree subst0) fm0
        -- We need to use a VFresh substitution, as otherwise renamings would
        -- be removed, which does not correspond to our intended semantics.
        go (substFromList VFresh subst0) fm
  where
    go subst (Qua All hint p) = do
        v <- uncurry freshLVar hint
        go subst (unquantify v p)
    go subst fm = do
        let (ants, succs) = partition negative $ getDisj $ toplevelDisjs fm
        return $ CClause subst (Conj $ map (mkAtom . negate) ants ) 
                               (Disj $ map mkAtom            succs) 

    mkAtom (Ato a) = CAtom $ freeFreeBLAtom a
    mkAtom fm      = CFormula fm

-- | Convert a lemma to a clause, where a lemma is a formula with all free
-- variables being implicitly universally quantified.
clauseFromLemma :: LFormula -> CClause
clauseFromLemma = clauseFromFormula . universalClosure (lvarName &&& lvarSort)


------------------------------------------------------------------------------
-- Prove queries on sequents
------------------------------------------------------------------------------

-- | @(from,to)@ is in @rawLessRel se@ iff we can prove that there is a path
-- from @from@ to @to@ in @se@ without appealing to transitivity.
rawLessRel :: Sequent -> [(NodeId,NodeId)]
rawLessRel se = 
    [ (from, nodePremNode prem) 
    | Edge (NodeConc (from,_)) prem <- S.toList $ get sEdges se ]
    ++
    [ (from, to) | SeLess from to <- S.toList $ get sLess se ]
    ++
    [ (nodeConcNode from, nodePremNode prem) 
    | Chain from prem <- S.toList $ get sChains se ]

-- | @(to,from)@ is in @rawRevLessRel se@ iff we can prove that there is a path
-- from @from@ to @to@ in @se@ without appealing to transitivity.
rawReverseLessRel :: Sequent -> [(NodeId,NodeId)]
rawReverseLessRel = map (uncurry $ flip (,)) . rawLessRel

-- | @proveLess se from to@ under-approximates |se| ==> from >+> to.
proveLess :: Sequent -> NodeId -> NodeId -> Bool
proveLess se from to = to `S.member` D.reachableSet [from] (rawLessRel se)

{-
-- | @proveNotLess se from to@ under-approximates |se| ==> not(from >+> to)
-- using the under-approximation 
-- @(from = to \/ to >+> from) ==> not(from >+> to)@ as an intermediate step.
proveNotLess :: Sequent -> NodeId -> NodeId -> Bool
proveNotLess se from to = from == to || proveLess se to from
-}

-- | @proveCyclic se@ under-approximates @|se| ==> Ex v. v >+> v@.
proveCyclic :: Sequent -> Bool
proveCyclic = D.cyclic . rawLessRel

{-
-- | @proveProvides se v fa@ under-approximates @|se| ==> v :> fa
proveProvides :: Sequent -> NodeId -> LFact -> Bool
proveProvides se v fa =
    SeProvides v fa `S.member` sProvides se ||
    fromMaybe False ((elem fa . rConcs) <$> (v `M.lookup` sNodes se))
-}

------------------------------------------------------------------------------
-- Proving literals implied by a sequent
------------------------------------------------------------------------------

-- |The existential variables of a sequent have to be viewed as constants when
-- reasoning about the free variables of the clauses.
data ClConst = ClName Name 
             | ClExVar (String, LSort, Int)
             deriving( Eq, Ord, Show, Data, Typeable )

type ClTerm  = VTerm ClConst LVar
type ClFact  = Fact ClTerm
type ClSubst = Subst VFree ClConst LVar

instance Show (Lit ClConst LVar) where
    show (Name (ClName x))  = show x
    show (Name (ClExVar x)) = "%" ++ show (toSequentVar x)
    show (Var v)            = show v

instance IsConst ClConst where

-- | The state during proving something inside a clause. The substitution maps
-- universally quantified variables of the clause to terms with existentially
-- quantified variables of the sequent (regarded as constants) and universally
-- quantified variables of the clause.
--
-- Fresh universally quantified variables can be introduced and failure of
-- proof is modeled using the MonadPlus instance from the underlying Maybe
-- monad.
--
-- Note that before every proof step the current substitution has to be applied
-- to the problem underlying the proof step.
-- 
-- FIXME: Check why semantics of 'proveEmptyClause' disagrees when using an
-- underlying list versus an underyling maybe.
type ClProof = WriterT [Goal] (StateT ClSubst (FreshT []))

-- | @clauseTerm t@ converts the term @t@ interpreted relative to the clause
-- only, to a term that is interpreted relative to clause and the sequent.
clauseTerm :: LTerm -> ClTerm
clauseTerm = fmap conv
  where
    conv (Var x)  = Var x
    conv (Name a) = Name (ClName a)

-- | @sequentTerm t@ converts the term @t@ interpreted relative to the sequent
-- only, to a term that is interpreted relative to clause and sequent.
sequentTerm :: LTerm -> ClTerm
sequentTerm = fmap conv
  where
    conv (Var x)  = Name (fromSequentVar x)
    conv (Name a) = Name (ClName a)

-- | @fromSequentVar ev@ converts the existentially quantified variables @ev@
-- interpreted with respect to the sequent to an existentially quantified
-- variable interpreted with respect to the clause; i.e., @ev@ is regarded as a
-- constant.
fromSequentVar :: LVar -> ClConst
fromSequentVar x = ClExVar (lvarName x, lvarSort x, lvarIdx x)

-- | @toSequentVar ev@ converts an existentially quantified variable @ev@
-- interpreted with respect to a clause to a @LVar@ interpreted with respect to
-- the sequent.
toSequentVar :: (String, LSort, Int) -> LVar
toSequentVar (n,s,i) = LVar n s i

-- | @constraintEq (ex, ut)@ creates the equality associated with the
-- constraint that the existential variable @ex@ is mapped to the term with
-- universal variables @ut@.
constraintEq :: (LVar, LTerm) -> Equal ClTerm
constraintEq (ex, ut) = Equal (Lit (Name (fromSequentVar ex))) (clauseTerm ut)

-- | Tries to prove a list of term equalities using unification to find
-- instantiations of the universal variables of the clause such that the
-- equalities are satisfied.
--
proveTermEqs :: [Equal ClTerm] -> ClProof ()
proveTermEqs eqs0 = do
    eqs <- gets (\subst -> map (fmap (applyVTerm subst)) eqs0)
    -- FIXME: Handle node-identities.
    subst <- msum $ map freshToFree $ unifyVTermEqs sortOf eqs
    MS.modify (`compose` subst)
  where
    sortOf (ClName (FreshName,_)) = LSortFresh
    sortOf (ClName (PubName,_))   = LSortPub
    sortOf (ClExVar (_,lsort,_))  = lsort

-- | @proveUnivEqTerm uv t@ tries to instantiate @uv@ such that it is equal to
-- @t@.
proveUnivEqTerm :: LVar -> ClTerm -> ClProof ()
proveUnivEqTerm x t = proveTermEqs $ [Equal (Lit (Var x)) t]

-- | @proveFactEq ufact efact@ extends the current substitution such that
-- @ufact@ is mapped to @efact@ if possible.
proveFactEq :: ClFact -> ClFact -> ClProof ()
proveFactEq (Fact tag1 ts1) (Fact tag2 ts2) = do
    guard (tag1 == tag2 && length ts1 == length ts2)
    proveTermEqs $ zipWith Equal ts1 ts2

-- | @clauseNodeId uv@ applies the current substitution to the node @uv@ that
-- is interpreted local to the clause.
clauseNodeId :: LVar -> ClProof ClTerm
clauseNodeId uv = 
    fromMaybe (Lit (Var uv)) <$> (imageOf <$> MS.get <*> pure uv)

-- | @proveAtom se at@ tries to prove that there is an extension of the current
-- instantiation of the universal variables of the clause such that the sequent
-- @se@ implies the atom @at@.
--
proveAtom :: Sequent -> LAtom -> ClProof ()
proveAtom _ (EqE t1 t2) =
    -- TODO: Ensure that EqE is an equality modulo AC
    proveTermEqs $ [Equal (clauseTerm t1) (clauseTerm t2)]

proveAtom se (Less from0 to0) =
    -- clauseNodeId ensures that the current substitution is applied
    join $ prove <$> clauseNodeId from0 <*> clauseNodeId to0
  where
    -- two existentials: just check the path
    prove (Lit (Name (ClExVar efrom))) (Lit (Name (ClExVar eto))) =
        guard (proveLess se (toSequentVar efrom) (toSequentVar eto))

    -- from existential to universal: enumerate all reachable nodes
    prove (Lit (Name (ClExVar efrom))) (Lit (Var uto)) = do
        eto <- oneOfSet $ D.reachableSet [toSequentVar efrom] (rawLessRel se)
        proveUnivEqTerm uto (Lit (Name (fromSequentVar eto)))

    -- from universal to existential: enumerate all reachable nodes
    prove (Lit (Var ufrom)) (Lit (Name (ClExVar eto))) = do
        efrom <- oneOfSet $ D.reachableSet [toSequentVar eto] (rawReverseLessRel se)
        proveUnivEqTerm ufrom (Lit (Name (fromSequentVar efrom)))
    
    -- from universal to universal: bad luck: enumerate all paths 
    prove (Lit (Var ufrom)) (Lit (Var uto)) = do
        let pathrel = rawLessRel se
        efrom <- oneOfList $ M.keys $ get sNodes se
        proveUnivEqTerm ufrom (Lit (Name (fromSequentVar efrom)))
        eto <- oneOfSet $ D.reachableSet [efrom] pathrel
        proveUnivEqTerm uto (Lit (Name (fromSequentVar eto)))

    -- sort error
    prove tfrom tto = 
        nodeIsTermError $ "proveAtom path: from '" ++ show tfrom ++ 
                          "' to '" ++ show tto ++ "'"

proveAtom se (Requires uv0 ufact) = do
    (efact, eprem) <- selectNode =<< clauseNodeId uv0
    proveFactEq (clauseFact ufact) (sequentFact efact)
    -- tell [PremiseGoal efact eprem]
  where
    clauseFact = fmap clauseTerm
    sequentFact = fmap sequentTerm

    rulePrems ev ru = oneOfList $ zip prems covered
      where
        covered = NodePrem <$> zip (repeat ev) [0..length prems - 1]
        prems   = get rPrems ru

    -- existential variable was not yet mapped: enumerate all possibilities
    selectNode (Lit (Var uv)) =
        do (ev, ru) <- oneOfList $ M.toList $ get sNodes se
           proveUnivEqTerm uv (Lit (Name (fromSequentVar ev)))
           rulePrems ev ru
        {- FIXME: Check if we can reenable this case
        <|>
        do SeRequires ev efact <- oneOfSet $ get sRequires se
           proveUnivEqTerm uv (Lit (Name (fromSequentVar ev)))
           return (efact, NodePremFact ev efact)
        -}

    -- existential variable is mapped to an existential variable: lookup its
    -- rule and enumerate conclusions
    selectNode (Lit (Name (ClExVar ev))) =
        do maybe mzero (rulePrems evSe) $ M.lookup evSe $ get sNodes se
        {- FIXME: Check if we can reenable this case
        <|>
        do SeRequires ev' efact <- oneOfSet $ get sRequires se
           guard (evSe == ev')
           return (efact, NodePremFact ev' efact)
        -}
      where
        evSe = toSequentVar ev

    -- sort error
    selectNode et = 
        nodeIsTermError $ "proveAtom (Requires): '" ++ show uv0 ++ 
                          "' mapped to '" ++ show et  ++ "'"

proveAtom se (Provides uv0 ufact) = do
    (ev, efact) <- selectNode =<< clauseNodeId uv0
    proveFactEq (clauseFact ufact) (sequentFact efact)
    -- tell [ProvidesGoal (SeProvides ev efact)]
  where
    clauseFact = fmap clauseTerm
    sequentFact = fmap sequentTerm

    ruleConcs ru = oneOfList $ get rConcs ru

    -- existential variable was not yet mapped: enumerate all possibilities
    selectNode (Lit (Var uv)) =
        do (ev, ru) <- oneOfList $ M.toList $ get sNodes se
           proveUnivEqTerm uv (Lit (Name (fromSequentVar ev)))
           (,) ev <$> ruleConcs ru
        <|>
        do SeProvides ev efact <- oneOfSet $ get sProvides se
           proveUnivEqTerm uv (Lit (Name (fromSequentVar ev)))
           return (ev, efact)

    -- existential variable is mapped to an existential variable: lookup its
    -- rule and enumerate conclusions
    selectNode (Lit (Name (ClExVar ev))) =
        do efact <- maybe mzero ruleConcs $ M.lookup (toSequentVar ev) $ get sNodes se
           return (toSequentVar ev, efact)
        <|>
        do SeProvides ev' efact <- oneOfSet $ get sProvides se
           guard (toSequentVar ev == ev')
           return (ev', efact)

    -- sort error
    selectNode et = 
        nodeIsTermError $ "proveAtom (Provides): '" ++ show uv0 ++ 
                          "' mapped to '" ++ show et  ++ "'"

-- | Report a sort error occurring from a node being replaced with a
-- non-variable term.
nodeIsTermError :: String -> a
nodeIsTermError msg = error $ "node sort constraint violated in " ++ msg

-- Try to prove a 'CAtom' in the current clause proof context, if it is an
-- atom.
proveCAtom :: Sequent -> CAtom -> ClProof ()
proveCAtom se (CAtom ato)  = proveAtom se ato
proveCAtom _  (CFormula _) = mzero

-- | Try to find a clause that can be resolved against the sequent and return
-- the first resolvent.
proveCoveredGraphClause :: Sequent 
                        -> Maybe ((String, CClause), (ClSubst, Conj LAtom, [Goal]))
proveCoveredGraphClause se = headMay $ do
    namedCl   <- oneOfMap $ get sClauses se
    resolvent <- resolveCoveredGraphClause (snd namedCl) se
    return (namedCl, resolvent)

-- | @resolveCoveredGraphClause cl se@ checks that @cl@ has a succedent of the form 
-- @Ex y1..yn. ato1 /\ .. /\ atok@ such that all @atoi@ are graph atoms whose
-- free variables are covered by the existential quantifier or the antecedent
-- of the clause. Then, it tries to find an instantiation for the
-- universal variables of @cl@ such that the antecedent of @cl@ is implied by
-- the sequent and the succedent contains new information with respect to the
-- sequent. Free variables in the atoms are to be interpreted as existentially
-- quantified.
resolveCoveredGraphClause :: CClause  -- ^ Clause to resolve against sequent.
                          -> Sequent  -- ^ Sequent.
                          -> [(ClSubst, Conj LAtom, [Goal])] 
                             -- ^ Instantiation, implied atoms, and newly covered goals.
resolveCoveredGraphClause cl se = do
    -- ensure the clause has the expected form
    guard (hasCoveredGraphSuccedent cl)
    -- compute an instantation such that the constraints and the antecedent are
    -- true and return the implied atoms.
    (((atoms, coveredGoals), inst), freshSupply) <- 
        (`runFreshT` avoid (boundClauseVars cl)) $ 
        (`runStateT` emptySubst                ) $ 
        runWriterT                               $ do 
            proveTermEqs $ map constraintEq $ substToList $ get cConstrs cl
            mapM_ (proveCAtom se) $ getConj $ get cAnte cl
            impliedAtoms (getDisj $ get cSucc cl)
    -- check that this resolution adds information to the graph part; i.e.,
    -- some of the newly added consequences cannot be proven from it.
    let producing = null $ 
            (`runFreshT` freshSupply) $ (`execStateT` inst) $ runWriterT $
                mapM_ (proveAtom se) (getConj atoms)
    guard (null (getConj atoms) || producing)
    return (inst, atoms, coveredGoals)
  where
    impliedAtoms []            = return $ Conj []
    impliedAtoms [CAtom ato]   = return $ Conj [ato]
    impliedAtoms [CFormula fm] = destExConjs fm
    impliedAtoms _             = unexpectedStructure

    destExConjs (Qua Ex hint fm) = do
        v <- uncurry freshLVar hint
        destExConjs (unquantify v fm)
    destExConjs fm =
        T.mapM mkCAtom $ toplevelConjs fm
    
    mkCAtom (Ato ato) = return $ freeFreeBLAtom ato
    mkCAtom _         = unexpectedStructure

    unexpectedStructure = error "resolveCoveredGraphClause: unexpected structure"
