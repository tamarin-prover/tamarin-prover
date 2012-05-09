{-# LANGUAGE ViewPatterns, DeriveDataTypeable, TupleSections, TypeOperators, TemplateHaskell, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- A monad for writing constraint reduction steps together with basic steps
-- for inserting nodes, edges, actions, and equations and applying
-- substitutions.
module Theory.Constraint.Solver.Reduction (
  -- * The constraint 'Reduction' monad
    Reduction
  , execReduction
  , runReduction

  -- ** Change management
  , ChangeIndicator(..)
  , whenChanged
  , applyChangeList
  , whileChanging

  -- ** Accessing the 'ProofContext'
  , getProofContext
  , getMaudeHandle

  -- ** Inserting nodes, edges, and atoms
  , labelNodeId
  , insertFreshNode
  , insertFreshNodeConc
  , insertFreshCoerceRuleNode

  , insertAtom
  , insertEdges
  , insertAction
  , insertLess
  , insertFormula
  , reducibleFormula

  -- ** Substitution application
  , substSystem
  , substNodes
  , substEdges
  , substLastAtom
  , substLessAtoms
  , substActionAtoms
  , substFormulas
  , substSolvedFormulas

  -- ** Solving equalities
  , solveNodeIdEqs
  , solveTermEqs
  , solveFactEqs
  , solveRuleEqs
  , solveSubstEqs

  -- ** Conjunction with another constraint 'System'
  , conjoinSystem

  -- ** Convenience export
  , module Logic.Connectives

  ) where

import           Prelude                        hiding ( (.), id )

import qualified Data.Foldable                  as F
import qualified Data.Map                       as M
import qualified Data.Set                       as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Bind
import           Control.Monad.Disj
import           Control.Monad.Reader
import           Control.Monad.State            (StateT, runStateT, execStateT, gets )

import           Text.PrettyPrint.Class

import           Extension.Data.Label
import           Extension.Data.Monoid          (Monoid(..))
import           Extension.Prelude

import           Logic.Connectives

import           Theory.Constraint.Solver.Types
import           Theory.Constraint.Solver.Contradictions
import           Theory.Constraint.System
import           Theory.Model


------------------------------------------------------------------------------
-- The constraint reduction monad
------------------------------------------------------------------------------

-- | A constraint reduction step. Its state is the current constraint system,
-- it can generate fresh names, split over cases, and access the proof
-- context.
type Reduction = StateT System (FreshT (DisjT (Reader ProofContext)))


-- Executing reductions
-----------------------

-- | Run a constraint reduction. Returns a list of constraint systems whose
-- combined solutions are equal to the solutions of the given system. This
-- property is obviously not enforced, but it must be respected by all
-- functions of type 'Reduction'.
runReduction :: Reduction a -> ProofContext -> System -> FreshState
             -> Disj ((a, System), FreshState)
runReduction m ctxt se fs =
    Disj $ (`runReader` ctxt) $ runDisjT $ (`runFreshT` fs) $ runStateT m se

-- | Run a constraint reduction returning only the updated constraint systems
-- and the new freshness states.
execReduction :: Reduction a -> ProofContext -> System -> FreshState
              -> Disj (System, FreshState)
execReduction m ctxt se fs =
    Disj $ (`runReader` ctxt) . runDisjT . (`runFreshT` fs) $ execStateT m se


-- Change management
--------------------

-- | Indicate whether the constraint system was changed or not.
data ChangeIndicator = Unchanged | Changed
       deriving( Eq, Ord, Show )

instance Monoid ChangeIndicator where
    mempty = Unchanged

    Changed   `mappend` _         = Changed
    _         `mappend` Changed   = Changed
    Unchanged `mappend` Unchanged = Unchanged

-- | Return 'True' iff there was a change.
wasChanged :: ChangeIndicator -> Bool
wasChanged Changed   = True
wasChanged Unchanged = False

-- | Only apply a monadic action, if there has been a change.
whenChanged :: Monad m => ChangeIndicator -> m () -> m ()
whenChanged = when . wasChanged

-- | Apply a list of changes to the proof state.
applyChangeList :: [Reduction ()] -> Reduction ChangeIndicator
applyChangeList []      = return Unchanged
applyChangeList changes = sequence_ changes >> return Changed

-- | Execute a 'Reduction' as long as it results in changes. Indicate whether
-- at least one change was performed.
whileChanging :: Reduction ChangeIndicator -> Reduction ChangeIndicator
whileChanging reduction =
    go Unchanged
  where
    go indicator = do indicator' <- reduction
                      case indicator' of
                          Unchanged -> return indicator
                          Changed   -> go     indicator'


-- Accessing the proof context
------------------------------

-- | Retrieve the 'ProofContext'.
getProofContext :: Reduction ProofContext
getProofContext = ask

-- | Retrieve the 'MaudeHandle' from the 'ProofContext'.
getMaudeHandle :: Reduction MaudeHandle
getMaudeHandle = askM pcMaudeHandle


-- Inserting (fresh) nodes into the constraint system
-----------------------------------------------------

-- | Insert a fresh rule node labelled with a fresh instance of one of the
-- rules and return one of the conclusions.
insertFreshNodeConc :: [RuleAC] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConc rules = do
    (i, ru) <- insertFreshNode rules
    (v, fa) <- disjunctionOfList $ enumConcs ru
    return (ru, (i, v), fa)

-- | Insert a fresh rule node labelled with a fresh instance of one of the rules
-- and solve it's 'Fr', 'In', and 'KU' premises immediatly.
insertFreshNode :: [RuleAC] -> Reduction (NodeId, RuleACInst)
insertFreshNode rules = do
    i <- freshLVar "vr" LSortNode
    (,) i <$> labelNodeId i rules

-- | Label a node-id with a fresh instance of one of the rules and
-- solve it's 'Fr', 'In', and 'KU' premises immediatly.
--
-- PRE: Node must not yet be labelled with a rule.
labelNodeId :: NodeId -> [RuleAC] -> Reduction RuleACInst
labelNodeId = \i rules -> do
    (ru, mrconstrs) <- importRule =<< disjunctionOfList rules
    solveRuleConstraints mrconstrs
    modM sNodes (M.insert i ru)

    -- CR-rule *DG2_2* specialized for *In* facts.
    let inFacts = do
            (v, Fact InFact [m]) <- enumPrems ru
            return $ do
                j <- freshLVar "vf" LSortNode
                ruKnows <- mkISendRuleAC m
                modM sNodes (M.insert j ruKnows)
                modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i, v))
                solveKuPrems j ruKnows

    -- CR-rule *DG2_2* specialized for *Fr* facts.
    let freshFacts = do
            (v, Fact FreshFact [m]) <- enumPrems ru
            return $ do
                j <- freshLVar "vf" LSortNode
                modM sNodes (M.insert j (mkFreshRuleAC m))
                unless (isFreshVar m) $ do
                    -- 'm' must be of sort fresh
                    n <- varTerm <$> freshLVar "n" LSortFresh
                    void (solveTermEqs SplitNow [Equal m n])
                modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i,v))

    -- solve all Fr, In, and KU premises
    sequence_ inFacts
    sequence_ freshFacts
    solveKuPrems i ru
    return ru
  where
    -- | Import a rule with all its variables renamed to fresh variables.
    importRule ru = someRuleACInst ru `evalBindT` noBindings

    mkISendRuleAC m = do
        faPrem <- kuFact Nothing m
        return $ Rule (IntrInfo (ISendRule))
                      [faPrem] [inFact m] [kLogFact m]

    mkFreshRuleAC m = Rule (ProtoInfo (ProtoRuleACInstInfo FreshRule []))
                           [] [freshFact m] []

    -- CR-rule *DG2_{2,u}*: solve all KU-premises of a node annoted with the
    -- given rule by inserting the corresponding KU-actions before this node.
    solveKuPrems :: NodeId -> RuleACInst -> Reduction ()
    solveKuPrems i ru = sequence_ $ do
        (_, fa) <- enumPrems ru
        guard (isKUFact fa)
        return $ do
            j <- freshLVar "vk" LSortNode
            insertLess j i
            void (insertAction j fa)

-- | Generate a fresh coerce rule node; return node-index, premise, and
-- conclusion.
insertFreshCoerceRuleNode :: Reduction (LVar, (LNFact, LNFact))
insertFreshCoerceRuleNode = do
    i <- freshLVar "vc" LSortNode
    x <- varTerm <$> freshLVar "x" LSortMsg
    v <- freshLVar "f_" LSortMsg
    let faPrem = Fact KDFact [varTerm v, x]
        faConc = Fact KUFact [varTerm v, x]
    modM sNodes (M.insert i (Rule (IntrInfo CoerceRule) [faPrem] [faConc] []))
    return (i, (faPrem, faConc))

-- | Insert an edge constraint. CR-rule *DG1_2* is enforced automatically,
-- i.e., the fact equalities are enforced.
insertEdges :: [(NodeConc, LNFact, LNFact, NodePrem)] -> Reduction ()
insertEdges edges = do
    void (solveFactEqs SplitNow [ Equal fa1 fa2 | (_, fa1, fa2, _) <- edges ])
    modM sEdges (\es -> foldr S.insert es [ Edge c p | (c,_,_,p) <- edges])

-- | Insert an 'Action' atom. Ensures that (almost all) trivial *KU* actions
-- are solved immediatly using rule *S_{at,u,triv}*. We currently avoid
-- adding intermediate products. Indicates whether nodes other than the given
-- action have been added to the constraint system.
--
-- FIXME: Ensure that intermediate products are also solved before stating
-- that no rule is applicable.
insertAction :: NodeId -> LNFact -> Reduction ChangeIndicator
insertAction i fa = do
    present <- ((i, fa) `S.member`) <$> getM sActionAtoms
    if present
      then do return Unchanged
      else do modM sActionAtoms (S.insert (i, fa))
              case kFactView fa of
                Just (UpK, _, viewTerm2 -> FPair m1 m2) ->
                    requiresKU m1 *> requiresKU m2 *> return Changed

                Just (UpK, _, viewTerm2 -> FInv m) ->
                    requiresKU m *> return Changed

                Just (UpK, _, viewTerm2 -> FMult ms) ->
                    mapM_ requiresKU ms *> return Changed

                _ -> return Unchanged
  where
    -- Here we rely on the fact that the action is new. Otherwise, we might
    -- loop due to generating new KU-nodes that are merged immediatly.
    requiresKU t = do
      j <- freshLVar "vk" LSortNode
      faKU <- kuFact Nothing t
      insertLess j i
      void (insertAction j faKU)

-- | Insert a 'Less' atom. @insertLess i j@ means that *i < j* is added.
insertLess :: NodeId -> NodeId -> Reduction ()
insertLess i j = modM sLessAtoms (S.insert (i, j))

-- | Insert a 'Last' atom and ensure their uniqueness.
insertLast :: NodeId -> Reduction ChangeIndicator
insertLast i = do
    lst <- getM sLastAtom
    case lst of
      Nothing -> setM sLastAtom (Just i) >> return Unchanged
      Just j  -> solveNodeIdEqs [Equal i j]

-- | Insert an atom. Returns 'Changed' if another part of the constraint
-- system than the set of actions was changed.
insertAtom :: LNAtom -> Reduction ChangeIndicator
insertAtom ato = case ato of
    EqE x y       -> solveTermEqs SplitNow [Equal x y]
    Action i fa   -> insertAction (ltermNodeId' i) fa
    Less i j      -> do insertLess (ltermNodeId' i) (ltermNodeId' j)
                        return Unchanged
    Last i        -> insertLast (ltermNodeId' i)

-- | Insert a 'Guarded' formula. Ensures that existentials, conjunctions, negated
-- last atoms, and negated less atoms, are immediately solved using the rules
-- *S_exists*, *S_and*, *S_not,last*, and *S_not,less*. Only the inserted
-- formula is marked as solved. Other intermediate formulas are not marked.
insertFormula :: LNGuarded -> Reduction ()
insertFormula = do
    insert True
  where
    insert mark fm = do
        formulas       <- getM sFormulas
        solvedFormulas <- getM sSolvedFormulas
        insert' mark formulas solvedFormulas fm

    insert' mark formulas solvedFormulas fm
      | fm `S.member` formulas       = return ()
      | fm `S.member` solvedFormulas = return ()
      | otherwise = case fm of
          GAto ato -> do
              markAsSolved
              void (insertAtom (bvarToLVar ato))

          -- CR-rule *S_∧*
          GConj fms -> do
              markAsSolved
              mapM_ (insert False) (getConj fms)

          -- CR-rule *S_∃*
          GGuarded Ex ss as gf -> do
              -- must always mark as solved, as we otherwise may repeatedly
              -- introduce fresh variables.
              modM sSolvedFormulas $ S.insert fm
              xs <- mapM (uncurry freshLVar) ss
              let body = gconj (map GAto as ++ [gf])
              insert False (substBound (zip [0..] (reverse xs)) body)

          -- CR-rule *S_{¬,⋖}*
          GGuarded All [] [Less i j] gf  | gf == gfalse -> do
              markAsSolved
              insert False (gdisj [GAto (EqE i j), GAto (Less j i)])

          -- CR-rule *S_{¬,last}*
          GGuarded All [] [Last i]   gf  | gf == gfalse -> do
              markAsSolved
              lst <- getM sLastAtom
              j <- case lst of
                     Nothing  -> do j <- freshLVar "l" LSortNode
                                    void (insertLast j)
                                    return (varTerm (Free j))
                     Just j -> return (varTerm (Free j))
              insert False $ gdisj [ GAto (Less j i), GAto (Less i j) ]

          -- Fallback -- for Disj and Guarded All quantification: just store
          -- for later steps.
          _ -> modM sFormulas (S.insert fm)
      where
        markAsSolved = when mark $ modM sSolvedFormulas $ S.insert fm

-- | 'True' iff the formula can be reduced by one of the rules implemented in
-- 'insertFormula'.
reducibleFormula :: LNGuarded -> Bool
reducibleFormula fm = case fm of
    GAto _                        -> True
    GConj _                       -> True
    GGuarded Ex _ _ _             -> True
    GGuarded All [] [Less _ _] gf -> gf == gfalse
    GGuarded All [] [Last _]   gf -> gf == gfalse
    _                             -> False


-- Substitution
---------------

-- | Apply the current substitution of the equation store to the remainder of
-- the sequent.
substSystem :: Reduction ChangeIndicator
substSystem = do
    c1 <- substNodes
    substEdges
    substChains
    substLastAtom
    substLessAtoms
    c2 <- substActionAtoms
    substFormulas
    substSolvedFormulas
    substLemmas
    return (c1 <> c2)

-- no invariants to maintain here
substEdges, substChains, substLessAtoms, substLastAtom, substFormulas,
  substSolvedFormulas, substLemmas :: Reduction ()

substEdges          = substPart sEdges
substLessAtoms      = substPart sLessAtoms
substLastAtom       = substPart sLastAtom
substChains         = substPart sChains
substFormulas       = substPart sFormulas
substSolvedFormulas = substPart sSolvedFormulas
substLemmas         = substPart sLemmas

-- | Apply the current substitution of the equation store to a part of the
-- sequent. This is an internal function.
substPart :: Apply a => (System :-> a) -> Reduction ()
substPart l = do subst <- getM sSubst
                 modM l (apply subst)

-- | Substitute all action atoms.
substActionAtoms :: Reduction ChangeIndicator
substActionAtoms = do
    subst <- getM sSubst
    actions <- S.toList <$> getM sActionAtoms
    sActionAtoms =: S.empty
    changes <- forM actions $ \action@(i, fa) -> case kFactView fa of
        -- Look out for KU-actions that might need to be solved again.
        Just (UpK, _, m)
          | (isMsgVar m || isProduct m) && (apply subst m /= m) ->
              insertAction i (apply subst fa)
        _ -> do modM sActionAtoms (S.insert $ apply subst action)
                return Unchanged

    return (mconcat changes)

-- | Apply the current substitution of the equation store the nodes of the
-- constraint system. Indicates whether additional equalities were added to
-- the equations store.
substNodes :: Reduction ChangeIndicator
substNodes =
    substNodeIds <* ((modM sNodes . M.map . apply) =<< getM sSubst)

-- | @setNodes nodes@ normalizes the @nodes@ such that node ids are unique and
-- then updates the @sNodes@ field of the proof state to the corresponding map.
-- Return @True@ iff new equalities have been added to the equation store.
setNodes :: [(NodeId, RuleACInst)] -> Reduction ChangeIndicator
setNodes nodes0 = do
    sNodes =: M.fromList nodes
    if null ruleEqs then                                    return Unchanged
                    else solveRuleEqs SplitLater ruleEqs >> return Changed
  where
    -- merge nodes with equal node id
    (ruleEqs, nodes) = first concat $ unzip $ map merge $ groupSortOn fst nodes0

    merge []            = unreachable "setNodes"
    merge (keep:remove) = (map (Equal (snd keep) . snd) remove, keep)

-- | Apply the current substitution of the equation store to the node ids and
-- ensure uniqueness of the labels, as required by rule *U_lbl*. Indicates
-- whether there where new equalities added to the equations store.
substNodeIds :: Reduction ChangeIndicator
substNodeIds =
    whileChanging $ do
        subst <- getM sSubst
        nodes <- gets (map (first (apply subst)) . M.toList . get sNodes)
        setNodes nodes


-- Conjoining two constraint systems
------------------------------------

-- | @conjoinSystem se@ conjoins the logical information in @se@ to the
-- constraint system. It assumes that the free variables in @se@ are shared
-- with the free variables in the proof state.
conjoinSystem :: System -> Reduction ()
conjoinSystem sys = do
    kind <- getM sCaseDistKind
    unless (kind == get sCaseDistKind sys) $
        error "conjoinSystem: typing-kind mismatch"
    joinSets sSolvedFormulas
    joinSets sLemmas
    joinSets sChains
    joinSets sEdges
    F.mapM_ insertLast             $ get sLastAtom    sys
    F.mapM_ (uncurry insertLess)   $ get sLessAtoms   sys
    F.mapM_ (uncurry insertAction) $ get sActionAtoms sys
    F.mapM_ insertFormula $ get sFormulas sys
    -- update nodes
    _ <- (setNodes . (M.toList (get sNodes sys) ++) . M.toList) =<< getM sNodes
    -- conjoin equation store
    modM sConjDisjEqs (`mappend` get sConjDisjEqs sys)
    void (solveSubstEqs SplitNow $ get sSubst sys)
    -- Propagate substitution changes. Ignore change indicator, as it is
    -- assumed to be 'Changed' by default.
    void substSystem
  where
    joinSets :: Ord a => (System :-> S.Set a) -> Reduction ()
    joinSets proj = modM proj (`S.union` get proj sys)



-- Unification via the equation store
-------------------------------------

-- The 'ChangeIndicator' indicates whether at least one non-trivial equality
-- was solved.

-- | @noContradictoryEqStore@ suceeds iff the equation store is not
-- contradictory.
noContradictoryEqStore :: Reduction ()
noContradictoryEqStore = (contradictoryIf . eqsIsFalse) =<< getM sEqStore

-- | Add a list of term equalities to the equation store. And
--  split resulting disjunction of equations according
--  to given split strategy.
solveTermEqs :: SplitStrategy -> [Equal LNTerm] -> Reduction ChangeIndicator
solveTermEqs splitStrat eqs0 =
    case filter (not . evalEqual) eqs0 of
      []  -> do return Unchanged
      eqs -> do hnd <- getMaudeHandle
                se <- gets id
                setM sEqStore =<< simp hnd (substCreatesNonNormalTerms hnd se)
                              =<< disjunctionOfList
                              =<< addEqs splitStrat hnd eqs
                              =<< getM sEqStore
                noContradictoryEqStore
                return Changed

-- | Add a list of equalities in substitution form to the equation store
solveSubstEqs :: SplitStrategy -> LNSubst -> Reduction ChangeIndicator
solveSubstEqs split subst =
    solveTermEqs split [Equal (varTerm v) t | (v, t) <- substToList subst]

-- | Add a list of node equalities to the equation store.
solveNodeIdEqs :: [Equal NodeId] -> Reduction ChangeIndicator
solveNodeIdEqs = solveTermEqs SplitNow . map (fmap varTerm)

-- | Add a list of fact equalities to the equation store, if possible.
solveFactEqs :: SplitStrategy -> [Equal LNFact] -> Reduction ChangeIndicator
solveFactEqs split eqs = do
    contradictoryIf (not $ all evalEqual $ map (fmap factTag) eqs)
    solveListEqs (solveTermEqs split) $ map (fmap factTerms) eqs

-- | Add a list of rule equalities to the equation store, if possible.
solveRuleEqs :: SplitStrategy -> [Equal RuleACInst] -> Reduction ChangeIndicator
solveRuleEqs split eqs = do
    contradictoryIf (not $ all evalEqual $ map (fmap (get rInfo)) eqs)
    solveListEqs (solveFactEqs split) $
        map (fmap (get rConcs)) eqs ++ map (fmap (get rPrems)) eqs

-- | Solve a number of equalities between lists interpreted as free terms
-- using the given solver for solving the entailed per-element equalities.
solveListEqs :: ([Equal a] -> Reduction b) -> [(Equal [a])] -> Reduction b
solveListEqs solver eqs = do
    contradictoryIf (not $ all evalEqual $ map (fmap length) eqs)
    solver $ concatMap flatten eqs
  where
    flatten (Equal l r) = zipWith Equal l r

-- | Solve the constraints associated with a rule.
solveRuleConstraints :: Maybe RuleACConstrs -> Reduction ()
solveRuleConstraints (Just eqConstr) = do
    hnd <- getMaudeHandle
    setM sEqStore
        -- do not use expensive substCreatesNonNormalTerms here
        =<< (simp hnd (const False) . addRuleVariants eqConstr)
        =<< getM sEqStore
    noContradictoryEqStore
solveRuleConstraints Nothing = return ()

