{-# LANGUAGE ViewPatterns, DeriveDataTypeable, TupleSections, TypeOperators, TemplateHaskell, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- The constraint reduction rules, which are not enforced as invariants in
-- "Theory.Constraint.Solver.Reduction".
module Theory.Constraint.Solver.Goals (
    openGoals
  , solveGoal
  , markGoalAsSolved
  ) where

import           Debug.Trace

import           Prelude                                 hiding ((.), id)

import qualified Data.DAG.Simple                         as D (cyclic)
import           Data.List
import qualified Data.Map                                as M
import qualified Data.Set                                as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.State                     (gets)

import           Text.PrettyPrint.Class

import           Extension.Data.Label
import           Extension.Prelude

import           Theory.Constraint.Solver.Contradictions (substCreatesNonNormalTerms)
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model


------------------------------------------------------------------------------
-- Extracting Goals
------------------------------------------------------------------------------

data Usefulness = Useful | Useless
  deriving (Show, Eq, Ord)

-- | All open premises stemming both from labelled nodes and requires facts.
openPremiseGoals :: System -> [(Usefulness, Goal)]
openPremiseGoals se = do
    (i, ru) <- oneOfMap $ get sNodes se
    (u, fa) <- enumPrems ru
    let p = (i, u)
        breakers = ruleInfo (get praciLoopBreakers) (const []) $ get rInfo ru
    case fa of
      -- up-K facts: are transformed to actions by 'labelNodeId'.
      (kFactView -> Just (UpK, _, _))  -> mzero
      -- down-K facts
      (kFactView -> Just (DnK, _, _))
        | p `S.member` coveredPrems -> mzero
        | otherwise                 -> return . (Useful,)  $ PremDnKG p
      -- all other facts
      _ | p `S.member` coveredPrems -> mzero
        | u `elem` breakers         -> return . (Useless,) $ PremiseG p fa True
        | otherwise                 -> return . (Useful,) $  PremiseG p fa False
  where
    coveredPrems = S.fromList $ eTgt <$> S.toList (get sEdges se) <|>
                                cTgt <$> S.toList (get sChains se)



-- | All open chain goals. These are all the chains that do not end in a
-- message variable in the sequent because they are deleted upon solving.
openChainGoals :: System -> [Goal]
openChainGoals se = do
    ch@(Chain c _) <- S.toList $ get sChains se
    case kFactView (nodeConcFact c se) of
      Just (DnK, _, m) | isMsgVar m -> mzero
                       | otherwise  -> return $ ChainG ch
      fa -> error $ "openChainGoals: impossible fact: " ++ show fa

-- | All open splitting goals.
openSplitGoals :: System -> [Goal]
openSplitGoals se = SplitG <$> eqSplits (get sEqStore se)

openKUActionGoals :: System -> [(Usefulness, Goal)]
openKUActionGoals sys = do
    (i, fa, m) <- kuActionAtoms sys
    case () of
        -- Products, pairs, and inverses are solved by 'insertAction'
      _ | isProduct m || isPair m || isInverse m   -> []
        -- Message variables and public names can be instantiated such that
        -- they are solved.
        | isMsgVar m || sortOfLNTerm m == LSortPub -> []
        -- Simple terms must be constructed, but their actions are unlikely
        -- to introduce a contradiction. Deducible terms are also unlikely to
        -- introduce a contradiction => delay both of them
        | isSimpleTerm m || deducible i m -> return (Useless, ActionG i fa)
        -- Other KU-action goals.
        | otherwise                       -> return (Useful, ActionG i fa)
  where
    existingDeps = rawLessRel sys

    -- We use the following heuristic for marking KU-actions as useful (worth
    -- solving now) or useless (to be delayed until no more useful goals
    -- remain). We ignore all goals that do not contain a fresh variable
    -- or where there exists a node, not after the premise or the last node,
    -- providing an Out or KD conclusion that provides the message we are
    -- looking for as a toplevel term.
    --
    -- If such a node exist, then solving the goal will result in at least one
    -- case where we didn't make real progress except.
    toplevelTerms t@(destPair -> Just (t1, t2)) =
        t : toplevelTerms t1 ++ toplevelTerms t2
    toplevelTerms t@(destInverse -> Just t1) = t : toplevelTerms t1
    toplevelTerms t = [t]

    deducible i m = or $ do
        (j, ru) <- M.toList $ get sNodes sys
        -- We cannot deduce a message from a last node.
        guard (not $ isLast sys j)
        let derivedMsgs = concatMap toplevelTerms $
                [ t | Fact OutFact [t] <- get rConcs ru] <|>
                [ t | Just (DnK, _, t) <- kFactView <$> get rConcs ru]
        -- m is deducible from j without an immediate contradiction
        -- if it is a derived message of 'ru' and the dependency does
        -- not make the graph cyclic.
        return $ m `elem` derivedMsgs &&
                 not (D.cyclic ((j, i) : existingDeps))

openStandardActionGoals :: System -> [Goal]
openStandardActionGoals = map (uncurry ActionG) . standardActionAtoms

-- | All open disjunction goals.
--
-- We assume that solved formulas have been removed from sFormulas
openDisjunctionGoals :: System -> [Goal]
openDisjunctionGoals se = do
  GDisj d <- filter (/= gfalse) $ S.toList $ get sFormulas se
  return $ DisjG d

-- | All open goals (non-deterministic choices of possible proof steps) in the
-- sequent.
openGoals :: System -> [Goal]
openGoals se = delayUseless $ sortDecisionTree solveFirst $ concat $
   [ (Useful,) <$> openStandardActionGoals se
   , (Useful,) <$> openDisjunctionGoals se
   , (Useful,) <$> openChainGoals se
   , openPremiseGoals se
   , openKUActionGoals se
   -- SM: Commented out as automatic saturation works again.
   -- , (Useful,) <$> openImplicationGoals se
   , (Useful,) <$> openSplitGoals se
   ]
  where
    solveFirst = map (. snd)
        [ isDisjGoal
        , isNonLoopingProtoFactGoal
        , isStandardActionGoal
        , isChainGoal
        , isFreshKnowsGoal
        , isSplitGoalSmall
        , isDoubleExpGoal ]

    isNonLoopingProtoFactGoal (PremiseG _ (Fact KUFact _) _      ) = False
    isNonLoopingProtoFactGoal (PremiseG _ _               mayLoop) = not mayLoop
    isNonLoopingProtoFactGoal _                                    = False

    msgPremise (ActionG _ fa) = do (UpK, _, m) <- kFactView fa; return m
    msgPremise _              = Nothing

    isFreshKnowsGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | lvarSort lv == LSortFresh -> True
        _                                                           -> False

    isDoubleExpGoal goal = case msgPremise goal of
        Just (viewTerm2 -> FExp  _ (viewTerm2 -> FMult _)) -> True
        _                                                  -> False

    isSplitGoalSmall (SplitG sid) = splitCasenum (get sEqStore se) sid < 3
    isSplitGoalSmall _            = False

    delayUseless = map snd . sortOn fst


-- | @sortDecisionTree xs ps@ returns a reordering of @xs@
-- such that the sublist satisfying @ps!!0@ occurs first,
-- then the sublist satisfying @ps!!1@, and so on.
sortDecisionTree :: [a -> Bool] -> [a] -> [a]
sortDecisionTree []     xs = xs
sortDecisionTree (p:ps) xs = sat ++ sortDecisionTree ps nonsat
  where (sat, nonsat) = partition p xs

------------------------------------------------------------------------------
-- Solving 'Goal's
------------------------------------------------------------------------------

-- | @solveGoal rules goal@ enumerates all possible cases of how this goal
-- could be solved in the context of the given @rules@. For each case, a
-- sensible case-name is returned.
solveGoal :: Goal -> Reduction String
solveGoal goal = do
    -- mark before solving, as representation might change due to unification
    markGoalAsSolved "directly" goal
    rules <- askM pcRules
    case goal of
      ActionG i fa   -> solveAction  (nonSilentRules rules) (i, fa)
      PremiseG p fa _mayLoop ->
          solvePremise (get crProtocol rules ++ get crConstruct rules) p fa
      PremDnKG p     -> solvePremDnK (get crProtocol  rules) p
      ChainG ch      -> solveChain   (get crDestruct  rules) ch
      SplitG i       -> solveSplit i
      DisjG disj     -> solveDisjunction disj
      ImplG gf       -> modM sFormulas (S.insert gf) >> return "add_formula"

-- The follwoing functions are internal to 'solveGoal'. Use them with great
-- care.

-- | Mark this 'Goal' as being solved. This does not work for all goals. Check
-- the code.
markGoalAsSolved :: String -> Goal -> Reduction ()
markGoalAsSolved how goal =
    trace msg $
    case goal of
      ActionG i fa   -> modM sActionAtoms (S.delete (i, fa))
      PremiseG _ _ _ -> return ()
      PremDnKG _     -> return ()
      ChainG ch      -> modM sChains (S.delete ch)
      SplitG _       -> return () -- FIXME:
      DisjG disj     -> modM sFormulas       (S.delete $ GDisj disj) >>
                        modM sSolvedFormulas (S.insert $ GDisj disj)
      ImplG _       -> return ()
  where
    msg = render $ nest 2 $ sep
      [ text "solving goal" <-> parens (text how) <> colon
      , nest 2 (prettyGoal goal) ]

-- | CR-rule *S_at*: solve an action goal.
solveAction :: [RuleAC]         -- ^ All rules labelled with an action
            -> (NodeId, LNFact) -- ^ The action we are looking for.
            -> Reduction String   -- ^ A sensible case name.
solveAction rules (i, fa) = do
    mayRu <- M.lookup i <$> getM sNodes
    showRuleCaseName <$> case mayRu of
        Nothing -> do ru  <- labelNodeId i rules
                      act <- disjunctionOfList $ get rActs ru
                      void (solveFactEqs SplitNow [Equal fa act])
                      return ru

        Just ru -> do unless (fa `elem` get rActs ru) $ do
                          act <- disjunctionOfList $ get rActs ru
                          void (solveFactEqs SplitNow [Equal fa act])
                      return ru

{-
-- | CR-rule *DG2_2,u*: solve a KU-premise.
--
-- Solve a K-up-knowledge premise.
--
--  Should not be required, as non-trivial KU-premises are solved by
--  solvePremise and rule S_{at,u,triv} is applied by solveUpK.
--
solvePremUpK :: [RuleAC]  -- ^ All rules with KU-conclusions.
             -> NodePrem  -- ^ Premise requiring the
             -> LNTerm
             -> Reduction String
solvePremUpK rules p m = do
    (ru, c, faConc) <- freshNodeConc rules
    case kFactView faConc of
      Just (UpK, _, m') ->
        do solveTermEqs SplitNow [(Equal m m')]
           modM sMsgEdges (S.insert (MsgEdge c p))
           return $ showRuleCaseName ru
      _ -> error $ "solveUpK: unexpected fact: " ++ show faConc
-}

-- | CR-rule *DG_{2,P}*: solve a premise with a direct edge
-- from a unifying conclusion.
--
-- Note that *In* and *Fr* facts are solved directly when adding a 'ruleNode'.
-- Moreover, *KD* facts are solved by 'solveDnK' and *KU* facts are solved by
-- 'solveUpK'.
--
solvePremise :: [RuleAC]       -- ^ All rules with a non-K-fact conclusion.
             -> NodePrem       -- ^ Premise to solve.
             -> LNFact         -- ^ Fact required at this premise.
             -> Reduction String -- ^ Case name to use.
solvePremise rules p faPrem = do
    (ru, c, faConc) <- insertFreshNodeConc rules
    void (solveFactEqs SplitNow [(Equal faPrem faConc)])
    modM sEdges (S.insert (Edge c p))
    return $ showRuleCaseName ru

-- | CR-rule *DG2_{2,d}*: solve a KD-premise.
solvePremDnK :: [RuleAC]       -- ^ All rules that derive a send fact.
             -> NodePrem       -- ^ The KD-premise to solve.
             -> Reduction String -- ^ Case name to use.
solvePremDnK rules p = do
    iLearn    <- freshLVar "vl" LSortNode
    mLearn    <- varTerm <$> freshLVar "t" LSortMsg
    concLearn <- kdFact (Just CanExp) mLearn
    let premLearn = outFact mLearn
        -- !! Make sure that you construct the correct rule!
        ruLearn = Rule (IntrInfo IRecvRule) [premLearn] [concLearn] []
        cLearn = (iLearn, ConcIdx 0)
        pLearn = (iLearn, PremIdx 0)
    modM sNodes  (M.insert iLearn ruLearn)
    modM sChains (S.insert (Chain cLearn p))
    solvePremise rules pLearn premLearn

-- | CR-rule *DG2_chain*: solve a chain constraint.
solveChain :: [RuleAC]        -- ^ All destruction rules.
           -> Chain           -- ^ The chain to extend by one step.
           -> Reduction String  -- ^ Case name to use.
solveChain rules (Chain c p) = do
    faConc  <- gets $ nodeConcFact c
    (do -- solve it by a direct edge
        faPrem <- gets $ nodePremFact p
        void (solveFactEqs SplitNow [(Equal faPrem faConc)])
        modM sEdges  (S.insert (Edge c p))
        let m = case kFactView faConc of
                  Just (DnK, _, m') -> m'
                  _                 -> error $ "solveChain: impossible"
            caseName (viewTerm -> FApp o _) = show o
            caseName t                      = show t
        return $ caseName m
     `disjunction`
     do -- extend it with one step
        (i, ru)     <- insertFreshNode rules
        (v, faPrem) <- disjunctionOfList $ enumPrems ru
        void (solveFactEqs SplitNow [(Equal faPrem faConc)])
        modM sEdges  (S.insert (Edge c (i, v)))
        modM sChains (S.insert (Chain (i, ConcIdx 0) p))
        return $ showRuleCaseName ru
     )

-- | Solve an equation split. There is no corresponding CR-rule in the rule
-- system on paper because there we eagerly split over all variants of a rule.
-- In practice, this es too expensive and we therefore use the equation store
-- to delay these splits.
solveSplit :: SplitId -> Reduction String
solveSplit x = do
    split <- gets ((`splitAtPos` x) . get sEqStore)
    let errMsg = error "solveSplit: split of equations on unconstrained variable!"
    store      <- maybe errMsg disjunctionOfList split
    -- FIXME: Simplify this interaction with the equation store
    hnd        <- getMaudeHandle
    substCheck <- gets (substCreatesNonNormalTerms hnd)
    store'     <- simp hnd substCheck store
    contradictoryIf (eqsIsFalse store')
    sEqStore =: store'
    return "split"

-- | CR-rule *S_disj*: solve a disjunction of guarded formulas using a case
-- distinction.
--
-- In contrast to the paper, we use n-ary disjunctions and also split over all
-- of them at once.
solveDisjunction :: Disj LNGuarded -> Reduction String
solveDisjunction disj = do
    (i, gfm) <- disjunctionOfList $ zip [(1::Int)..] $ getDisj disj
    insertFormula gfm
    return $ "case_" ++ show i

