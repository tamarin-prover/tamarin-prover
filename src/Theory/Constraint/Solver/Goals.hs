{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns  #-}
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
    Usefulness(..)
  , AnnotatedGoal
  , GoalRanking
  , wfProtoRanking

  , openGoals
  , solveGoal
  ) where

import           Debug.Trace

import           Prelude                                 hiding (id, (.))

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

-- | Goals annotated with their number and usefulness.
type AnnotatedGoal = (Goal, (Integer, Usefulness))

type GoalRanking   = System -> [AnnotatedGoal] -> [AnnotatedGoal]


-- | The list of goals that must be solved before a solution can be extracted.
-- Each goal is annotated with its age and an indicator for its usefulness.
openGoals :: System -> [AnnotatedGoal]
openGoals sys = do
    (goal, status) <- M.toList $ get sGoals sys
    let solved = get gsSolved status
    -- check whether the goal is still open
    guard $ case goal of
        ActionG _ (kFactView -> Just (UpK, _, m)) -> not (isMsgVar m || solved)
        ActionG _ _                               -> not solved
        PremiseG _ _                              -> not solved
        -- Technically the 'False' disj would be a solvable goal. However, we
        -- have a separate proof method for this, i.e., contradictions.
        DisjG (Disj [])                           -> False
        DisjG _                                   -> not solved

        ChainG c _     ->
          case kFactView (nodeConcFact c sys) of
              Just (DnK, _, m) | isMsgVar m -> False
                               | otherwise  -> not solved
              fa -> error $ "openChainGoals: impossible fact: " ++ show fa

        -- FIXME: Split goals may be duplicated, we always have to check
        -- explicitly if they still exist.
        SplitG idx -> splitExists (get sEqStore sys) idx

    let useful = case goal of
          -- Note that 'solveAllSafeGoals' in "CaseDistinctions" relies on
          -- looping goals being classified as 'Useless'.
          _ | get gsLoops status                    -> Useless
          ActionG i (kFactView -> Just (UpK, _, m))
            | isSimpleTerm m || deducible i m       -> Useless
          _                                         -> Useful

    return (goal, (get gsNr status, useful))
  where
    existingDeps = rawLessRel sys

    -- We use the following heuristic for marking KU-actions as useful (worth
    -- solving now) or useless (to be delayed until no more useful goals
    -- remain). We ignore all goals that are simple terms or where there
    -- exists a node, not after the premise or the last node, providing an Out
    -- or KD conclusion that provides the message we are looking for as a
    -- toplevel term. If such a node exist, then solving the goal will result
    -- in at least one case where we didn't make real progress except.
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

-- | A ranking function tuned for the automatic verification of
-- classical security protocols that exhibit a well-founded protocol premise
-- fact flow.
wfProtoRanking :: GoalRanking
wfProtoRanking sys =
    delayUseless . sortDecisionTree solveFirst
  where
    delayUseless = sortOn (snd . snd)

    solveFirst = map (. fst)
        [ isDisjGoal
        , isProtoFactGoal
        , isChainGoal
        , isStandardActionGoal
        , isFreshKnowsGoal
        , isSplitGoalSmall
        , isDoubleExpGoal ]

    isProtoFactGoal (PremiseG _ fa) = not $ isKFact fa
    isProtoFactGoal _               = False

    msgPremise (ActionG _ fa) = do (UpK, _, m) <- kFactView fa; return m
    msgPremise _              = Nothing

    isFreshKnowsGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | lvarSort lv == LSortFresh -> True
        _                                                           -> False

    isDoubleExpGoal goal = case msgPremise goal of
        Just (viewTerm2 -> FExp  _ (viewTerm2 -> FMult _)) -> True
        _                                                  -> False

    -- Be conservative on splits that don't exist.
    isSplitGoalSmall (SplitG sid) =
        maybe False (< 3) $ splitSize (get sEqStore sys) sid
    isSplitGoalSmall _            = False

    -- | @sortDecisionTree xs ps@ returns a reordering of @xs@
    -- such that the sublist satisfying @ps!!0@ occurs first,
    -- then the sublist satisfying @ps!!1@, and so on.
    sortDecisionTree :: [a -> Bool] -> [a] -> [a]
    sortDecisionTree []     xs = xs
    sortDecisionTree (p:ps) xs = sat ++ sortDecisionTree ps nonsat
      where (sat, nonsat) = partition p xs


{-
-- | All open premises stemming both from labelled nodes and requires facts.
openPremiseGoals :: System -> [(Usefulness, Goal)]
openPremiseGoals se = do
    (i, ru) <- oneOfMap $ get sNodes se
    (u, fa) <- enumPrems ru
    let p = (i, u)
        breakers = ruleInfo (get praciLoopBreakers) (const []) $ get rInfo ru
    case () of
      _ | isKUFact fa               -> [] -- KU-facts handled by 'labelNodeId'
        | p `S.member` coveredPrems -> []
        | u `elem` breakers         -> return . (Useless,) $ PremiseG p fa True
        | otherwise                 -> return . (Useful,) $  PremiseG p fa False
  where
    coveredPrems = S.fromList $ eTgt <$> S.toList (get sEdges se) <|>
                                snd <$> chains se

-- | All open chain goals. These are all the chains that do not end in a
-- message variable in the sequent because they are deleted upon solving.
openChainGoals :: System -> [Goal]
openChainGoals se = do
    (c, p) <- chains se
    case kFactView (nodeConcFact c se) of
      Just (DnK, _, m) | isMsgVar m -> mzero
                       | otherwise  -> return $ ChainG c p
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
-- system together with their age.
openGoals :: System -> [(Goal, Maybe Integer)]
openGoals sys = do
    goal <- openGoals_ sys
    return (goal, M.lookup goal (get sGoals sys))

-- | All open goals (non-deterministic choices of possible proof steps) in the
-- system.
openGoals_:: System -> [Goal]
openGoals_ sys =
   filter annotated $ delayUseless $ sortDecisionTree solveFirst $ concat $
     [ (Useful,) <$> openStandardActionGoals sys
     , (Useful,) <$> openDisjunctionGoals sys
     , (Useful,) <$> openChainGoals sys
     , openPremiseGoals sys
     , openKUActionGoals sys
     , (Useful,) <$> openSplitGoals sys
     ]
  where
    annotated goal
      | goal `M.member` get sGoals sys = True
      | otherwise                      =
          error (render $ text "goal not annotated: " $-$ prettyGoal goal) True

    solveFirst = map (. snd)
        [ isDisjGoal
        , isNonLoopingProtoFactGoal
        , isChainGoal
        , isStandardActionGoal
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

    isSplitGoalSmall (SplitG sid) = splitCasenum (get sEqStore sys) sid < 3
    isSplitGoalSmall _            = False

    delayUseless = map snd . sortOn fst


-- | @sortDecisionTree xs ps@ returns a reordering of @xs@
-- such that the sublist satisfying @ps!!0@ occurs first,
-- then the sublist satisfying @ps!!1@, and so on.
sortDecisionTree :: [a -> Bool] -> [a] -> [a]
sortDecisionTree []     xs = xs
sortDecisionTree (p:ps) xs = sat ++ sortDecisionTree ps nonsat
  where (sat, nonsat) = partition p xs
-}

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
      ActionG i fa  -> solveAction  (nonSilentRules rules) (i, fa)
      PremiseG p fa ->
           solvePremise (get crProtocol rules ++ get crConstruct rules) p fa
      ChainG c p    -> solveChain (get crDestruct  rules) (c, p)
      SplitG i      -> solveSplit i
      DisjG disj    -> solveDisjunction disj

-- The follwoing functions are internal to 'solveGoal'. Use them with great
-- care.

-- | CR-rule *S_at*: solve an action goal.
solveAction :: [RuleAC]          -- ^ All rules labelled with an action
            -> (NodeId, LNFact)  -- ^ The action we are looking for.
            -> Reduction String  -- ^ A sensible case name.
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

-- | CR-rules *DG_{2,P}* and *DG_{2,d}*: solve a premise with a direct edge
-- from a unifying conclusion or using a destruction chain.
--
-- Note that *In*, *Fr*, and *KU* facts are solved directly when adding a
-- 'ruleNode'.
--
solvePremise :: [RuleAC]       -- ^ All rules with a non-K-fact conclusion.
             -> NodePrem       -- ^ Premise to solve.
             -> LNFact         -- ^ Fact required at this premise.
             -> Reduction String -- ^ Case name to use.
solvePremise rules p faPrem
  | isKDFact faPrem = do
      iLearn    <- freshLVar "vl" LSortNode
      mLearn    <- varTerm <$> freshLVar "t" LSortMsg
      concLearn <- kdFact (Just CanExp) mLearn
      let premLearn = outFact mLearn
          -- !! Make sure that you construct the correct rule!
          ruLearn = Rule (IntrInfo IRecvRule) [premLearn] [concLearn] []
          cLearn = (iLearn, ConcIdx 0)
          pLearn = (iLearn, PremIdx 0)
      modM sNodes  (M.insert iLearn ruLearn)
      insertChain cLearn p
      solvePremise rules pLearn premLearn

  | otherwise = do
      (ru, c, faConc) <- insertFreshNodeConc rules
      insertEdges [(c, faConc, faPrem, p)]
      return $ showRuleCaseName ru

-- | CR-rule *DG2_chain*: solve a chain constraint.
solveChain :: [RuleAC]              -- ^ All destruction rules.
           -> (NodeConc, NodePrem)  -- ^ The chain to extend by one step.
           -> Reduction String      -- ^ Case name to use.
solveChain rules (c, p) = do
    faConc  <- gets $ nodeConcFact c
    (do -- solve it by a direct edge
        faPrem <- gets $ nodePremFact p
        insertEdges [(c, faConc, faPrem, p)]
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
        insertEdges [(c, faConc, faPrem, (i, v))]
        markGoalAsSolved "directly" (PremiseG (i, v) faPrem)
        insertChain (i, ConcIdx 0) p
        return $ showRuleCaseName ru
     )

-- | Solve an equation split. There is no corresponding CR-rule in the rule
-- system on paper because there we eagerly split over all variants of a rule.
-- In practice, this es too expensive and we therefore use the equation store
-- to delay these splits.
solveSplit :: SplitId -> Reduction String
solveSplit x = do
    split <- gets ((`performSplit` x) . get sEqStore)
    let errMsg = error "solveSplit: inexistent split-id"
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

