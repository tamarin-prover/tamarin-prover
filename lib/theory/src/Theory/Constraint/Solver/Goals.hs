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
--
-- A goal represents a possible application of a rule that may result in
-- multiple cases or even non-termination (if applied repeatedly). These goals
-- are computed as the list of 'openGoals'. See
-- "Theory.Constraint.Solver.ProofMethod" for the public interface to solving
-- goals and the implementation of heuristics.
module Theory.Constraint.Solver.Goals (
    Usefulness(..)
  , AnnotatedGoal
  , openGoals
  , solveGoal
  ) where

-- import           Debug.Trace

import           Prelude                                 hiding (id, (.))

import qualified Data.DAG.Simple                         as D (reachableSet)
-- import           Data.Foldable                           (foldMap)
import qualified Data.Map                                as M
import qualified Data.Monoid                             as Mono
import qualified Data.Set                                as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.State                     (gets)
import           Control.Monad.Trans.State.Lazy          hiding (get,gets)
import           Control.Monad.Trans.FastFresh           -- GHC7.10 needs: hiding (get,gets)
import           Control.Monad.Trans.Reader              -- GHC7.10 needs: hiding (get,gets)

import           Extension.Data.Label

import           Theory.Constraint.Solver.Contradictions (substCreatesNonNormalTerms)
import           Theory.Constraint.Solver.Reduction
-- import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Tools.IntruderRules (mkDUnionRule, isDExpRule, isDPMultRule, isDEMapRule)
import           Theory.Model

------------------------------------------------------------------------------
-- Extracting Goals
------------------------------------------------------------------------------

data Usefulness =
    Useful
  -- ^ A goal that is likely to result in progress.
  | LoopBreaker
  -- ^ A goal that is delayed to avoid immediate termination.
  | ProbablyConstructible
  -- ^ A goal that is likely to be constructible by the adversary.
  | CurrentlyDeducible
  -- ^ A message that is deducible for the current solution.
  deriving (Show, Eq, Ord)

-- | Goals annotated with their number and usefulness.
type AnnotatedGoal = (Goal, (Integer, Usefulness))


-- Instances
------------

-- | The list of goals that must be solved before a solution can be extracted.
-- Each goal is annotated with its age and an indicator for its usefulness.
openGoals :: System -> [AnnotatedGoal]
openGoals sys = do
    (goal, status) <- M.toList $ get sGoals sys
    let solved = get gsSolved status
    -- check whether the goal is still open
    guard $ case goal of
        ActionG i (kFactView -> Just (UpK, m)) ->
          if get sDiffSystem sys 
             -- In a diff proof, all action goals need to be solved.
             then not (solved)
                      -- handled by 'insertAction'
--                       || isPair m || isInverse m 
--                       || isProduct m || isUnion m) 
             else
               not $    solved
                    -- message variables are not solved, except if the node already exists in the system -> facilitates finding contradictions
                    || (isMsgVar m && Nothing == M.lookup i (get sNodes sys)) || sortOfLNTerm m == LSortPub
                    -- handled by 'insertAction'
                    || isPair m || isInverse m || isProduct m
                    || isUnion m || isNullaryPublicFunction m
        ActionG _ _                               -> not solved
        PremiseG _ _                              -> not solved
        -- Technically the 'False' disj would be a solvable goal. However, we
        -- have a separate proof method for this, i.e., contradictions.
        DisjG (Disj [])                           -> False
        DisjG _                                   -> not solved

        ChainG c p     ->
          case kFactView (nodeConcFact c sys) of
              Just (DnK, viewTerm2 -> FUnion args) ->
                  not solved && allMsgVarsKnownEarlier c args
              -- open chains for msg vars are only solved if N5'' is applicable
              Just (DnK,  m) | isMsgVar m          -> (not solved) && 
                                                      (chainToEquality m c p)
                             | otherwise           -> not solved
              fa -> error $ "openChainGoals: impossible fact: " ++ show fa

        -- FIXME: Split goals may be duplicated, we always have to check
        -- explicitly if they still exist.
        SplitG idx -> splitExists (get sEqStore sys) idx

    let
        useful = case goal of
          _ | get gsLoopBreaker status              -> LoopBreaker
          ActionG i (kFactView -> Just (UpK, m))
              -- if there are KU-guards then all knowledge goals are useful
            | hasKUGuards             -> Useful
            | currentlyDeducible i m  -> CurrentlyDeducible
            | probablyConstructible m -> ProbablyConstructible
          _                           -> Useful

    return (goal, (get gsNr status, useful))
  where
    existingDeps = rawLessRel sys
    hasKUGuards  =
        any ((KUFact `elem`) . guardFactTags) $ S.toList $ get sFormulas sys

    checkTermLits :: (LSort -> Bool) -> LNTerm -> Bool
    checkTermLits p =
        Mono.getAll . foldMap (Mono.All . p . sortOfLit)

    -- KU goals of messages that are likely to be constructible by the
    -- adversary. These are terms that do not contain a fresh name or a fresh
    -- name variable. For protocols without loops they are very likely to be
    -- constructible. For protocols with loops, such terms have to be given
    -- similar priority as loop-breakers.
    probablyConstructible  m = checkTermLits (LSortFresh /=) m
                               && not (containsPrivate m)

    -- KU goals of messages that are currently deducible. Either because they
    -- are composed of public names only and do not contain private function
    -- symbols or because they can be extracted from a sent message using
    -- unpairing or inversion only.
    currentlyDeducible i m = (checkTermLits (LSortPub ==) m
                              && not (containsPrivate m))
                          || extractible i m

    extractible i m = or $ do
        (j, ru) <- M.toList $ get sNodes sys
        -- We cannot deduce a message from a last node.
        guard (not $ isLast sys j)
        let derivedMsgs = concatMap toplevelTerms $
                [ t | Fact OutFact [t] <- get rConcs ru] <|>
                [ t | Just (DnK, t)    <- kFactView <$> get rConcs ru]
        -- m is deducible from j without an immediate contradiction
        -- if it is a derived message of 'ru' and the dependency does
        -- not make the graph cyclic.
        return $ m `elem` derivedMsgs &&
                 not (j `S.member` D.reachableSet [i] existingDeps)

    toplevelTerms t@(viewTerm2 -> FPair t1 t2) =
        t : toplevelTerms t1 ++ toplevelTerms t2
    toplevelTerms t@(viewTerm2 -> FInv t1) = t : toplevelTerms t1
    toplevelTerms t = [t]


    allMsgVarsKnownEarlier (i,_) args =
        all (`elem` earlierMsgVars) (filter isMsgVar args)
      where earlierMsgVars = do (j, _, t) <- allKUActions sys
                                guard $ isMsgVar t && alwaysBefore sys j i
                                return t
                                
    -- check whether we have a chain that fits N5'' (an open chain between an 
    -- equality rule and a simple msg var conclusion that exists as a K up 
    -- previously) which needs to be resolved even if it is an open chain
    chainToEquality :: LNTerm -> NodeConc -> NodePrem -> Bool
    chainToEquality t_start conc p = is_msg_var && is_equality && ku_before
        where
            -- check whether it is a msg var
            is_msg_var  = isMsgVar t_start
            -- and whether we do have an equality rule instance at the end
            is_equality = isIEqualityRule $ nodeRule (fst p) sys
            -- get all KU-facts with the same msg var
            ku_start    = filter (\x -> (fst x) == t_start) $ 
                              map (\(i, _, m) -> (m, i)) $ allKUActions sys
            -- and check whether any of them happens before the KD-conclusion
            ku_before   = any (\(_, x) -> alwaysBefore sys x (fst conc)) ku_start 
                                
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

-- The following functions are internal to 'solveGoal'. Use them with great
-- care.

-- | CR-rule *S_at*: solve an action goal.
solveAction :: [RuleAC]          -- ^ All rules labelled with an action
            -> (NodeId, LNFact)  -- ^ The action we are looking for.
            -> Reduction String  -- ^ A sensible case name.
solveAction rules (i, fa) = do
    mayRu <- M.lookup i <$> getM sNodes
    showRuleCaseName <$> case mayRu of
        Nothing -> do ru  <- labelNodeId i rules Nothing
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
      let concLearn = kdFact mLearn
          premLearn = outFact mLearn
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
        cRule <- gets $ nodeRule (nodeConcNode c)
        pRule <- gets $ nodeRule (nodePremNode p)
        faPrem <- gets $ nodePremFact p
        contradictoryIf (forbiddenEdge cRule pRule)
        insertEdges [(c, faConc, faPrem, p)]
        let mPrem = case kFactView faConc of
                      Just (DnK, m') -> m'
                      _              -> error $ "solveChain: impossible"
            caseName (viewTerm -> FApp o _)    = showFunSymName o
            caseName (viewTerm -> Lit l)       = showLitName l
            caseName t                         = show t
        contradictoryIf (illegalCoerce pRule mPrem)
        return (caseName mPrem)
     `disjunction`
     -- extend it with one step
     case kFactView faConc of
         Just (DnK, viewTerm2 -> FUnion args) ->
             do -- If the chain starts at a union message, we
                -- compute the applicable destruction rules directly.
                i <- freshLVar "vr" LSortNode
                let rus = map (ruleACIntrToRuleACInst . mkDUnionRule args)
                              (filter (not . isMsgVar) args)
                -- NOTE: We rely on the check that the chain is open here.
                ru <- disjunctionOfList rus
                modM sNodes (M.insert i ru)
                -- FIXME: Do we have to add the PremiseG here so it
                -- marked as solved?
                let v = PremIdx 0
                faPrem <- gets $ nodePremFact (i,v)
                extendAndMark i ru v faPrem faConc
         Just (DnK, m) ->
             do -- If the chain does not start at a union message,
                -- the usual *DG2_chain* extension is perfomed.
                -- But we ignore open chains, as we only resolve 
                -- open chains with a direct chain
                contradictoryIf (isMsgVar m)
                cRule <- gets $ nodeRule (nodeConcNode c)
                (i, ru) <- insertFreshNode rules (Just cRule)
                contradictoryIf (forbiddenEdge cRule ru)
                -- This requires a modified chain constraint def:
                -- path via first destruction premise of rule ...
                (v, faPrem) <- disjunctionOfList $ take 1 $ enumPrems ru
                extendAndMark i ru v faPrem faConc
         _ -> error "solveChain: not a down fact"
     )
  where
    extendAndMark :: NodeId -> RuleACInst -> PremIdx -> LNFact -> LNFact 
      -> Control.Monad.Trans.State.Lazy.StateT System 
      (Control.Monad.Trans.FastFresh.FreshT 
      (DisjT (Control.Monad.Trans.Reader.Reader ProofContext))) String
    extendAndMark i ru v faPrem faConc = do
        insertEdges [(c, faConc, faPrem, (i, v))]
        markGoalAsSolved "directly" (PremiseG (i, v) faPrem)
        insertChain (i, ConcIdx 0) p
        return (showRuleCaseName ru)

    -- contradicts normal form condition:
    -- no edge from dexp to dexp KD premise, no edge from dpmult
    -- to dpmult KD premise, and no edge from dpmult to demap KD premise
    -- (this condition replaces the exp/noexp tags)
    -- no more than the allowed consecutive rule applications
    forbiddenEdge :: RuleACInst -> RuleACInst -> Bool
    forbiddenEdge cRule pRule = isDExpRule   cRule && isDExpRule  pRule  ||
                                isDPMultRule cRule && isDPMultRule pRule ||
                                isDPMultRule cRule && isDEMapRule  pRule ||
                                (getRuleName cRule == getRuleName pRule)
                                    && (getRemainingRuleApplications cRule == 1)

    -- Contradicts normal form condition N2:
    -- No coerce of a pair of inverse.
    illegalCoerce pRule mPrem = isCoerceRule pRule && isPair    mPrem ||
                                isCoerceRule pRule && isInverse mPrem ||
    -- Also: Coercing of products is unnecessary, since the protocol is *-restricted.
                                isCoerceRule pRule && isProduct mPrem 
    

-- | Solve an equation split. There is no corresponding CR-rule in the rule
-- system on paper because there we eagerly split over all variants of a rule.
-- In practice, this is too expensive and we therefore use the equation store
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

