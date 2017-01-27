{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns       #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- This module implements all rules that do not result in case distinctions
-- and equation solving. Some additional cases may although result from
-- splitting over multiple AC-unifiers. Note that a few of these rules are
-- implemented directly in the methods for inserting constraints to the
-- constraint system.  These methods are provided by
-- "Theory.Constraint.Solver.Reduction".
--
module Theory.Constraint.Solver.Simplify (

  simplifySystem

  ) where

import           Debug.Trace

import           Prelude                            hiding (id, (.))

import qualified Data.DAG.Simple                    as D
-- import           Data.Data
-- import           Data.Either                        (partitionEithers)
import qualified Data.Foldable                      as F
import           Data.List
import qualified Data.Map                           as M
-- import           Data.Monoid                        (Monoid(..))
import qualified Data.Set                           as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
-- import           Control.Monad.Fresh
import           Control.Monad.Reader
import           Control.Monad.State                (gets)


import           Extension.Data.Label
import           Extension.Prelude

import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.Reduction
-- import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model
import           Theory.Text.Pretty


-- | Apply CR-rules that don't result in case splitting until the constraint
-- system does not change anymore.
simplifySystem :: Reduction ()
simplifySystem = do
    isdiff <- getM sDiffSystem
    -- Start simplification, indicating that some change happened
    go (0 :: Int) [Changed]
    if isdiff
       then do
        -- Remove equation split goals that do not exist anymore
        removeSolvedSplitGoals
       else do
        -- Add all ordering constraint implied by CR-rule *N6*.
        exploitUniqueMsgOrder
        -- Remove equation split goals that do not exist anymore
        removeSolvedSplitGoals    
  where
    go n changes0
      -- We stop as soon as all simplification steps have been run without
      -- reporting any change to the constraint system.
      | Unchanged == mconcat changes0 = return ()
      | otherwise                     = do
          -- Store original system for reporting
          se0 <- gets id
          -- Perform one initial substitution. We do not have to consider its
          -- changes as 'substSystem' is idempotent.
          void substSystem
          -- Perform one simplification pass.
          isdiff <- getM sDiffSystem
          -- In the diff case, we cannot enfore N4-N6.
          if isdiff
            then do
              (c1,c3) <- enforceFreshAndKuNodeUniqueness
              c4 <- enforceEdgeUniqueness
              c5 <- solveUniqueActions
              c6 <- reduceFormulas
              c7 <- evalFormulaAtoms
              c8 <- insertImpliedFormulas

              -- Report on looping behaviour if necessary
              let changes = filter ((Changed ==) . snd) $
                    [ ("unique fresh instances (DG4)",        c1)
--                     , ("unique K↓-facts (N5↓)",               c2)
                    , ("unique K↑-facts (N5↑)",               c3)
                    , ("unique (linear) edges (DG2 and DG3)", c4)
                    , ("solve unambiguous actions (S_@)",     c5)
                    , ("decompose trace formula",             c6)
                    , ("propagate atom valuation to formula", c7)
                    , ("saturate under ∀-clauses (S_∀)",      c8)
                    ]
                  traceIfLooping
                    | n <= 10   = id
                    | otherwise = trace $ render $ vsep
                        [ text "Simplifier iteration" <-> int n <> colon
                        , fsep $ text "The reduction-rules for" :
                                (punctuate comma $ map (text . fst) changes) ++
                                [text "were applied to the following constraint system."]
                        , nest 2 (prettySystem se0)
                        ]

              traceIfLooping $ go (n + 1) (map snd changes)
            else do
              (c1,c2,c3) <- enforceNodeUniqueness
              c4 <- enforceEdgeUniqueness
              c5 <- solveUniqueActions
              c6 <- reduceFormulas
              c7 <- evalFormulaAtoms
              c8 <- insertImpliedFormulas

              -- Report on looping behaviour if necessary
              let changes = filter ((Changed ==) . snd) $
                    [ ("unique fresh instances (DG4)",        c1)
                    , ("unique K↓-facts (N5↓)",               c2)
                    , ("unique K↑-facts (N5↑)",               c3)
                    , ("unique (linear) edges (DG2 and DG3)", c4)
                    , ("solve unambiguous actions (S_@)",     c5)
                    , ("decompose trace formula",             c6)
                    , ("propagate atom valuation to formula", c7)
                    , ("saturate under ∀-clauses (S_∀)",      c8)
                    ]
                  traceIfLooping
                    | n <= 10   = id
                    | otherwise = trace $ render $ vsep
                        [ text "Simplifier iteration" <-> int n <> colon
                        , fsep $ text "The reduction-rules for" :
                                (punctuate comma $ map (text . fst) changes) ++
                                [text "were applied to the following constraint system."]
                        , nest 2 (prettySystem se0)
                        ]

              traceIfLooping $ go (n + 1) (map snd changes)


-- | CR-rule *N6*: add ordering constraints between all KU-actions and
-- KD-conclusions.
exploitUniqueMsgOrder :: Reduction ()
exploitUniqueMsgOrder = do
    kdConcs   <- gets (M.fromList . map (\(i, _, m) -> (m, i)) . allKDConcs)
    kuActions <- gets (M.fromList . map (\(i, _, m) -> (m, i)) . allKUActions)
    -- We can add all elements where we have an intersection
    F.mapM_ (uncurry insertLess) $ M.intersectionWith (,) kdConcs kuActions

-- | CR-rules *DG4*, *N5_u*, and *N5_d*: enforcing uniqueness of *Fresh* rule
-- instances, *KU*-actions, and *KD*-conclusions.
--
-- Returns 'Changed' if a change was done.
enforceNodeUniqueness :: Reduction (ChangeIndicator, ChangeIndicator, ChangeIndicator)
enforceNodeUniqueness =
    (,,)
      <$> (merge (const $ return Unchanged) freshRuleInsts)
      <*> (merge (solveRuleEqs SplitNow)    kdConcs)
      <*> (merge (solveFactEqs SplitNow)    kuActions)
  where
    -- *DG4*
    freshRuleInsts se = do
        (i, ru) <- M.toList $ get sNodes se
        guard (isFreshRule ru)
        return (ru, ((), i))  -- no need to merge equal rules

    -- *N5_d*
    kdConcs sys = (\(i, ru, m) -> (m, (ru, i))) <$> allKDConcs sys

    -- *N5_u*
    kuActions se = (\(i, fa, m) -> (m, (fa, i))) <$> allKUActions se

    merge :: Ord b
          => ([Equal a] -> Reduction ChangeIndicator)
             -- ^ Equation solver for 'Equal a'
          -> (System -> [(b,(a,NodeId))])
             -- ^ Candidate selector
          -> Reduction ChangeIndicator                  --
    merge solver candidates = do
        changes <- gets (map mergers . groupSortOn fst . candidates)
        mconcat <$> sequence changes
      where
        mergers []                          = unreachable "enforceUniqueness"
        mergers ((_,(xKeep, iKeep)):remove) =
            mappend <$> solver         (map (Equal xKeep . fst . snd) remove)
                    <*> solveNodeIdEqs (map (Equal iKeep . snd . snd) remove)

-- | CR-rule *DG4*: enforcing uniqueness of *Fresh* rule
-- instances.
--
-- Returns 'Changed' if a change was done.
enforceFreshAndKuNodeUniqueness :: Reduction (ChangeIndicator, ChangeIndicator)
enforceFreshAndKuNodeUniqueness =
    (,)
      <$> (merge (const $ return Unchanged) freshRuleInsts)
      <*> (merge (solveFactEqs SplitNow)    kuActions)
  where
    -- *DG4*
    freshRuleInsts se = do
        (i, ru) <- M.toList $ get sNodes se
        guard (isFreshRule ru)
        return (ru, ((), i))  -- no need to merge equal rules

    -- *N5_u*
    kuActions se = (\(i, fa, m) -> (m, (fa, i))) <$> allKUActions se

    merge :: Ord b
          => ([Equal a] -> Reduction ChangeIndicator)
             -- ^ Equation solver for 'Equal a'
          -> (System -> [(b,(a,NodeId))])
             -- ^ Candidate selector
          -> Reduction ChangeIndicator                  --
    merge solver candidates = do
        changes <- gets (map mergers . groupSortOn fst . candidates)
        mconcat <$> sequence changes
      where
        mergers []                          = unreachable "enforceFreshAndKuUniqueness"
        mergers ((_,(xKeep, iKeep)):remove) =
            mappend <$> solver         (map (Equal xKeep . fst . snd) remove)
                    <*> solveNodeIdEqs (map (Equal iKeep . snd . snd) remove)
                    

-- | CR-rules *DG2_1* and *DG3*: merge multiple incoming edges to all facts
-- and multiple outgoing edges from linear facts.
enforceEdgeUniqueness :: Reduction ChangeIndicator
enforceEdgeUniqueness = do
    se <- gets id
    let edges = S.toList (get sEdges se)
    (<>) <$> mergeNodes eSrc eTgt edges
         <*> mergeNodes eTgt eSrc (filter (proveLinearConc se . eSrc) edges)
  where
    -- | @proveLinearConc se (v,i)@ tries to prove that the @i@-th
    -- conclusion of node @v@ is a linear fact.
    proveLinearConc se (v, i) =
        maybe False (isLinearFact . (get (rConc i))) $
            M.lookup v $ get sNodes se

    -- merge the nodes on the 'mergeEnd' for edges that are equal on the
    -- 'compareEnd'
    mergeNodes mergeEnd compareEnd edges
      | null eqs  = return Unchanged
      | otherwise = do
            -- all indices of merged premises and conclusions must be equal
            contradictoryIf (not $ and [snd l == snd r | Equal l r <- eqs])
            -- nodes must be equal
            solveNodeIdEqs $ map (fmap fst) eqs
      where
        eqs = concatMap (merge mergeEnd) $ groupSortOn compareEnd edges

        merge _    []            = error "exploitEdgeProps: impossible"
        merge proj (keep:remove) = map (Equal (proj keep) . proj) remove

-- | Special version of CR-rule *S_at*, which is only applied to solve actions
-- that are guaranteed not to result in case splits.
solveUniqueActions :: Reduction ChangeIndicator
solveUniqueActions = do
    rules       <- nonSilentRules <$> askM pcRules
    actionAtoms <- gets unsolvedActionAtoms

    -- FIXME: We might cache the result of this static computation in the
    -- proof-context, e.g., in the 'ClassifiedRules'.
    let uniqueActions = [ x | [x] <- group (sort ruleActions) ]
        ruleActions   = [ (tag, length ts)
                        | ru <- rules, Fact tag ts <- get rActs ru ]

        isUnique (Fact tag ts) =
           (tag, length ts) `elem` uniqueActions
           -- multiset union leads to case-splits because there
           -- are multiple unifiers
           && null [ () | t <- ts, FUnion _ <- return (viewTerm2 t) ]

        trySolve (i, fa)
          | isUnique fa = solveGoal (ActionG i fa) >> return Changed
          | otherwise   = return Unchanged

    mconcat <$> mapM trySolve actionAtoms

-- | Reduce all formulas as far as possible. See 'insertFormula' for the
-- CR-rules exploited in this step. Note that this step is normally only
-- required to decompose the formula in the initial constraint system.
reduceFormulas :: Reduction ChangeIndicator
reduceFormulas = do
    formulas <- getM sFormulas
    applyChangeList $ do
        fm <- S.toList formulas
        guard (reducibleFormula fm)
        return $ do modM sFormulas $ S.delete fm
                    insertFormula fm

-- | Try to simplify the atoms contained in the formulas. See
-- 'partialAtomValuation' for an explanation of what CR-rules are exploited
-- here.
evalFormulaAtoms :: Reduction ChangeIndicator
evalFormulaAtoms = do
    ctxt      <- ask
    valuation <- gets (partialAtomValuation ctxt)
    formulas  <- getM sFormulas
    applyChangeList $ do
        fm <- S.toList formulas
        case simplifyGuarded valuation fm of
          Just fm' -> return $ do
              case fm of
                GDisj disj -> markGoalAsSolved "simplified" (DisjG disj)
                _          -> return ()
              modM sFormulas       $ S.delete fm
              modM sSolvedFormulas $ S.insert fm
              insertFormula fm'
          Nothing  -> []

-- | A partial valuation for atoms. The return value of this function is
-- interpreted as follows.
--
-- @partialAtomValuation ctxt sys ato == Just True@ if for every valuation
-- @theta@ satisfying the graph constraints and all atoms in the constraint
-- system @sys@, the atom @ato@ is also satisfied by @theta@.
--
-- The interpretation for @Just False@ is analogous. @Nothing@ is used to
-- represent *unknown*.
--
partialAtomValuation :: ProofContext -> System -> LNAtom -> Maybe Bool
partialAtomValuation ctxt sys =
    eval
  where
    runMaude   = (`runReader` get pcMaudeHandle ctxt)
    before     = alwaysBefore sys
    lessRel    = rawLessRel sys
    nodesAfter = \i -> filter (i /=) $ S.toList $ D.reachableSet [i] lessRel

    -- | 'True' iff there in every solution to the system the two node-ids are
    -- instantiated to a different index *in* the trace.
    nonUnifiableNodes :: NodeId -> NodeId -> Bool
    nonUnifiableNodes i j = maybe False (not . runMaude) $
        (unifiableRuleACInsts) <$> M.lookup i (get sNodes sys)
                               <*> M.lookup j (get sNodes sys)

    -- | Try to evaluate the truth value of this atom in all models of the
    -- constraint system 'sys'.
    eval ato = case ato of
          Action (ltermNodeId' -> i) fa
            | ActionG i fa `M.member` get sGoals sys -> Just True
            | otherwise ->
                case M.lookup i (get sNodes sys) of
                  Just ru
                    | any (fa ==) (get rActs ru)                                -> Just True
                    | all (not . runMaude . unifiableLNFacts fa) (get rActs ru) -> Just False
                  _                                                             -> Nothing

          Less (ltermNodeId' -> i) (ltermNodeId' -> j)
            | i == j || j `before` i             -> Just False
            | i `before` j                       -> Just True
            | isLast sys i && isInTrace sys j    -> Just False
            | isLast sys j && isInTrace sys i &&
              nonUnifiableNodes i j              -> Just True
            | otherwise                          -> Nothing

          EqE x y
            | x == y                                -> Just True
            | not (runMaude (unifiableLNTerms x y)) -> Just False
            | otherwise                             ->
                case (,) <$> ltermNodeId x <*> ltermNodeId y of
                  Just (i, j)
                    | i `before` j || j `before` i  -> Just False
                    | nonUnifiableNodes i j         -> Just False
                  _                                 -> Nothing

          Last (ltermNodeId' -> i)
            | isLast sys i                       -> Just True
            | any (isInTrace sys) (nodesAfter i) -> Just False
            | otherwise ->
                case get sLastAtom sys of
                  Just j | nonUnifiableNodes i j -> Just False
                  _                              -> Nothing



-- | CR-rule *S_∀*: insert all newly implied formulas.
insertImpliedFormulas :: Reduction ChangeIndicator
insertImpliedFormulas = do
    sys <- gets id
    hnd <- getMaudeHandle
    applyChangeList $ do
        clause  <- (S.toList $ get sFormulas sys) ++
                   (S.toList $ get sLemmas sys)
        implied <- impliedFormulas hnd sys clause
        if ( implied `S.notMember` get sFormulas sys &&
             implied `S.notMember` get sSolvedFormulas sys )
          then return (insertFormula implied)
          else []

