{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE DoAndIfThenElse    #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
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
import qualified Data.Foldable                      as F
import           Data.List
import qualified Data.Map                           as M
import qualified Data.Set                           as S
import           Data.Maybe                         (mapMaybe, listToMaybe)

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.Reader
import           Control.Monad.State                (gets)

import           Safe                           (headMay)

import           Extension.Data.Label               hiding (modify)
import           Extension.Prelude

import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.System
import           Theory.Model
import           Theory.Text.Pretty
import           Theory.Tools.InjectiveFactInstances

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
        -- Add ordering constraint from injective facts
        addNonInjectiveFactInstances
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
              c9 <- freshOrdering
              c10 <- simpSubterms
              c11 <- simpInjectiveFactEqMon

              -- Report on looping behaviour if necessary
              let changes = filter ((Changed ==) . snd) $
                    [ ("unique fresh instances (DG4)",                    c1)
--                     , ("unique K↓-facts (N5↓)",                           c2)
                    , ("unique K↑-facts (N5↑)",                           c3)
                    , ("unique (linear) edges (DG2 and DG3)",             c4)
                    , ("solve unambiguous actions (S_@)",                 c5)
                    , ("decompose trace formula",                         c6)
                    , ("propagate atom valuation to formula",             c7)
                    , ("saturate under ∀-clauses (S_∀)",                  c8)
                    , ("orderings for ~vars (S_fresh-order)",             c9)
                    , ("simplification of SubtermStore",                  c10)
                    , ("equations and monotonicity from injective Facts", c11)
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
              c9 <- freshOrdering
              c10 <- simpSubterms
              c11 <- simpInjectiveFactEqMon

              -- Report on looping behaviour if necessary
              let changes = filter ((Changed ==) . snd) $
                    [ ("unique fresh instances (DG4)",                    c1)
                    , ("unique K↓-facts (N5↓)",                           c2)
                    , ("unique K↑-facts (N5↑)",                           c3)
                    , ("unique (linear) edges (DG2 and DG3)",             c4)
                    , ("solve unambiguous actions (S_@)",                 c5)
                    , ("decompose trace formula",                         c6)
                    , ("propagate atom valuation to formula",             c7)
                    , ("saturate under ∀-clauses (S_∀)",                  c8)
                    , ("orderings for ~vars (S_fresh-order)",             c9)
                    , ("simplification of SubtermStore",                  c10)
                    , ("equations and monotonicity from injective Facts", c11)
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
    F.mapM_ insertLess (M.map (\(x,y)-> LessAtom x y NormalForm)
              $ M.intersectionWith (,) kdConcs kuActions)

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
                        | ru <- rules, Fact tag _ ts <- get rActs ru ]

        isUnique (Fact tag _ ts) =
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
    verbose   <- getVerbose
    valuation <- gets (partialAtomValuation ctxt)
    formulas  <- getM sFormulas
    applyChangeList $ do
        fm <- S.toList formulas
        case simplifyGuarded valuation fm verbose of
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
-- FIXME this function is almost identical to System>safePartial evaluation -> join them
--
partialAtomValuation :: ProofContext -> System -> LNAtom -> Maybe Bool
partialAtomValuation ctxt sys =
    eval
  where
    runMaude   = (`runReader` get pcMaudeHandle ctxt)
    before     = alwaysBefore sys
    lessRel    = rawLessRel sys
    nodesAfter = \i -> filter (i /=) $ S.toList $ D.reachableSet [i] lessRel
    reducible  = reducibleFunSyms $ mhMaudeSig $ get pcMaudeHandle ctxt
    sst        = get sSubtermStore sys

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

          Subterm small big                      -> isTrueFalse reducible (Just sst) (small, big)

          Last (ltermNodeId' -> i)
            | isLast sys i                       -> Just True
            | any (isInTrace sys) (nodesAfter i) -> Just False
            | otherwise ->
                case get sLastAtom sys of
                  Just j | nonUnifiableNodes i j -> Just False
                  _                              -> Nothing

          Syntactic _                            -> Nothing



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

-- | CR-rule *S_fresh-order*:
--
-- `i0:f0`, `j:g`, `t1 ⊂ s1`, ..., `t_(n-1) ⊂ s_(n-1)`
-- -- insert --
-- `im<j`
-- where `∃u,v,Fact,tn` with `prems(f0)u = Fr(~s0)` and `prems(g)v = Fact(tn))`* and `j:g ∉ route(i0:f0, ~s0)`
-- if `si` is syntactically in `t_(i+1)` and not below a cancellation operator
-- where `route(i0:f0, ~s0)` is the maximal list `[i0:f0,...,im:fm]` where for two consecutive elements `ia:fa` `ib:fb` holds:
-- - `fa` has only one conclusion which is a non-persistent fact (especially not a `!KU` / `!KD`)
-- - `∃ w,t` with `concs(fa)1 = prems(fb)w = Fact(t)`
-- - and there is an edge `(ia,1) ↣ (ib,ub)`
freshOrdering :: Reduction ChangeIndicator
freshOrdering = do
  ctxt <- ask
  sys <- gets id
  let runMaude = (`runReader` get pcMaudeHandle ctxt)
  let nonUnifiableNodes i j = maybe False (not . runMaude) $ unifiableRuleACInsts <$> M.lookup i (get sNodes sys) <*> M.lookup j (get sNodes sys)

  rawSubterms <- rawSubtermRel <$> getM sSubtermStore
  el <- elemNotBelowReducible . reducibleFunSyms . mhMaudeSig <$> getMaudeHandle
  route <- getRoute <$> getM sNodes <*> getM sEdges
  nodes <- M.assocs <$> getM sNodes
  let freshVars = concatMap getFreshVars nodes  -- all (i,~x) where Fr(~x) is a premise of a node at position i
  let subterms = rawSubterms ++ [ (f,f) | (_,f) <- freshVars]  -- add a fake-subterm (f,f) for each freshVar f to the graph
  let graph = M.fromList $ map (\(_,x) -> (x, [ st | st <- subterms, x `el` fst st])) subterms  -- graph that has subterms (s,t) as nodes and edges (s,t) -> (u,v) if t `el` u
  let termsContaining = [((nid,x), map snd $ S.toList $ floodFill graph S.empty (x,x)) | (nid,x) <- freshVars]  -- (freshNodeId, t) for all terms t that have to contain x. So also the ones transitively connected by ⊏ to x
  let newLesses = [ LessAtom i j Fresh | (j,r) <- nodes, i <- connectNodeToFreshes el termsContaining r, i/=j]  -- new ordering constraints that can be added (or enhanced and then added)
  let enhancedLesses = [ LessAtom (last rs) j Fresh | (LessAtom i j _) <- newLesses, (frI, _) <- freshVars, i == frI, rs <- [route frI], length rs > 1, all (nonUnifiableNodes j) (tail rs)]  -- improved orderings according to routeOfFreshVar
  let allLesses = newLesses ++ enhancedLesses

  oldLesses <- gets (get sLessAtoms)
  mapM_ insertLess allLesses
  modifiedLesses <- gets (get sLessAtoms)
  return $ if oldLesses == modifiedLesses
    then Unchanged
    else Changed

    where
      -- returns all (i,~x) where Fr(~x) is a premise of a node at position i
      getFreshVars :: (NodeId, RuleACInst) -> [(NodeId, LNTerm)]
      getFreshVars (idx, get rPrems -> prems) = mapMaybe (\prem -> case factTag prem of
          FreshFact -> Just (idx, head $ factTerms prem)
          _         -> Nothing
        ) prems

      -- the route function as described in the documentation of freshOrdering
      getRoute :: M.Map NodeId RuleACInst -> S.Set Edge -> NodeId -> [NodeId]  -- also needs nodes and edges
      getRoute nodeMap edges nid = plainRoute nid
        where
          edgeMap :: M.Map NodeConc NodeId
          edgeMap = M.fromList [(eSrc edge, fst $ eTgt edge) | edge <- S.toList edges]

          plainRoute :: NodeId -> [NodeId]
          plainRoute i = case i `M.lookup` nodeMap of
            Just (enumConcs -> [(concIdx, fact)]) | isLinearFact fact -> i : maybe [] plainRoute ((i,concIdx) `M.lookup` edgeMap)
            _ -> [i]

      floodFill :: M.Map LNTerm [(LNTerm, LNTerm)] -> S.Set (LNTerm, LNTerm) -> (LNTerm, LNTerm) -> S.Set (LNTerm, LNTerm)
      floodFill graph visited (s,x)
        | (s,x) `S.member` visited = visited
        | otherwise                = foldl (floodFill graph) (S.insert (s,x) visited) (M.findWithDefault [] x graph)

      connectNodeToFreshes :: (LNTerm -> LNTerm -> Bool) -> [((NodeId, LNTerm), [LNTerm])] -> RuleACInst -> [NodeId]
      connectNodeToFreshes _ [] _ = []
      connectNodeToFreshes el (((nid,freshVar), containing):xs) r | allPremsNotF =
          case listToMaybe [nid | t <- containing, t' <- concatMap factTerms (concatMap (`get` r) [rPrems, rActs]), t `el` t'] of
            Just nid1 -> nid1 : connectNodeToFreshes el xs r
            _         ->        connectNodeToFreshes el xs r
        where
          allPremsNotF = freshFact freshVar `notElem` get rPrems r
      connectNodeToFreshes el (_:xs) r = connectNodeToFreshes el xs r


-- | simplify the subterm store
-- It also computes contradictions (which are indicated by isContradictory)
-- These contradictions are only later handled by Contradictions.hs to yield meaningful user output.
--
-- executes simplifySubtermStore
-- removes all SubtermGoals and inserts the new ones (if the new ones aren't [])
-- adds the equations from negSubterm splits
-- determines wether anything has changed
simpSubterms :: Reduction ChangeIndicator
simpSubterms = do
    reducible <- reducibleFunSyms . mhMaudeSig <$> getMaudeHandle
    sst <- getM sSubtermStore
    (sst1, formulas, goals) <- simpSubtermStore reducible sst

    -- updateSubtermStore
    setM sSubtermStore sst1
    let ignoringOldSst1 = set oldNegSubterms (get oldNegSubterms sst) sst1
    let changedStore = ignoringOldSst1 /= sst

    -- uptate goals
    changedGoals <- if null goals then return False else do  -- if goals = [] then goalsToRemove = [] holds because goals cannot disappear due to substitution
      oldOpenGoals <- gets plainOpenGoals
      oldGoals <- M.toList <$> getM sGoals
      let goalsToRemove = [SubtermG st | (SubtermG st, _) <- oldOpenGoals] \\ goals
      let goalsToAdd = goals \\ [SubtermG st | (SubtermG st, _) <- oldGoals]
      forM_ goalsToRemove (modM sGoals . M.delete)
      forM_ goalsToAdd (`insertGoal` False)
      return ((length goalsToAdd + length goalsToRemove) > 0)

    -- insert formulas
    allFormulas <- S.union <$> getM sSolvedFormulas <*> getM sFormulas
    forM_ formulas insertFormula
    let changedFormulas = not $ all (`S.member` allFormulas) formulas
    return $ if changedStore || changedGoals || changedFormulas then Changed else Unchanged
    -- TODO take care acFormulas are not inserted twice with different newVar's (didn't happen so far)
    --          if z ⊏ x+y is substituted to z ⊏ x+y'+y'' then
    --          the formula ∀newVar... in the LNGuarded formulas is updated automatically correctly.
    --          We only have to add z ⊏ y', z ⊏ y'' and could remove z ⊏ y'+y'' (formerly z ⊏ y)
    --          However, I'm not sure wether removing z ⊏ y'+y'' and the corresponding ∀newVar is beneficial:
    --            ∀n. n+z ≠ y'+y'' is clearly subsumed by ∀n. n+z ≠ x+y'+y''
    --            but it is hard to search for these collisions.


-- | if there are two instances @i and @j of an injective fact with the same first term, then
-- - (1) for each two terms s,t at a constant position, s=t is inserted
-- - for each two terms s,t at a strictly increasing position:
--   - (2) if s=t, then i=j is inserted
--   - (3) if s⊏t, then i<j is inserted
--   - (4) if i<j or j<i, then s≠t is inserted  -- only needed as a semi-replacement of (6) (especially in combination with 5) because (2) is directly applied if s=t
--   - (5) if ¬s⊏t and ¬s=t, (i.e., t⊏s must hold because of strict monotonicity) then j<i is inserted
--   - (6) if i<j, then s⊏t is inserted    -- has the potential to break many old proofs because subterms appear in the goals
-- - for each two terms s,t at an increasing position:
--   - (3) if s⊏t, then i<j is inserted
--   - (5) if ¬s⊏t and ¬s=t, (i.e., t⊏s must hold because of monotonicity) then j<i is inserted
--   - (6.1) if i<j, then (s⊏t ∨ s=t) is inserted    -- has the potential to break many old proofs because subterms appear in the goals
-- - for decreasing and strictly decreasing, the inverse of the increasing cases is done
simpInjectiveFactEqMon :: Reduction ChangeIndicator
simpInjectiveFactEqMon = do
  -- get some values out of the reduction
  inj <- S.toList <$> askM pcInjectiveFactInsts
  nodes <- getM sNodes
  sys <- gets id
  reducible <- reducibleFunSyms . mhMaudeSig <$> getMaudeHandle
  sst <- getM sSubtermStore
  let triviallySmaller small big = Just True == isTrueFalse reducible (Just sst) (small, big)
  let triviallyNotSmaller small big = Just False == isTrueFalse reducible (Just sst) (small, big)

  oldFormulas <- S.union <$> getM sFormulas <*> getM sSolvedFormulas
  let inequalities = S.fromList $ concatMap (\case
                    GGuarded All [] [EqE (bTermToLTerm->s) (bTermToLTerm->t)] gf | gf == gfalse -> [(s, t), (t, s)]
                    _                                                                           -> [])
                      $ S.toList oldFormulas
  let notIneq s t = (s,t) `S.notMember` inequalities
  let ineq s t = (s,t) `S.member` inequalities

  --  :: (MonotonicBehaviour, (NodeId, LNTerm), (NodeId, LNTerm)) -> ([LNGuarded], [(NodeId, NodeId)])
  let simpSingle (behaviour, (i, s), (j, t)) = --trace (show ("simpSingle", behaviour, i, s, j, t)) $
         case behaviour of
            Unspecified -> ([], [])
            Unstable -> ([], [])
            Decreasing -> simpSingle (Increasing, (j, s), (i, t))
            StrictlyDecreasing -> simpSingle (StrictlyIncreasing, (j, s), (i, t))
            Constant -> ([GAto $ EqE (lTermToBTerm s) (lTermToBTerm t) | s/=t], [])  -- (1)
            StrictlyIncreasing ->
                ([GAto $ EqE (varTerm $ Free i) (varTerm $ Free j) | s==t]  -- (2)
              ++ [gnotAtom $ EqE (lTermToBTerm s) (lTermToBTerm t) | alwaysBefore sys i j || alwaysBefore sys j i, notIneq s t]   -- (4)
              -- ++ [GAto $ Subterm (lTermToBTerm s) (lTermToBTerm t) | alwaysBefore sys i j, i/=j, not $ triviallySmaller s t]   -- (6)
                , [(i, j) | triviallySmaller    s t, not $ alwaysBefore sys i j]   -- (3)
              ++ [(j, i) | triviallyNotSmaller s t, not $ alwaysBefore sys j i, ineq s t]) -- (5)
            Increasing -> ([]--, [])
              --([ gdisj [--GAto $ Subterm (lTermToBTerm s) (lTermToBTerm t),
              --          GAto $ EqE (lTermToBTerm s) (lTermToBTerm t)]
              --  | alwaysBefore sys i j, i/=j, not $ triviallySmaller s t, s /= t]   -- (6.1)
              , snd $ simpSingle (StrictlyIncreasing, (i, s), (j, t)))

  -- generate and execute changes
  let (newFormulas, newLesses) = (concat *** concat) $ unzip $ map simpSingle (getPairs inj nodes)
  mapM_ insertFormula newFormulas
  mapM_ (\(x, y) -> insertLess (LessAtom x y InjectiveFacts)) -- $ trace (show ("newLesses", newLesses))
                              newLesses

  -- check if anything changed
  updatedFormulas <- S.union <$> getM sFormulas <*> getM sSolvedFormulas
  return $ if
      updatedFormulas == oldFormulas &&
      null newLesses
      then Unchanged else Changed

    where
      getPairs :: [(FactTag, [[MonotonicBehaviour]])] -> M.Map NodeId RuleACInst -> [(MonotonicBehaviour, (NodeId, LNTerm), (NodeId, LNTerm))]
      getPairs [] _ = []
      getPairs ((tag, behaviours):rest) nodes = paired ++ getPairs rest nodes
        where
          -- Flatten a (n-1)-tuple by only expanding the right-hand side of the tuple
          -- This function errors when n is bigger than the _length_ of the tuple
          -- E.g., shapeTerm 2 <t1, t2> = [t1, t2]
          -- E.g., shapeTerm 2 <<t1, t2>, t3> = [<t1, t2>, t3]
          -- Note that the above list has only 2 elements as the first tuple is not flattened
          -- E.g., shapeTerm 3 <t1, t2> throws an error
          -- Note that this code is identical to existing code in `InjectiveFactInstances.hs`.
          shapeTerm :: Int -> LNTerm -> [LNTerm]
          shapeTerm x (viewTerm2 -> FPair t1 t2) | x>1 = t1 : shapeTerm (x-1) t2
          shapeTerm x t | x>1 = error ("shapeTerm: the term (" ++ show t ++ ") does not have enough pairs."
            ++ "\nOccured in fact: (" ++ show tag ++") with behavior " ++ show behaviours)
          shapeTerm x t | x==1 = [t]
          shapeTerm _ _ = error "shapeTerm: cannot take an integer with size less than 1"

          -- Given an injective fact instance and the behaviour/shape of the corresponding FactTag
          -- (bound by the behaviours variable introduced in 'getPairs'), return a tuple that contains
          -- its _injective identitifer_ and 
          -- E.g., For behaviour/shape = [[=, =]]
          -- trimmedPairTerms S(~id, <a, b>) = (~id, [(=, a), (=, b)])
          -- E.g., For behaviour/shape = [[=]]
          -- trimmedPairTerms S(~id, <a, b>) = (~id, [(=, <a, b>)])
          -- E.g., For behaviour/shape = [[=, <]]
          -- trimmedPairTerms S(~id, <<a, b>, c>) = (~id, [(=, <a, b>), (<, c)])
          trimmedPairTerms :: LNFact -> (LNTerm, [(MonotonicBehaviour, LNTerm)])
          trimmedPairTerms (factTerms -> firstTerm:terms) = (firstTerm, concat $ zipWith (\behaviour term -> zip behaviour (shapeTerm (length behaviour) term)) behaviours terms )
          trimmedPairTerms _ = error "a fact with no terms cannot be injective"

          -- For each rule instance, filter its rhs for the current injective fact 'tag'
          -- and compute the pairs via 'trimmedPairTerms'
          behaviourTerms :: M.Map NodeId [(LNTerm, [(MonotonicBehaviour, LNTerm)])]
          behaviourTerms = M.map (map trimmedPairTerms . filter (\x -> factTag x == tag) . get rPrems) nodes  --all node premises with the matching tag

          -- Returns a list of pairs (i, s), (j, t) together with the behaviour b
          -- between s and t. i and j are the time points where the fact instances
          -- occured that contain s and t respectively.
          -- Example: For an injective fact S with behaviour/shape [[=, <]],
          -- S(~id, <a, b>) @ i and S(~id, <c, d>) @ j, we have
          -- paired = [(=, (i, a), (j, c)), (<, (i, b), (j, d))]
          paired :: [(MonotonicBehaviour, (NodeId, LNTerm), (NodeId, LNTerm))]
          paired = [(b, (i, s), (j,t)) |
            (i, l1) <- M.toList behaviourTerms,
            (j, l2) <- M.toList behaviourTerms,
            (first1, ss) <- l1,
            (first2, tt) <- l2,
            first1 == first2,
            i /= j,
            ((b, s),(_,t)) <- zip ss tt  -- the b and _ are automatically the same
            ]

-- | Compute all less relations implied by injective fact instances.
--
-- Formally, they are computed as follows. Let 'f' be a fact symbol with
-- injective instances. Let i and k be temporal variables ordered
-- according to
--
--   i < k
--
-- and let there be an edge from (i,u) to (k,w) for some indices u and w
-- corresponding to fact f(t,...).
-- If:
--    -  j<k & f(t,...) occurs at j in prems, then j<i (j<>i as in i f occurs in concs).
--    -  i<j & f(t,...) occurs at j concs, then k<j.
nonInjectiveFactInstances :: ProofContext -> System -> [(NodeId, NodeId)]
nonInjectiveFactInstances ctxt se = do
    Edge c@(i, _) (k, _) <- S.toList $ get sEdges se
    let kFaPrem            = nodeConcFact c se
        kTag               = factTag kFaPrem
        kTerm              = firstTerm kFaPrem
        conflictingFact fa = factTag fa == kTag && firstTerm fa == kTerm
        injFacts           = get pcInjectiveFactInsts ctxt
    guard (kTag `S.member` S.map fst injFacts)
--    j <- S.toList $ D.reachableSet [i] less
    (j, _) <- M.toList $ get sNodes se
    -- check that j<k
    guard  (k `S.member` D.reachableSet [j] less)
    let isCounterExample checkRule = (j /= i) && (j /= k) &&
                           maybe False checkRule (M.lookup j $ get sNodes se)
        checkRuleJK jRu    = (
                           -- check that f(t,...) occurs at j in prems and j<k
                           any conflictingFact (get rPrems jRu ++ get rConcs jRu) &&
                           (k `S.member` D.reachableSet [j] less) &&
                            nonUnifiableNodes j i
                           )
        checkRuleIJ jRu    = (
                           -- check that f(t,...) occurs at j in concs and i<j
                           any conflictingFact (get rPrems jRu ++  get rConcs jRu) &&
                           (j `S.member` D.reachableSet [i] less) &&
                            nonUnifiableNodes k j
                           )
    if (isCounterExample checkRuleJK) then return (j,i)
      else do
         guard (isCounterExample checkRuleIJ)
         return (k,j)
    -- (guard (isCounterExample checkRuleConcs)
    --  return (k,j))
--    insertLess k i
--    return (i, j, k) -- counter-example to unique fact instances
  where
    less      = rawLessRel se
    firstTerm = headMay . factTerms
    runMaude   = (`runReader` get pcMaudeHandle ctxt)
    nonUnifiableNodes :: NodeId -> NodeId -> Bool
    nonUnifiableNodes i j = maybe False (not . runMaude) $
        (unifiableRuleACInsts) <$> M.lookup i (get sNodes se)
                               <*> M.lookup j (get sNodes se)

addNonInjectiveFactInstances :: Reduction ()
addNonInjectiveFactInstances = do
  se <- gets id
  ctxt <- ask
  let list = map (\(x,y)-> LessAtom x y InjectiveFacts) $ nonInjectiveFactInstances ctxt se
  mapM_ insertLess list



 
