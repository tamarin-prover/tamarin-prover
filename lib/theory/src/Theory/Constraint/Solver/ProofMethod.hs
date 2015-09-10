{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE ViewPatterns    #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier & Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Proof methods and heuristics: the external small-step interface to the
-- constraint solver.
module Theory.Constraint.Solver.ProofMethod (
  -- * Proof methods
    CaseName
  , ProofMethod(..)
  , DiffProofMethod(..)
  , execProofMethod
  , execDiffProofMethod

  -- ** Heuristics
  , GoalRanking(..)
  , goalRankingName
  , rankProofMethods
  , rankDiffProofMethods

  , Heuristic
  , roundRobinHeuristic
  , useHeuristic

  -- ** Pretty Printing
  , prettyProofMethod
  , prettyDiffProofMethod

) where

-- import           Debug.Trace

import           Data.Binary
import           Data.DeriveTH
import           Data.Function                             (on)
import           Data.Label                                hiding (get)
import qualified Data.Label                                as L
import           Data.List                                 (intersperse,partition,groupBy,sortBy)
import qualified Data.Map                                  as M
import           Data.Maybe                                (catMaybes)
import           Data.Monoid
import           Data.Ord                                  (comparing)
import qualified Data.Set                                  as S
import           Extension.Prelude                         (sortOn)

import           Control.Basics
import           Control.DeepSeq
import qualified Control.Monad.Trans.PreciseFresh          as Precise

import           Theory.Constraint.Solver.CaseDistinctions
import           Theory.Constraint.Solver.Contradictions
import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.Solver.Simplify
-- import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model
import           Theory.Text.Pretty

------------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------------

-- | @uniqueListBy eq changes xs@ zips the @changes@ with all sequences equal
-- elements in the list.
--
-- > uniqueListBy compare id (const [ (++ show i) | i <- [1..] ]) ["a","b","a"] =
-- > ["a1","b","a2"]
--
uniqueListBy :: (a -> a -> Ordering) -> (a -> a) -> (Int -> [a -> a]) -> [a] -> [a]
uniqueListBy ord single distinguish xs0 =
      map fst
    $ sortBy (comparing snd)
    $ concat $ map uniquify $ groupBy (\x y -> ord (fst x) (fst y) == EQ)
    $ sortBy (ord `on` fst)
    $ zip xs0 [(0::Int)..]
  where
    uniquify []      = error "impossible"
    uniquify [(x,i)] = [(single x, i)]
    uniquify xs      = zipWith (\f (x,i) -> (f x, i)) dist xs
      where
        dist = distinguish $ length xs


------------------------------------------------------------------------------
-- Proof Methods
------------------------------------------------------------------------------

-- | Every case in a proof is uniquely named.
type CaseName = String

-- | Sound transformations of sequents.
data ProofMethod =
    Sorry (Maybe String)                 -- ^ Proof was not completed
  | Solved                               -- ^ An attack was found
  | Simplify                             -- ^ A simplification step.
  | SolveGoal Goal                       -- ^ A goal that was solved.
  | Contradiction (Maybe Contradiction)  -- ^ A contradiction could be
                                         -- derived, possibly with a reason.
  | Induction                            -- ^ Use inductive strengthening on
                                         -- the single formula constraint in
                                         -- the system.
  deriving( Eq, Ord, Show )

-- | Sound transformations of diff sequents.
-- FIXME
data DiffProofMethod =
    DiffSorry (Maybe String)                 -- ^ Proof was not completed
  | DiffMirrored                             -- ^ No attack was found
  | DiffAttack                               -- ^ A potential attack was found
  | DiffRuleEquivalence                      -- ^ Consider all rules
--   | DiffTrivial                              -- ^ The rule is trivially sound - REMOVED and merged with solved!
  | DiffBackwardSearch                       -- ^ Do the backward search starting from a rule
  | DiffBackwardSearchStep ProofMethod       -- ^ A step in the backward search starting from a rule
  deriving( Eq, Ord, Show )

  
instance HasFrees ProofMethod where
    foldFrees f (SolveGoal g)     = foldFrees f g
    foldFrees f (Contradiction c) = foldFrees f c
    foldFrees _ _                 = mempty

    foldFreesOcc  _ _ = const mempty

    mapFrees f (SolveGoal g)     = SolveGoal <$> mapFrees f g
    mapFrees f (Contradiction c) = Contradiction <$> mapFrees f c
    mapFrees _ method            = pure method

instance HasFrees DiffProofMethod where
--     foldFrees f (SolveGoal g)     = foldFrees f g
--     foldFrees f (Contradiction c) = foldFrees f c
    foldFrees _ _                 = mempty

    foldFreesOcc  _ _ = const mempty

--     mapFrees f (SolveGoal g)     = SolveGoal <$> mapFrees f g
--     mapFrees f (Contradiction c) = Contradiction <$> mapFrees f c
    mapFrees _ method            = pure method

-- Proof method execution
-------------------------


-- @execMethod rules method se@ checks first if the @method@ is applicable to
-- the sequent @se@. Then, it applies the @method@ to the sequent under the
-- assumption that the @rules@ describe all rewriting rules in scope.
--
-- NOTE that the returned systems have their free substitution fully applied
-- and all variable indices reset.
execProofMethod :: ProofContext
                -> ProofMethod -> System -> Maybe (M.Map CaseName System)
execProofMethod ctxt method sys =
      case method of
        Sorry _                  -> return M.empty
        Solved
          | null (openGoals sys) -> return M.empty
          | otherwise            -> Nothing
        SolveGoal goal
          | goal `M.member` L.get sGoals sys -> execSolveGoal goal
          | otherwise                        -> Nothing
        Simplify                 -> singleCase simplifySystem
        Induction                -> M.map cleanupSystem <$> execInduction
        Contradiction _
          | null (contradictions ctxt sys) -> Nothing
          | otherwise                      -> Just M.empty
  where
    -- at this point it is safe to remove the free substitution, as all
    -- systems have it fully applied (by the virtue of a call to
    -- simplifySystem). We also reset the variable indices here.
    cleanupSystem =
         (`Precise.evalFresh` Precise.nothingUsed)
       . renamePrecise
       . set sSubst emptySubst


    -- expect only one or no subcase in the given case distinction
    singleCase m =
        case    removeRedundantCases ctxt [] id . map cleanupSystem
              . map fst . getDisj $ execReduction m ctxt sys (avoid sys) of
          []                  -> return $ M.empty
          [sys'] | check sys' -> return $ M.singleton "" sys'
                 | otherwise  -> mzero
          syss                ->
               return $ M.fromList (zip (map show [(1::Int)..]) syss)
      where check sys' = cleanupSystem sys /= sys'

    -- solve the given goal
    -- PRE: Goal must be valid in this system.
    execSolveGoal goal =
        return . makeCaseNames . removeRedundantCases ctxt [] snd
               . map (second cleanupSystem) . map fst . getDisj
               $ runReduction solver ctxt sys (avoid sys)
      where
        ths    = L.get pcCaseDists ctxt
        solver = do name <- maybe (solveGoal goal)
                                  (fmap $ concat . intersperse "_")
                                  (solveWithCaseDistinction ctxt ths goal)
                    simplifySystem
                    return name

        makeCaseNames =
            M.fromListWith (error "case names not unique")
          . uniqueListBy (comparing fst) id distinguish
          where
            distinguish n =
                [ (\(x,y) -> (x ++ "_case_" ++ pad (show i), y))
                | i <- [(1::Int)..] ]
              where
                l      = length (show n)
                pad cs = replicate (l - length cs) '0' ++ cs

    -- Apply induction: possible if the system contains only
    -- a single, last-free, closed formula.
    execInduction
      | sys == sys0 =
          case S.toList $ L.get sFormulas sys of
            [gf] -> case ginduct gf of
                      Right (bc, sc) -> Just $ insCase "empty_trace"     bc
                                             $ insCase "non_empty_trace" sc
                                             $ M.empty
                      _              -> Nothing
            _    -> Nothing

      | otherwise = Nothing
      where
        sys0 = set sFormulas (L.get sFormulas sys)
             $ set sLemmas (L.get sLemmas sys)
             $ emptySystem (L.get sCaseDistKind sys) (L.get sDiffSystem sys)

        insCase name gf = M.insert name (set sFormulas (S.singleton gf) sys)

-- @execDiffMethod rules method se@ checks first if the @method@ is applicable to
-- the sequent @se@. Then, it applies the @method@ to the sequent under the
-- assumption that the @rules@ describe all rewriting rules in scope.
--
-- NOTE that the returned systems have their free substitution fully applied
-- and all variable indices reset.
execDiffProofMethod :: DiffProofContext
                -> DiffProofMethod -> DiffSystem -> Maybe (M.Map CaseName DiffSystem)
execDiffProofMethod ctxt method sys = -- error $ show ctxt ++ show method ++ show sys -- return M.empty
      case method of
        DiffSorry _                                           -> return M.empty
        DiffBackwardSearch
          | (L.get dsProofType sys) == (Just RuleEquivalence) -> case (L.get dsCurrentRule sys, L.get dsSide sys) of
                                                                      (Just rule, Nothing) -> Just $ startBackwardSearch rule
                                                                      (_ , _)              -> Nothing
          | otherwise                                         -> Nothing
        DiffBackwardSearchStep meth
          | (L.get dsProofType sys) == (Just RuleEquivalence)
            && (meth /= (Contradiction (Just ForbiddenKD)))   -> case (L.get dsCurrentRule sys, L.get dsSide sys, L.get dsSystem sys) of
                                                                      (Just _, Just s, Just sys') -> applyStep meth s sys'
                                                                      (_ , _ , _)                 -> Nothing
          | otherwise                                         -> Nothing
        DiffMirrored
          | (L.get dsProofType sys) == (Just RuleEquivalence) -> case (L.get dsCurrentRule sys, L.get dsSide sys, L.get dsSystem sys) of
                                                                      (Just _, Just s, Just sys') -> if ((isTrivial sys') && (checkOtherSide s sys' == Just True)) ||
                                                                                                        ((isSolved s sys') && (checkOtherSide s sys' == Nothing))
                                                                                                        then return M.empty 
                                                                                                        else Nothing
                                                                      (_ , _ , _)                 -> Nothing                                                       
          | otherwise                                         -> Nothing
        DiffAttack
          | (L.get dsProofType sys) == (Just RuleEquivalence) -> case (L.get dsCurrentRule sys, L.get dsSide sys, L.get dsSystem sys) of
                                                                      (Just _, Just s, Just sys') -> if (isSolved s sys') && (checkOtherSide s sys' == Just False)
                                                                                                        then return M.empty
                                                                                                        else Nothing
                                                                      (_ , _ , _)                 -> Nothing
          | otherwise                                         -> Nothing
        DiffRuleEquivalence
          | (L.get dsProofType sys) == Nothing                -> Just ruleEquivalence
          | otherwise                                         -> Nothing
          
  where
    protoRules       = (L.get dpcProtoRules  ctxt)
    destrRules       = (L.get dpcDestrRules  ctxt)
    constrRules      = (L.get dpcConstrRules ctxt)

    protoRulesAC :: Side -> [RuleAC]
    protoRulesAC LHS = filter (\x -> getRuleNameDiff x /= "IntrRecv") $ L.get crProtocol $ L.get pcRules (L.get dpcPCLeft  ctxt)
    protoRulesAC RHS = filter (\x -> getRuleNameDiff x /= "IntrRecv") $ L.get crProtocol $ L.get pcRules (L.get dpcPCRight ctxt)
    
    ruleEquivalenceSystem :: String -> DiffSystem
    ruleEquivalenceSystem rule = L.set dsCurrentRule (Just rule) 
      $ L.set dsConstrRules (S.fromList constrRules) 
      $ L.set dsDestrRules (S.fromList destrRules) 
      $ L.set dsProtoRules (S.fromList protoRules) 
      $ L.set dsProofType (Just RuleEquivalence) sys
      
    formula :: String -> LNFormula
    formula rulename = Qua Ex ("i", LSortNode) (Ato (Action (LIT (Var (Bound 0))) (Fact {factTag = ProtoFact Linear ("Diff" ++ rulename) 0, factTerms = []})))
    
    ruleEquivalenceCase :: M.Map CaseName DiffSystem -> RuleAC -> M.Map CaseName DiffSystem
    ruleEquivalenceCase m rule = M.insert ("Rule_" ++ (getRuleName rule) ++ "") (ruleEquivalenceSystem (getRuleNameDiff rule)) m
    
--     protoRuleEquivalenceCase :: M.Map CaseName DiffSystem -> ProtoRuleE -> M.Map CaseName DiffSystem
--     protoRuleEquivalenceCase m rule = M.insert ("Rule_" ++ (getRuleName rule) ++ "") (ruleEquivalenceSystem (getRuleNameDiff rule)) m
    
    -- Not checking construction rules is sound, as they are 'trivial' !
    -- Note that we use the protoRulesAC, as we also want to include the ISEND rule as it is labelled with an action that might show up in axioms.
    -- LHS or RHS is not important in this case als we only need the names of the rules.
    ruleEquivalence :: M.Map CaseName DiffSystem
    ruleEquivalence = foldl ruleEquivalenceCase (foldl ruleEquivalenceCase {-(foldl ruleEquivalenceCase-} M.empty {-constrRules)-} destrRules) (protoRulesAC LHS)
    
    isTrivial :: System -> Bool
    isTrivial sys' = (dgIsNotEmpty sys') && (allOpenGoalsAreSimpleFacts sys') && (allOpenFactGoalsAreIndependent sys')
    
    backwardSearchSystem :: Side -> DiffSystem -> String -> DiffSystem
    backwardSearchSystem s sys' rulename = L.set dsSide (Just s)
      $ L.set dsSystem (Just (formulaToSystem (snd . head $ filter (\x -> fst x == s) $ L.get dpcAxioms ctxt) TypedCaseDist ExistsSomeTrace True (formula rulename))) sys'

    startBackwardSearch :: String -> M.Map CaseName DiffSystem
    startBackwardSearch rulename = M.insert ("LHS") (backwardSearchSystem LHS sys rulename) $ M.insert ("RHS") (backwardSearchSystem RHS sys rulename) $ M.empty
    
    applyStep :: ProofMethod -> Side -> System -> Maybe (M.Map CaseName DiffSystem)
    applyStep m s sys' = case (execProofMethod (eitherProofContext ctxt s) m sys') of
                           Nothing    -> Nothing
                           Just cases -> Just $ M.map (\x -> L.set dsSystem (Just x) sys) cases
                           
    isSolved :: Side -> System -> Bool
    isSolved s sys' = {-filter isNotForbiddenKD-} (rankProofMethods GoalNrRanking (eitherProofContext ctxt s) sys') == [] -- checks if the system is solved
    
    -- Not necessary any more, now diff-systems do not generate ForbiddeKD-contradictions any more.
--     isNotForbiddenKD :: (ProofMethod, (M.Map CaseName System, String)) -> Bool
--     isNotForbiddenKD (Contradiction (Just ForbiddenKD), _) = False
--     isNotForbiddenKD (_                               , _) = True
    
    checkOtherSide :: Side -> System -> Maybe Bool
    checkOtherSide s sys'= case getMirrorDG ctxt s sys' of
                             Just sys'' -> {-trace ("RE: axioms: " ++ (show (axioms s sys'')) ++ " " ++ (show (doAxiomsHold (oppositeCtxt s) sys'' (axioms (opposite s) sys'') (isSolved s sys'))))-} (doAxiomsHold (oppositeCtxt s) sys'' (axioms (opposite s) sys'') (isSolved s sys'))
                             Nothing    -> Just False
            where
              oppositeCtxt s' = eitherProofContext ctxt (opposite s')
              axioms s' sys'' = filterAxioms (oppositeCtxt s') sys'' $ axioms' s' $ L.get dpcAxioms ctxt

              axioms' _ []              = []
              axioms' s' ((s'', form):xs) = if s' == s'' then form ++ (axioms' s' xs) else (axioms' s' xs)
    
    
    
    
------------------------------------------------------------------------------
-- Heuristics
------------------------------------------------------------------------------

-- | The different available functions to rank goals with respect to their
-- order of solving in a constraint system.
data GoalRanking =
    GoalNrRanking
  | UsefulGoalNrRanking
  | SmartRanking Bool
  | SmartDiffRanking
  deriving( Eq, Ord, Show )

-- | The name/explanation of a 'GoalRanking'.
goalRankingName :: GoalRanking -> String
goalRankingName ranking =
    "Goals sorted according to " ++ case ranking of
        GoalNrRanking                -> "their order of creation"
        UsefulGoalNrRanking          -> "their usefulness and order of creation"
        SmartRanking useLoopBreakers -> smart useLoopBreakers
        SmartDiffRanking             -> "the 'smart' heuristic (for diff proofs)"
   where
     smart b = "the 'smart' heuristic (loop breakers " ++
               (if b then "allowed" else "delayed") ++ ")."

-- | Use a 'GoalRanking' to sort a list of 'AnnotatedGoal's stemming from the
-- given constraint 'System'.
rankGoals :: ProofContext -> GoalRanking -> System -> [AnnotatedGoal] -> [AnnotatedGoal]
rankGoals ctxt ranking = case ranking of
    GoalNrRanking       -> \_sys -> goalNrRanking
    UsefulGoalNrRanking ->
        \_sys -> sortOn (\(_, (nr, useless)) -> (useless, nr))
    SmartRanking useLoopsBreakers -> smartRanking ctxt useLoopsBreakers
    SmartDiffRanking -> smartDiffRanking ctxt

-- | Use a 'GoalRanking' to generate the ranked, list of possible
-- 'ProofMethod's and their corresponding results in this 'ProofContext' and
-- for this 'System'. If the resulting list is empty, then the constraint
-- system is solved.
rankProofMethods :: GoalRanking -> ProofContext -> System
                 -> [(ProofMethod, (M.Map CaseName System, String))]
rankProofMethods ranking ctxt sys = do
    (m, expl) <-
            (contradiction <$> contradictions ctxt sys)
        <|> (case L.get pcUseInduction ctxt of
               AvoidInduction -> [(Simplify, ""), (Induction, "")]
               UseInduction   -> [(Induction, ""), (Simplify, "")]
            )
        <|> (solveGoalMethod <$> (rankGoals ctxt ranking sys $ openGoals sys))
    case execProofMethod ctxt m sys of
      Just cases -> return (m, (cases, expl))
      Nothing    -> []
  where
    contradiction c                    = (Contradiction (Just c), "")
    solveGoalMethod (goal, (nr, usefulness)) =
      ( SolveGoal goal
      , "nr. " ++ show nr ++ case usefulness of
                               Useful                -> ""
                               LoopBreaker           -> " (loop breaker)"
                               ProbablyConstructible -> " (probably constructible)"
                               CurrentlyDeducible    -> " (currently deducible)"
      )

-- | Use a 'GoalRanking' to generate the ranked, list of possible
-- 'ProofMethod's and their corresponding results in this 'ProofContext' and
-- for this 'System'. If the resulting list is empty, then the constraint
-- system is solved.
rankDiffProofMethods :: GoalRanking -> DiffProofContext -> DiffSystem
                 -> [(DiffProofMethod, (M.Map CaseName DiffSystem, String))]
rankDiffProofMethods ranking ctxt sys = do
    (m, expl) <-
            [(DiffRuleEquivalence, "Prove equivalence using rule equivalence")]
        <|> [(DiffMirrored, "Backward search completed")]
        <|> [(DiffAttack, "Found attack")]
        <|> [(DiffBackwardSearch, "Do backward search from rule")]
        <|> (case (L.get dsSide sys, L.get dsSystem sys) of
                  (Just s, Just sys') -> map (\x -> (DiffBackwardSearchStep (fst x), "Do backward search step")) (rankProofMethods ranking (eitherProofContext ctxt s) sys')
                  (_         , _        ) -> [])
    case execDiffProofMethod ctxt m sys of
      Just cases -> return (m, (cases, expl))
      Nothing    -> []

newtype Heuristic = Heuristic [GoalRanking]
    deriving( Eq, Ord, Show )

-- | Smart constructor for heuristics. Schedules the goal rankings in a
-- round-robin fashion dependent on the proof depth.
roundRobinHeuristic :: [GoalRanking] -> Heuristic
roundRobinHeuristic = Heuristic

-- | Use a heuristic to schedule a 'GoalRanking' according to the given
-- proof-depth.
useHeuristic :: Heuristic -> Int -> GoalRanking
useHeuristic (Heuristic []      ) = error "useHeuristic: empty list of rankings"
useHeuristic (Heuristic rankings) =
    ranking
  where
    n = length rankings

    ranking depth
      | depth < 0 = error $ "useHeuristic: negative proof depth " ++ show depth
      | otherwise = rankings !! (depth `mod` n)



{-
-- | Schedule the given local-heuristics in a round-robin fashion.
roundRobinHeuristic :: [GoalRanking] -> Heuristic
roundRobinHeuristic []       = error "roundRobin: empty list of rankings"
roundRobinHeuristic rankings =
    methods
  where
    n = length rankings

    methods depth ctxt sys
      | depth < 0 = error $ "roundRobin: negative proof depth " ++ show depth
      | otherwise =
          ( name
          ,     ((Contradiction . Just) <$> contradictions ctxt sys)
            <|> (case L.get pcUseInduction ctxt of
                   AvoidInduction -> [Simplify, Induction]
                   UseInduction   -> [Induction, Simplify]
                )
            <|> ((SolveGoal . fst) <$> (ranking sys $ openGoals sys))
          )
      where
        (name, ranking) = rankings !! (depth `mod` n)
-}

-- | Sort annotated goals according to their number.
goalNrRanking :: [AnnotatedGoal] -> [AnnotatedGoal]
goalNrRanking = sortOn (fst . snd)

-- | A ranking function tuned for the automatic verification of
-- classical security protocols that exhibit a well-founded protocol premise
-- fact flow.
smartRanking :: ProofContext
             -> Bool   -- True if PremiseG loop-breakers should not be delayed
             -> System
             -> [AnnotatedGoal] -> [AnnotatedGoal]
smartRanking ctxt allowPremiseGLoopBreakers sys =
    sortOnUsefulness . unmark . sortDecisionTree solveLast . sortDecisionTree solveFirst . goalNrRanking
  where
    oneCaseOnly = catMaybes . map getMsgOneCase . L.get pcCaseDists $ ctxt

    getMsgOneCase cd = case msgPremise (L.get cdGoal cd) of
      Just (viewTerm -> FApp o _)
        | length (getDisj (L.get cdCases cd)) == 1 -> Just o
      _                                            -> Nothing

    sortOnUsefulness = sortOn (tagUsefulness . snd . snd)

    tagUsefulness Useful                = 0 :: Int
    tagUsefulness ProbablyConstructible = 1
    tagUsefulness LoopBreaker           = 1
    tagUsefulness CurrentlyDeducible    = 2

    unmark | allowPremiseGLoopBreakers = map unmarkPremiseG
           | otherwise                 = id

    unmarkPremiseG (goal@(PremiseG _ _), (nr, _)) = (goal, (nr, Useful))
    unmarkPremiseG annGoal                        = annGoal

    solveLast = 
       [ isNonLastProtoFact . fst ]
       -- move the Last proto facts (L_) to the end.

    solveFirst =
        [ isChainGoal . fst
        , isDisjGoal . fst
        , isFirstProtoFact . fst
        , isNonLoopBreakerProtoFactGoal
        , isStandardActionGoal . fst
        , isPrivateKnowsGoal . fst
        , isFreshKnowsGoal . fst
        , isSplitGoalSmall . fst
        , isMsgOneCaseGoal . fst
        , isDoubleExpGoal . fst
        , isNoLargeSplitGoal . fst ]
        -- move the rest (mostly more expensive KU-goals) before expensive
        -- equation splits

    -- FIXME: This small split goal preferral is quite hacky when using
    -- induction. The problem is that we may end up solving message premise
    -- goals all the time instead of performing a necessary split. We should make
    -- sure that a split does not get too old.
    smallSplitGoalSize = 3

    isNonLoopBreakerProtoFactGoal (PremiseG _ fa, (_, Useful)) = not $ isKFact fa
    isNonLoopBreakerProtoFactGoal _                            = False

    msgPremise (ActionG _ fa) = do (UpK, m) <- kFactView fa; return m
    msgPremise _              = Nothing

    -- Detect 'F_' (first) fact prefix for heuristics
    isFirstProtoFact (PremiseG _ (Fact (ProtoFact _ ('F':'_':_) _) _)) = True
    isFirstProtoFact _                                                 = False

    -- Detect 'L_' (last) fact prefix for heuristics
    isNonLastProtoFact (PremiseG _ (Fact (ProtoFact _ ('L':'_':_) _) _)) = False
    isNonLastProtoFact _                                                 = True

    isFreshKnowsGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | lvarSort lv == LSortFresh -> True
        _                                                           -> False

    isMsgOneCaseGoal goal = case msgPremise goal of
        Just (viewTerm -> FApp o _) | o `elem` oneCaseOnly -> True
        _                                                  -> False

    isPrivateKnowsGoal goal = case msgPremise goal of
        Just t -> isPrivateFunction t
        _      -> False

    isDoubleExpGoal goal = case msgPremise goal of
        Just (viewTerm2 -> FExp  _ (viewTerm2 -> FMult _)) -> True
        _                                                  -> False

    -- Be conservative on splits that don't exist.
    isSplitGoalSmall (SplitG sid) =
        maybe False (<= smallSplitGoalSize) $ splitSize (L.get sEqStore sys) sid
    isSplitGoalSmall _            = False

    isNoLargeSplitGoal goal@(SplitG _) = isSplitGoalSmall goal
    isNoLargeSplitGoal _               = True

    -- | @sortDecisionTree xs ps@ returns a reordering of @xs@
    -- such that the sublist satisfying @ps!!0@ occurs first,
    -- then the sublist satisfying @ps!!1@, and so on.
    sortDecisionTree :: [a -> Bool] -> [a] -> [a]
    sortDecisionTree []     xs = xs
    sortDecisionTree (p:ps) xs = sat ++ sortDecisionTree ps nonsat
      where (sat, nonsat) = partition p xs


-- | A ranking function tuned for the automatic verification of
-- classical security protocols that exhibit a well-founded protocol premise
-- fact flow.
-- Adjusted for diff systems by delaying splitEqs and ensuring trivial goals are solved last.
smartDiffRanking :: ProofContext
                    -> System
                    -> [AnnotatedGoal] -> [AnnotatedGoal]
smartDiffRanking ctxt sys =
    delayTrivial . delaySplits . smartRanking ctxt False sys
  where
    delaySplits agl = fst parts ++ snd parts
      where
        parts = partition (not . isSplitGoal') agl
        isSplitGoal' ((SplitG _), _) = True
        isSplitGoal' _               = False


    delayTrivial agl = fst parts ++ snd parts
      where
        parts = partition (not . trivialKUGoal) agl
    
    trivialKUGoal ((ActionG _ fa), _) = isKUFact fa && (isTrivialMsgFact fa /= Nothing)
    trivialKUGoal _                   = False

    -- | If all the fact terms are simple and different msg variables (i.e., not fresh or public), returns the list of all these variables. Otherwise returns Nothing. Currently identical to "isTrivialFact" from Model/Fact, but could eventually be relaxed there, but not here. 
    isTrivialMsgFact :: LNFact -> Maybe [LVar]
    isTrivialMsgFact (Fact _ ts) = case ts of
      []   -> Just []
      x:xs -> Prelude.foldl combine (getMsgVar x) (map getMsgVar xs)
      where
        combine :: Maybe [LVar] -> Maybe [LVar] -> Maybe [LVar]
        combine Nothing    _        = Nothing
        combine (Just _ )  Nothing  = Nothing
        combine (Just l1) (Just l2) = if noDuplicates l1 l2 then (Just (l1++l2)) else Nothing
      
        noDuplicates l1 l2 = S.null (S.intersection (S.fromList l1) (S.fromList l2))


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty-print a proof method.
prettyProofMethod :: HighlightDocument d => ProofMethod -> d
prettyProofMethod method = case method of
    Solved               -> keyword_ "SOLVED" <-> lineComment_ "trace found"
    Induction            -> keyword_ "induction"
    Sorry reason         ->
        fsep [keyword_ "sorry", maybe emptyDoc closedComment_ reason]
    SolveGoal goal       ->
        keyword_ "solve(" <-> prettyGoal goal <-> keyword_ ")"
    Simplify             -> keyword_ "simplify"
    Contradiction reason ->
        sep [ keyword_ "contradiction"
            , maybe emptyDoc (closedComment . prettyContradiction) reason
            ]

-- | Pretty-print a diff proof method.
prettyDiffProofMethod :: HighlightDocument d => DiffProofMethod -> d
prettyDiffProofMethod method = case method of
    DiffMirrored             -> keyword_ "MIRRORED"
    DiffAttack               -> keyword_ "ATTACK" <-> lineComment_ "trace found"
    DiffSorry reason         ->
        fsep [keyword_ "sorry", maybe emptyDoc lineComment_ reason]
-- MERGED with solved.
--    DiffTrivial              -> keyword_ "trivial"
    DiffRuleEquivalence      -> keyword_ "rule-equivalence"
    DiffBackwardSearch       -> keyword_ "backward-search"  
    DiffBackwardSearchStep s -> keyword_ "step(" <-> prettyProofMethod s <-> keyword_ ")"
    
    
-- Derived instances
--------------------

$( derive makeBinary ''ProofMethod)
$( derive makeBinary ''DiffProofMethod)
$( derive makeBinary ''GoalRanking)
$( derive makeBinary ''Heuristic)

$( derive makeNFData ''ProofMethod)
$( derive makeNFData ''DiffProofMethod)
$( derive makeNFData ''GoalRanking)
$( derive makeNFData ''Heuristic)
