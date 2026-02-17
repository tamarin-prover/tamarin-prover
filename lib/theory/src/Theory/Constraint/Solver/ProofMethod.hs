{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE DeriveAnyClass  #-}
--{-# LANGUAGE QuasiQuotes     #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier & Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Proof methods for the heuristics: the external small-step interface to the
-- constraint solver.
module Theory.Constraint.Solver.ProofMethod (
  -- * Proof methods
    CaseName
  , ProofMethod(..)
  , Result(..)
  , DiffProofMethod(..)
  , checkAndExecProofMethod
  , execProofMethod
  , execDiffProofMethod
  , isFinished

  -- ** Heuristics
  , rankProofMethods
  , rankDiffProofMethods

  , roundRobinHeuristic
  , useHeuristic
  , finishedSubterms

  -- ** Pretty Printing
  , prettyProofMethod
  , prettyDiffProofMethod

) where
  
import           GHC.Generics                              (Generic)
import           Data.Binary
import           Data.Function                             (on)
import           Data.Label                                hiding (get)
import qualified Data.Label                                as L
import           Data.List                                 (partition,groupBy,sortBy,isPrefixOf,findIndex,intercalate, uncons)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map                                  as M
import           Data.Maybe                                (catMaybes, fromMaybe, mapMaybe, isNothing, isJust)
-- import           Data.Monoid
import           Data.Ord                                  (comparing)
import qualified Data.Set                                  as S
import           Extension.Prelude                         (sortOn)
import qualified Data.ByteString.Char8 as BC

import           Control.Basics
import           Control.DeepSeq
import qualified Control.Monad.Trans.PreciseFresh          as Precise
import qualified Control.Monad.Trans.State                 as St

import           Debug.Trace
import           Safe
import           System.IO.Unsafe
import           System.Process

import           Theory.Constraint.Solver.Sources
import           Theory.Constraint.Solver.Contradictions
import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.AnnotatedGoals
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.Solver.Simplify
--import           Theory.Constraint.Solver.Heuristics
import           Theory.Constraint.System
import           Theory.Model
import           Theory.Text.Pretty
import qualified Extension.Data.Label as L
import Control.Monad.Disj (disjunctionOfList)
import Data.Bool (bool)



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
    $ concatMap uniquify $ groupBy (\x y -> ord (fst x) (fst y) == EQ)
    $ sortBy (ord `on` fst)
    $ zip xs0 [(0::Int)..]
  where
    uniquify []      = error "impossible"
    uniquify [(x,i)] = [(single x, i)]
    uniquify xs      = zipWith (\f (x,i) -> (f x, i)) dist xs
      where
        dist = distinguish $ length xs

isNonLoopBreakerProtoFactGoal :: (Goal, (a, Usefulness)) -> Bool
isNonLoopBreakerProtoFactGoal (PremiseG _ fa, (_, Useful)) =
   not (isKFact fa) && not (isAuthOutFact fa)
isNonLoopBreakerProtoFactGoal _                            = False


isLastProtoFact :: Goal -> Bool
isLastProtoFact (PremiseG _ fa) = isSolveLastFact fa
isLastProtoFact _               = False

isFirstProtoFact :: Goal -> Bool
isFirstProtoFact (PremiseG _ fa) = isSolveFirstFact fa
isFirstProtoFact _               = False

isNotAuthOut :: Goal -> Bool
isNotAuthOut (PremiseG _ fa) = not (isAuthOutFact fa)
isNotAuthOut _               = False

msgPremise :: Goal -> Maybe LNTerm
msgPremise (ActionG _ fa) = do (UpK, m) <- kFactView fa; return m
msgPremise _              = Nothing

isProgressFact :: Fact t -> Bool
isProgressFact (factTag -> ProtoFact Linear name 1) = isPrefixOf "ProgressTo_" name
isProgressFact _ = False

isProgressDisj :: Goal -> Bool
isProgressDisj (DisjG (Disj disj )) = all (\f ->  (case f of 
        GGuarded Ex [(_,LSortNode)] [Action _ f' ] _ -> isProgressFact f'
        _                                            -> False
        )) disj
isProgressDisj _ = False

isDisjGoalButNotProgress :: Goal -> Bool
isDisjGoalButNotProgress g = isDisjGoal g && not (isProgressDisj g)

isLastName :: LVar -> Bool
isLastName lv = "L_" `isPrefixOf` (lvarName lv)

isFirstName :: LVar -> Bool
isFirstName lv = "F_" `isPrefixOf` (lvarName lv)

isKnowsLastNameGoal :: Goal -> Bool
isKnowsLastNameGoal goal = case msgPremise goal of
    Just (viewTerm -> Lit (Var lv)) | ((lvarSort lv  == LSortFresh) && isLastName lv)-> True
    _                                                           -> False

isKnowsFirstNameGoal :: Goal -> Bool
isKnowsFirstNameGoal goal = case msgPremise goal of
    Just (viewTerm -> Lit (Var lv)) | ((lvarSort lv  == LSortFresh) && isFirstName lv)-> True
    _                                                           -> False

isPrivateKnowsGoal :: Goal -> Bool
isPrivateKnowsGoal goal = case msgPremise goal of
    Just t -> isPrivateFunction t
    _      -> False

isDoubleExpGoal :: Goal -> Bool
isDoubleExpGoal goal = case msgPremise goal of
    Just (viewTerm2 -> FExp  _ (viewTerm2 -> FMult _)) -> True
    _                                                  -> False

-- | @sortDecisionTree xs ps@ returns a reordering of @xs@
-- such that the sublist satisfying @ps!!0@ occurs first,
-- then the sublist satisfying @ps!!1@, and so on.
sortDecisionTree :: [a -> Bool] -> [a] -> [a]
sortDecisionTree []     xs = xs
sortDecisionTree (p:ps) xs = sat ++ sortDecisionTree ps nonsat
  where (sat, nonsat) = partition p xs

-- | Same as sortDecisionTree, but adding the satisfied goals at the end of the list
sortDecisionTreeLast :: [a -> Bool] -> [a] -> [a]
sortDecisionTreeLast []     xs = xs
sortDecisionTreeLast (p:ps) xs = sortDecisionTreeLast ps nonsat ++ sat
  where (sat, nonsat) = partition p xs

unmarkPremiseG :: (Goal, (a, Usefulness))
    -> (Goal, (a, Usefulness))
unmarkPremiseG (goal@(PremiseG _ _), (nr, _)) = (goal, (nr, Useful))
unmarkPremiseG annGoal                        = annGoal


------------------------------------------------------------------------------
-- Proof Methods
------------------------------------------------------------------------------

-- | Every case in a proof is uniquely named.
type CaseName = String

data Result =
    Solved
  -- ^ A dependency graph was found.
  | Contradictory (Maybe Contradiction)
  -- ^ A contradiction could be derived, possibly with a reason. The single
  --    formula constraint in the system.
  | Unfinishable
  -- ^ The proof cannot be finished (due to reducible operators in subterms or
  --   because a solution was found after weakening).
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | Sound transformations of sequents.
data ProofMethod =
    Sorry (Maybe String)                 -- ^ Proof was not completed
  | Simplify                             -- ^ A simplification step.
  | SolveGoal Goal                       -- ^ A goal that was solved.
  | Induction                            -- ^ Use inductive strengthening on
                                         -- the single formula constraint in
                                         -- the system.
  | Finished Result
  | Invalidated                          -- ^ mark as invalidated as a result of editing other lemmas
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | Sound transformations of diff sequents.
data DiffProofMethod =
    DiffSorry (Maybe String)                 -- ^ Proof was not completed
  | DiffMirrored                             -- ^ No attack was found
  | DiffAttack                               -- ^ A potential attack was found
  | DiffUnfinishable                         -- ^ The backward search is complete (but there are reducible operators in subterms)
  | DiffRuleEquivalence                      -- ^ Consider all rules
  | DiffBackwardSearch                       -- ^ Do the backward search starting from a rule
  | DiffBackwardSearchStep ProofMethod       -- ^ A step in the backward search starting from a rule
  deriving( Eq, Ord, Show, Generic, NFData, Binary )

  
instance HasFrees ProofMethod where
    foldFrees f (SolveGoal g)     = foldFrees f g
    foldFrees f (Finished (Contradictory c)) = foldFrees f c
    foldFrees _ _                 = mempty

    foldFreesOcc  _ _ = const mempty

    mapFrees f (SolveGoal g)     = SolveGoal <$> mapFrees f g
    mapFrees f (Finished (Contradictory c)) = Finished . Contradictory <$> mapFrees f c
    mapFrees _ method            = pure method

instance HasFrees DiffProofMethod where
    foldFrees f (DiffBackwardSearchStep c) = foldFrees f c
    foldFrees _ _                          = mempty

    foldFreesOcc  _ _ = const mempty

    mapFrees f (DiffBackwardSearchStep c) = DiffBackwardSearchStep <$> mapFrees f c
    mapFrees _ method                     = pure method

-- Proof method execution
-------------------------

-- @checkAndExecMethod rules method se@ checks first if the @method@ is
-- applicable to the sequent @se@ and, if so, applies it.
checkAndExecProofMethod :: ProofContext -> ProofMethod -> System -> Maybe (M.Map CaseName System)
checkAndExecProofMethod ctxt method sys = do
    case method of
      Finished r -> isFinished ctxt sys >>= guard . equalReason r
      Induction -> canApplyInduction
      SolveGoal goal -> guard (goal `M.member` L.get sGoals sys)
      Simplify -> Just ()
      Sorry _ -> Just ()
    execProofMethod ctxt method sys
  where
    canApplyInduction :: Maybe ()
    canApplyInduction = do
      guard (M.null $ L.get sNodes sys)
      guard (S.null $ L.get sSolvedFormulas sys)
      guard (M.null $ L.get sGoals sys)
      (_, t) <- uncons $ S.toList $ L.get sFormulas sys
      guard (null t)

    equalReason :: Result -> Result -> Bool
    equalReason (Contradictory _) (Contradictory _) = True
    equalReason r1 r2 = r1 == r2
    -- ^ all other reasons don't have an argument

-- @execMethod rules method se@ applies the @method@ to the sequent under the
-- assumption that it is sound to apply the method and that the @rules@ describe
-- all rewriting rules in scope.
--
-- NOTE that the returned systems have their free substitution fully applied
-- and all variable indices reset.
execProofMethod :: ProofContext
                -> ProofMethod -> System -> Maybe (M.Map CaseName System)
execProofMethod ctxt method sys =
    case method of
      Sorry _               -> return M.empty
      Finished _            -> return M.empty
      Simplify              ->
        let cases = process (return "") -- @process@ simplifies
        in case M.toList cases of
          -- Check whether simplified system is equal to previous one; if so,
          -- fail in applying this method.
          [(_, sys')] -> guard (sys' /= cleanup sys) >> return cases
          -- If simplifying resulted in multiple cases, the resulting ones
          -- cannot be equal to the original one so there's nothing to check.
          _ -> return cases
      Induction             -> process . induction <$> getInductionCases sys
      SolveGoal goal        -> return $ process $ solve goal
      Invalidated           -> Nothing
  where
    process :: Reduction CaseName -> M.Map CaseName System
    process m =
      let cases =   removeRedundantCases ctxt [] snd
                  . map (fmap cleanup . fst)
                  . getDisj $ runReduction (m <* simplifySystem) ctxt sys (avoid sys)
      in  M.fromListWith (error "case names not unique")
            $ uniqueListBy (comparing fst) id distinguish cases

    cleanup :: System -> System
    cleanup s = L.set sSubst emptySubst (Precise.evalFresh (renamePrecise s) Precise.nothingUsed)

    -- solve the given goal
    -- PRE: Goal must be valid in this system.
    solve :: Goal -> Reduction CaseName
    solve goal =
      let ths = L.get pcSources ctxt
      in maybe  (solveGoal goal)
                (intercalate "_" <$>)
                (solveWithSource ctxt ths goal)

    -- Induction is only possible if the system contains only
    -- a single, last-free, closed formula.
    getInductionCases :: System -> Maybe (LNGuarded, LNGuarded)
    getInductionCases s = do
      (h, _) <- uncons $ S.toList $ L.get sFormulas s
      either (const Nothing) Just (ginduct h)

    induction :: (LNGuarded, LNGuarded) -> Reduction String
    induction (baseCase, stepCase) = do
      (caseName, caseFormula) <- disjunctionOfList [("empty_trace", baseCase), ("non_empty_trace", stepCase)]
      L.setM sFormulas (S.singleton caseFormula)
      return caseName

    distinguish n =
        [ (\(x,y) -> (if null x then show i else x ++ "_case_" ++ pad (show i), y))
        | i <- [(1::Int)..] ]
      where
        l      = length (show n)
        pad cs = replicate (l - length cs) '0' ++ cs

-- @execDiffMethod rules method se@ checks first if the @method@ is applicable to
-- the sequent @se@. Then, it applies the @method@ to the sequent under the
-- assumption that the @rules@ describe all rewriting rules in scope.
--
-- NOTE that the returned systems have their free substitution fully applied
-- and all variable indices reset.
execDiffProofMethod :: DiffProofContext
                -> DiffProofMethod -> DiffSystem -> Maybe (M.Map CaseName DiffSystem)
execDiffProofMethod ctxt method sys =
  case method of
    DiffSorry _ -> return M.empty
    DiffBackwardSearch -> do
      guard (L.get dsProofType sys == Just RuleEquivalence)
      rule <- L.get dsCurrentRule sys
      guard (isNothing $ L.get dsSide sys)
      return $ startBackwardSearch rule
    DiffBackwardSearchStep meth -> do
      guard (L.get dsProofType sys == Just RuleEquivalence)
      guard (meth /= Induction)
      guard (meth /= Finished (Contradictory (Just ForbiddenKD)))
      _ <- L.get dsCurrentRule sys
      s <- L.get dsSide sys
      applyStep meth s =<< sequent
    DiffMirrored -> do
      guard (L.get dsProofType sys == Just RuleEquivalence)
      guard (isJust $ L.get dsCurrentRule sys)
      msys' >>= guard . trivial
      mallSubtermsFinished >>= guard
      mirrorSyss <- mmirrorSyss
      solved <- isSolved <$> mside <*> msys'
      guard (fst (evaluateRestrictions ctxt sys mirrorSyss solved) == TTrue)
      return M.empty
    DiffAttack -> do
      guard (L.get dsProofType sys == Just RuleEquivalence)
      guard (isJust $ L.get dsCurrentRule sys)
      s <- L.get dsSide sys
      solved <- isSolved <$> mside <*> msys'
      sys' <- L.get dsSystem sys
      notContradictory <- not . contradictorySystem (eitherProofContext ctxt s) <$> sequent
      -- In the second case, the system is trivial, has no mirror and restrictions do not get in the way.
      -- If we solve arbitrarily the last remaining trivial goals,
      -- then there will be an attack.
      guard (solved || (trivial sys' && notContradictory))
      allSubtermsFinished <- mallSubtermsFinished
      guard allSubtermsFinished
      mirrorSyss <- mmirrorSyss
      guard (fst (evaluateRestrictions ctxt sys mirrorSyss solved) == TFalse)
      return M.empty
    DiffRuleEquivalence -> do
      guard (isNothing $ L.get dsProofType sys)
      return ruleEquivalence
    DiffUnfinishable -> do
      guard (L.get dsProofType sys == Just RuleEquivalence)
      guard (isJust $ L.get dsCurrentRule sys)
      solved <- isSolved <$> mside <*> msys'
      allSubtermsFinished <- mallSubtermsFinished
      guard solved
      guard (not allSubtermsFinished)
      return M.empty
  where
    sequent              = L.get dsSystem sys
    mside                = L.get dsSide sys
    msys'                = L.get dsSystem sys
    mmirrorSyss          = getMirrorDG ctxt <$> mside <*> msys'
    mctxt                = eitherProofContext ctxt <$> mside
    mmirrorCtxt          = eitherProofContext ctxt . opposite <$> mside
    mallSubtermsFinished = do
      finished <- finishedSubterms <$> mctxt <*> msys'
      finishedMirrored <- (all . finishedSubterms <$> mmirrorCtxt) <*> mmirrorSyss
      return $ finished && finishedMirrored

    protoRules       = L.get dpcProtoRules  ctxt
    destrRules       = L.get dpcDestrRules  ctxt
    constrRules      = L.get dpcConstrRules ctxt

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
    formula rulename = Qua Ex ("i", LSortNode) (Ato (Action (LIT (Var (Bound 0))) (Fact (ProtoFact Linear ("Diff" ++ rulename) 0) S.empty [])))

    ruleEquivalenceCase :: M.Map CaseName DiffSystem -> RuleAC -> M.Map CaseName DiffSystem
    ruleEquivalenceCase m rule = M.insert ("Rule_" ++ (getRuleName rule) ++ "") (ruleEquivalenceSystem (getRuleNameDiff rule)) m

    -- Not checking construction rules is sound, as they are 'trivial' !
    -- Note that we use the protoRulesAC, as we also want to include the ISEND rule as it is labelled with an action that might show up in restrictions.
    -- LHS or RHS is not important in this case as we only need the names of the rules.
    ruleEquivalence :: M.Map CaseName DiffSystem
    ruleEquivalence = foldl ruleEquivalenceCase (foldl ruleEquivalenceCase {-(foldl ruleEquivalenceCase-} M.empty {-constrRules)-} destrRules) (protoRulesAC LHS)

    trivial :: System -> Bool
    trivial sys' = (dgIsNotEmpty sys') && (allOpenGoalsAreSimpleFacts ctxt sys') && (allOpenFactGoalsAreIndependent sys')

    backwardSearchSystem :: Side -> DiffSystem -> String -> DiffSystem
    backwardSearchSystem s sys' rulename = L.set dsSide (Just s)
      $ L.set dsSystem (Just ruleSys) sys'
        where
          ruleSys = insertLemmas reuseLemmas $ formulaToSystem (snd . head $ filter (\x -> fst x == s) $ L.get dpcRestrictions ctxt) RefinedSource ExistsSomeTrace True (formula rulename)
          reuseLemmas = map snd $ filter (\x -> fst x == s) $ L.get dpcReuseLemmas ctxt

    startBackwardSearch :: String -> M.Map CaseName DiffSystem
    startBackwardSearch rulename = M.insert ("LHS") (backwardSearchSystem LHS sys rulename) $ M.insert ("RHS") (backwardSearchSystem RHS sys rulename) $ M.empty

    isSolved :: Side -> System -> Bool
    isSolved s sys' = isJust $ isFinished (eitherProofContext ctxt s) sys' >>= guard . (== Solved)

    applyStep :: ProofMethod -> Side -> System -> Maybe (M.Map CaseName DiffSystem)
    applyStep m s dsSys = do
      cases <- checkAndExecProofMethod (eitherProofContext ctxt s) m dsSys
      return $ M.map (\x -> L.set dsSystem (Just x) sys) cases

-- | returns True if there are no reducible operators on top of a right side of a subterm in the subterm store
finishedSubterms :: ProofContext -> System -> Bool
finishedSubterms pc sys = hasReducibleOperatorsOnTop (reducibleFunSyms $ mhMaudeSig $ L.get pcMaudeHandle pc) (L.get sSubtermStore sys)

------------------------------------------------------------------------------
-- Heuristics
------------------------------------------------------------------------------

data ProofInstruction = ApplySorry

data Ranking a = Ranking
  { ranked :: a
  , instruction :: Maybe ProofInstruction }

plainRanking :: a -> Ranking a
plainRanking = (`Ranking` Nothing)

-- | Use a 'GoalRanking' to sort a list of 'AnnotatedGoal's stemming from the
-- given constraint 'System'.
rankGoals :: ProofContext -> GoalRanking ProofContext -> [Tactic ProofContext] -> System -> [AnnotatedGoal] -> Ranking [AnnotatedGoal]
rankGoals ctxt ranking tacticsList sys = case ranking of
    GoalNrRanking       -> plainRanking . goalNrRanking
    OracleRanking quitOnEmpty oracleName -> oracleRanking (const goalNrRanking) oracleName quitOnEmpty ctxt sys
    OracleSmartRanking quitOnEmpty oracleName -> oracleRanking (smartRanking ctxt False) oracleName quitOnEmpty ctxt sys
    UsefulGoalNrRanking -> plainRanking. sortOn (\(_, (nr, useless)) -> (useless, nr))
    SapicRanking -> plainRanking . sapicRanking ctxt sys
    SapicPKCS11Ranking -> plainRanking . sapicPKCS11Ranking ctxt sys
    SmartRanking useLoopBreakers -> plainRanking . smartRanking ctxt useLoopBreakers sys
    SmartDiffRanking -> plainRanking . smartDiffRanking ctxt sys
    InjRanking useLoopBreakers -> plainRanking . injRanking ctxt useLoopBreakers sys
    InternalTacticRanking quitOnEmpty tactic -> internalTacticRanking (chosenTactic tacticsList tactic) quitOnEmpty ctxt sys

    where 
      chosenTactic :: [Tactic ProofContext] -> Tactic ProofContext-> Tactic ProofContext
      chosenTactic   []  t = chooseError tacticsList t
      chosenTactic (h:q) t = if checkName h t then h else chosenTactic q t

      definedHeuristic = intercalate [','] (foldl (\acc x -> (_name x):acc ) [] tacticsList)

      checkName t1 t2 = (_name t1) == (_name t2)

      chooseError [] _ = error $ "No tactic has been written in the theory file"
      chooseError _  t = error $ "The tactic specified ( "++(show $ _name t)++" ) is not written in the theory file, please chose among the following: "++(show definedHeuristic)

isFinished :: ProofContext -> System -> Maybe Result
isFinished ctxt sys
  | isInitialSystem sys = Nothing
  | not $ null cs = Just $ Contradictory (Just $ head cs)
  | null ogs && stFinished = Just Solved
  | null ogs && not stFinished = Just Unfinishable
  | otherwise = Nothing
  where
    cs = contradictions ctxt sys
    ogs = openGoals sys
    stFinished = finishedSubterms ctxt sys

-- | Use a 'GoalRanking' to generate the ranked, list of possible
-- 'ProofMethod's and their corresponding results in this 'ProofContext' and
-- for this 'System'.
rankProofMethods :: GoalRanking ProofContext -> [Tactic ProofContext] -> ProofContext -> System
                 -> [(ProofMethod, (M.Map CaseName System, String))]
rankProofMethods ranking tactics ctxt sys =
  let Ranking (map solveGoalMethod -> goals) instr = rankGoals ctxt ranking tactics sys (openGoals sys)
      insertInduction (simplify NE.:| gs) = case L.get pcUseInduction ctxt of
        AvoidInduction -> simplify : (Induction, "") : gs
        UseInduction   -> (Induction, "") : simplify : gs
      proofMethods = bool NE.toList insertInduction (isInitialSystem sys) ((Simplify, "") NE.:| goals)
      stoppingMethod =    (Finished <$> isFinished ctxt sys)
                      <|> (Sorry (Just "Oracle ranked no proof methods") <$ instr)
  in execMethods $ maybe proofMethods ((:[]) . (,"")) stoppingMethod
  where
    execMethods = mapMaybe execMethod
    execMethod (m, expl) = do
      cases <- execProofMethod ctxt m sys
      return (m, (cases, expl))

    sourceRule goal = case goalRule sys goal of
        Just ru -> " (from rule " ++ getRuleName ru ++ ")"
        Nothing -> ""

    solveGoalMethod (goal, (nr, usefulness)) =
      ( SolveGoal goal
      , "nr. " ++ show nr ++ sourceRule goal ++ case usefulness of
                               Useful                -> ""
                               LoopBreaker           -> " (loop breaker)"
                               ProbablyConstructible -> " (probably constructible)"
                               CurrentlyDeducible    -> " (currently deducible)"
      )

-- | Use a 'GoalRanking' to generate the ranked, list of possible
-- 'ProofMethod's and their corresponding results in this 'DiffProofContext' and
-- for this 'DiffSystem'. If the resulting list is empty, then the constraint
-- system is solved.
rankDiffProofMethods :: GoalRanking ProofContext -> [Tactic ProofContext] -> DiffProofContext -> DiffSystem
                 -> [(DiffProofMethod, (M.Map CaseName DiffSystem, String))]
rankDiffProofMethods ranking tactics ctxt sys = do
    (m, expl) <-
            [ (DiffRuleEquivalence, "Prove equivalence using rule equivalence")
            , (DiffMirrored, "Backward search completed")
            , (DiffAttack, "Found attack")
            , (DiffUnfinishable, "Proof cannot be finished")
            , (DiffBackwardSearch, "Do backward search from rule")]
        ++  maybe []
              (map (\x -> (DiffBackwardSearchStep (fst x), "Do backward search step")) . filter (isDiffApplicable . fst))
              ((rankProofMethods ranking tactics . eitherProofContext ctxt <$> L.get dsSide sys) <*> sys')
    maybe [] (return . (m,) . (,expl)) (execDiffProofMethod ctxt m sys)
  where
    sys' = L.get dsSystem sys
    isDiffApplicable (Finished (Contradictory _)) = True
    isDiffApplicable Simplify = True
    isDiffApplicable (SolveGoal _) = True
    isDiffApplicable _ = False

-- | Smart constructor for heuristics. Schedules the proof method rankings in a
-- round-robin fashion dependent on the proof depth.
roundRobinHeuristic :: [GoalRanking ProofContext] -> Heuristic ProofContext
roundRobinHeuristic = Heuristic

-- | Use a heuristic to schedule a 'GoalRanking' according to the given
-- proof-depth.
useHeuristic :: Heuristic ProofContext -> Int -> GoalRanking ProofContext
useHeuristic (Heuristic []      ) = error "useHeuristic: empty list of rankings"
useHeuristic (Heuristic rankings) =
    ranking
  where
    n = length rankings

    ranking depth
      | depth < 0 = error $ "useHeuristic: negative proof depth " ++ show depth
      | otherwise = rankings !! (depth `mod` n)

-- | Sort annotated goals according to their number.
goalNrRanking :: [AnnotatedGoal] -> [AnnotatedGoal]
goalNrRanking = sortOn (fst . snd)

-- | A ranking function using an external oracle to allow user-definable
--   heuristics for each lemma separately.
oracleRanking :: (System -> [AnnotatedGoal] -> [AnnotatedGoal])
              -> Oracle
              -> Bool
              -> ProofContext
              -> System
              -> [AnnotatedGoal]
              -> Ranking [AnnotatedGoal]
oracleRanking preSort oracle quitOnEmpty ctxt _sys ags0 = unsafePerformIO $ do
  let ags = preSort _sys ags0
  let inp = unlines $ zipWith (\i ag -> show i ++": "++ (concat . lines . render $ pgoal ag)) [(0::Int)..] ags
  outp <- readProcess (oraclePath oracle) [ L.get pcLemmaName ctxt ] inp

  let indices = mapMaybe readMay $ lines outp
      ranked = mapMaybe (atMay ags) indices
      remaining = filter (`notElem` ranked) ags
      logMsg =    ">>>>>>>>>>>>>>>>>>>>>>>> START INPUT\n"
                ++ inp
                ++ "\n>>>>>>>>>>>>>>>>>>>>>>>> START OUTPUT\n"
                ++ outp
                ++ "\n>>>>>>>>>>>>>>>>>>>>>>>> END Oracle call\n"
  guard $ trace logMsg True

  return (Ranking (ranked ++ remaining)
                  (guard (quitOnEmpty && null ranked) *> Just ApplySorry))
  where
    pgoal (g,(_nr,_usefulness)) = prettyGoal g

-- | This function apply a tactic to a list of AnnotatedGoals to retrive an ordered list according
-- | to its Prio/Deprio's functions
itRanking :: Tactic ProofContext -> [AnnotatedGoal] -> Bool -> ProofContext -> System -> Ranking [AnnotatedGoal]
itRanking tactic ags quitOnEmpty ctxt _sys =
    Ranking result (guard (quitOnEmpty && null rankedPrioGoals && null rankedDeprioGoals) *> Just ApplySorry)
    where
      -- Getting the functions from priorities
      prioToFunctions = map functionsPrio (_prios tactic)
      indexPrio = map (findIndex (==True)) $ map (applyIsPrio prioToFunctions ctxt _sys) ags    -- find the first prio that match every goal
      indexedPrio = sortOn fst $ zip indexPrio ags                                              -- ordening of goals given the fisrt prio they meet 
      groupedPrio = groupBy (\(indice1,_) (indice2,_) -> indice1 == indice2) indexedPrio        -- grouping goals by prio
      preorderedPrio = if (Nothing `elem` indexPrio) then map (snd . unzip) (tail groupedPrio) else map (snd . unzip) groupedPrio -- recovering ranked goals only (no prio = Nothing = fst)

      prioRankingFunctions = map rankingPrio (_prios tactic)                                              -- retrieve rankingFuntions for all Prio
      rankingFunToBeAppliedPrio = chooseRankingFunctionByPrio prioRankingFunctions (map head groupedPrio) -- only the functions for prios that are relevant
      prioReorderedGoals = applyRankingFunctions rankingFunToBeAppliedPrio preorderedPrio                 -- apply the function 

      rankedPrioGoals = concat prioReorderedGoals                                                         -- string the results in a single table
      
      -- Getting the functions from depriorities (same as above but dor the depriorities)
      deprioToFunctions = map functionsDeprio (_deprios tactic)
      indexDeprio = map (findIndex (==True)) $ map (applyIsPrio deprioToFunctions ctxt _sys) ags
      indexedDeprio = sortOn fst $ zip indexDeprio ags 
      groupedDeprio = groupBy (\(indice1,_) (indice2,_) -> indice1 == indice2) indexedDeprio
      preorderedDeprio = if (Nothing `elem` indexDeprio) then map (snd . unzip) (tail groupedDeprio) else map (snd . unzip) groupedDeprio -- recovering ranked goals only (no prio = Nothing = fst)

      deprioRankingFunctions = map rankingDeprio (_deprios tactic)
      rankingFunToBeAppliedDeprio = chooseRankingFunctionByPrio deprioRankingFunctions (map head groupedDeprio)
      deprioReorderedGoals = applyRankingFunctions rankingFunToBeAppliedDeprio preorderedDeprio

      rankedDeprioGoals = concat deprioReorderedGoals

      --Concatenation of results
      nonRanked = filter (`notElem` rankedPrioGoals++rankedDeprioGoals) ags
      result = rankedPrioGoals ++ nonRanked ++ rankedDeprioGoals

      -- Check whether a goal match a prio
      isPrio :: [(AnnotatedGoal, ProofContext, System) -> Bool] -> ProofContext -> System -> AnnotatedGoal -> Bool
      isPrio list agoal ctxt_ sys = or $ (sequenceA list) (sys,agoal,ctxt_)

      -- Try to match all prio with all goals
      applyIsPrio :: [[(AnnotatedGoal, ProofContext, System) -> Bool]] -> ProofContext -> System -> AnnotatedGoal -> [Bool]
      applyIsPrio [] _ _ _ = []
      applyIsPrio [xs] agoal ctxt_ sys = isPrio xs agoal ctxt_ sys:[]
      applyIsPrio (h:t) agoal ctxt_ sys = isPrio h agoal ctxt_ sys:applyIsPrio t agoal ctxt_ sys

      -- If it exists, retrieve the right rankingFuntion for all Goals recognized by a Prio/Deprio
      chooseRankingFunctionByPrio :: [Maybe ([AnnotatedGoal] -> [AnnotatedGoal])] -> [(Maybe Int,AnnotatedGoal)] -> [Maybe ([AnnotatedGoal] -> [AnnotatedGoal])]
      chooseRankingFunctionByPrio [] _ = []
      chooseRankingFunctionByPrio _ [] = []
      chooseRankingFunctionByPrio _ [(Nothing,_)] = []
      chooseRankingFunctionByPrio rf [(Just n,_)] = [rf !! n]
      chooseRankingFunctionByPrio rf ((Nothing,_):t) = (chooseRankingFunctionByPrio rf t)
      chooseRankingFunctionByPrio rf ((Just n,_):t) = (rf !! n):(chooseRankingFunctionByPrio rf t)

      -- If a given Prio/Deprio has a rankingFunction defined, apply it to the goals regognized by this Prio/Deprio
      applyRankingFunctions :: [Maybe ([AnnotatedGoal] -> [AnnotatedGoal])] -> [[AnnotatedGoal]] -> [[AnnotatedGoal]]
      applyRankingFunctions [] _ = []
      applyRankingFunctions _ [] = []
      applyRankingFunctions (hf:tf) (hg:tg) = (apply_ hf hg):(applyRankingFunctions tf tg)
        where
            apply_ :: Maybe ([AnnotatedGoal] -> [AnnotatedGoal]) -> [AnnotatedGoal] -> [AnnotatedGoal]
            apply_ Nothing l = l
            apply_ (Just f) l = f l



-- | A ranking function using a tactic to allow user-definable heuristics
--   for each lemma separately, using the user chosen defaultMethod heuristic
--   as the baseline.
internalTacticRanking :: Tactic ProofContext -> Bool -> ProofContext -> System -> [AnnotatedGoal] -> Ranking [AnnotatedGoal]
internalTacticRanking tactic quitOnEmpty ctxt _sys ags0 = trace logMsg res
    where
        defaultMethod =  _presort tactic                        -- retrieve baseline heuristic 
        ags = ranked $ rankGoals ctxt defaultMethod [tactic] _sys ags0   -- get goals accordingly
        pgoal (g,(_nr,_usefulness)) = prettyGoal g
        inp = unlines
                    (map (\(i,ag) -> show i ++": "++ (concat . lines . render $ pgoal ag))
                         (zip [(0::Int)..] ags))
        res = itRanking tactic ags quitOnEmpty ctxt _sys  -- apply the tactic ranking
        dict = M.fromList (zip ags [(0::Int)..])
        outp = map (fromMaybe (-1) . flip M.lookup dict) (ranked res)
        prettyOut = unlines (map show outp)
        logMsg = ">>>>>>>>>>>>>>>>>>>>>>>> START INPUT\n"
                     ++ inp
                     ++ "\n>>>>>>>>>>>>>>>>>>>>>>>> START OUTPUT\n"
                     ++ prettyOut
                     ++ "\n>>>>>>>>>>>>>>>>>>>>>>>> END Tactic call\n"

-- | Utilities for SAPiC translations specifically 

isAuthOutFact :: Fact t -> Bool
isAuthOutFact (Fact (ProtoFact _ "AuthOut" _) _ _) = True
isAuthOutFact  _                                 = False

isStateFact :: Goal -> Bool
isStateFact (PremiseG _ (Fact (ProtoFact _ n _) _ _)) = isPrefixOf "state_" n
isStateFact  _                                 = False

isUnlockAction :: Goal -> Bool
isUnlockAction (ActionG _ (Fact (ProtoFact _ "Unlock" _) _ _)) = True
isUnlockAction  _                                 = False

isEventAction :: Goal -> Bool
isEventAction (ActionG _ (Fact (ProtoFact _ "Event" _) _ _ )) = True
isEventAction  _                                 = False

isMID_Receiver :: Goal -> Bool
isMID_Receiver (PremiseG _ (Fact (ProtoFact _ "MID_Receiver" _) _ _)) = True
isMID_Receiver  _                                 = False

isMID_Sender :: Goal -> Bool
isMID_Sender (PremiseG _ (Fact (ProtoFact _ "MID_Sender" _) _ _)) = True
isMID_Sender  _                                 = False

isFirstInsertAction :: Goal -> Bool
isFirstInsertAction (ActionG _ (Fact (ProtoFact _ "Insert" _) _ (t:_)) ) = 
    case t of
    (viewTerm2 -> FPair (viewTerm2 -> Lit2( Con (Name PubName a)))  _) -> isPrefixOf "F_" (show a)
    _ -> False
isFirstInsertAction _ = False

isLastInsertAction :: Goal -> Bool
isLastInsertAction (ActionG _ (Fact (ProtoFact _ "Insert" _) _ (t:_)) ) = 
        case t of
            (viewTerm2 -> FPair (viewTerm2 -> Lit2( Con (Name PubName a)))  _) ->  isPrefixOf "L_" (show a)
            _ -> False
isLastInsertAction _ = False

isNotInsertAction :: Goal -> Bool
isNotInsertAction (ActionG _ (Fact (ProtoFact _ "Insert" _) _ _)) = False
isNotInsertAction  _                                 = True

isNotReceiveAction :: Goal -> Bool
isNotReceiveAction (ActionG _ (Fact (ProtoFact _ "Receive" _) _ _)) = False
isNotReceiveAction  _                                 = True

isStandardActionGoalButNotInsertOrReceive :: Goal -> Bool
isStandardActionGoalButNotInsertOrReceive g = 
   (isStandardActionGoal g) && (isNotInsertAction g) && (isNotReceiveAction g)

isStandardActionGoalButNotInsert :: Goal -> Bool
isStandardActionGoalButNotInsert g = 
       (isStandardActionGoal g) &&  (isNotInsertAction g) && (not $ isEventAction g)

-- | A ranking function tuned for the automatic verification of
-- protocols generated with the Sapic tool
sapicRanking :: ProofContext
              -> System
              -> [AnnotatedGoal] -> [AnnotatedGoal]
sapicRanking ctxt sys =
    sortOnUsefulness . unmark . sortDecisionTreeLast solveLast . sortDecisionTree solveFirst . goalNrRanking
  where
    oneCaseOnly = catMaybes . map getMsgOneCase . L.get pcSources $ ctxt

    isMsgOneCaseGoal goal = case msgPremise goal of
        Just (viewTerm -> FApp o _) | o `elem` oneCaseOnly -> True
        _                                                  -> False

    getMsgOneCase cd = case msgPremise (L.get cdGoal cd) of
      Just (viewTerm -> FApp o _)
        | length (getDisj (L.get cdCases cd)) == 1 -> Just o
      _                                            -> Nothing

    sortOnUsefulness = sortOn (tagUsefulness . snd . snd)
    unmark = map unmarkPremiseG

    tagUsefulness Useful                = 0 :: Int
    tagUsefulness ProbablyConstructible = 1
    tagUsefulness LoopBreaker           = 0
    tagUsefulness CurrentlyDeducible    = 2

    solveLast = 
        [ 
        isLastInsertAction . fst, -- move insert actions for positions that start with L_ to the end
        isLastProtoFact . fst, -- move Last proto facts (L_) to the end.
        isKnowsLastNameGoal . fst, -- move last names (L_key) to the end
        isEventAction . fst -- move event action, used in accountabilty translation, to the end
        ]

    solveFirst =
        [ isChainGoal . fst
        , isDisjGoalButNotProgress . fst --
        , isFirstProtoFact . fst
        , isMID_Receiver . fst --
        , isMID_Sender . fst --
        , isStateFact . fst
        , isUnlockAction . fst
        , isKnowsFirstNameGoal . fst
        , isFirstInsertAction . fst
        , isNonLoopBreakerProtoFactGoal
        , isStandardActionGoalButNotInsertOrReceive  . fst
        , isProgressDisj . fst
        , isNotAuthOut . fst
        , isPrivateKnowsGoal . fst
        -- , isFreshKnowsGoal . fst
        , isSplitGoalSmall . fst
        , isMsgOneCaseGoal . fst
        , isDoubleExpGoal . fst
        , isNoLargeSplitGoal . fst 
        ]
        -- move the rest (mostly more expensive KU-goals) before expensive
        -- equation splits

    -- FIXME: This small split goal preferral is quite hacky when using
    -- induction. The problem is that we may end up solving message premise
    -- goals all the time instead of performing a necessary split. We should make
    -- sure that a split does not get too old.
    smallSplitGoalSize = 3

    -- Be conservative on splits that don't exist.
    isSplitGoalSmall (SplitG sid) =
        maybe False (<= smallSplitGoalSize) $ splitSize (L.get sEqStore sys) sid
    isSplitGoalSmall _            = False

    isNoLargeSplitGoal goal@(SplitG _) = isSplitGoalSmall goal
    isNoLargeSplitGoal _               = True

--  Problematic when using handles.
--    isFreshKnowsGoal goal = case msgPremise goal of
--        Just (viewTerm -> Lit (Var lv)) | lvarSort lv == LSortFresh -> True
--        _                                                           -> False
    -- we recognize any variable starting with h as a handle an deprioritize 

-- | A ranking function tuned for a specific model of the
-- PKCS#11 keymanagement API formulated in SAPIC's input language.
sapicPKCS11Ranking :: ProofContext
              -> System
              -> [AnnotatedGoal] -> [AnnotatedGoal]
sapicPKCS11Ranking ctxt sys =
    sortOnUsefulness . unmark . sortDecisionTreeLast solveLast . sortDecisionTree solveFirst . goalNrRanking
  where
    oneCaseOnly = catMaybes . map getMsgOneCase . L.get pcSources $ ctxt


    getMsgOneCase cd = case msgPremise (L.get cdGoal cd) of
      Just (viewTerm -> FApp o _)
        | length (getDisj (L.get cdCases cd)) == 1 -> Just o
      _                                            -> Nothing

    sortOnUsefulness = sortOn (tagUsefulness . snd . snd)

    unmark = map unmarkPremiseG
    tagUsefulness Useful                = 0 :: Int
    tagUsefulness ProbablyConstructible = 1
    tagUsefulness LoopBreaker           = 0
    tagUsefulness CurrentlyDeducible    = 2

    solveLast = 
        [ 
        -- isNotInsertAction . fst 
        -- ,        
        isKnowsHandleGoal . fst,
        isLastProtoFact . fst,
        isEventAction . fst
        ]
        -- move the Last proto facts (L_) to the end.

    solveFirst =
        [ isChainGoal . fst
        , isDisjGoal . fst
        , isFirstProtoFact . fst
        , isStateFact . fst
        , isUnlockAction . fst
        , isInsertTemplateAction . fst
        , isNonLoopBreakerProtoFactGoal
        , isStandardActionGoalButNotInsert  . fst
        , isNotAuthOut . fst
        , isPrivateKnowsGoal . fst
        -- , isFreshKnowsGoal . fst
        , isSplitGoalSmall . fst
        , isMsgOneCaseGoal . fst
        , isDoubleExpGoal . fst
        , isNoLargeSplitGoal . fst 
        ]
        -- move the rest (mostly more expensive KU-goals) before expensive
        -- equation splits

    -- FIXME: This small split goal preferral is quite hacky when using
    -- induction. The problem is that we may end up solving message premise
    -- goals all the time instead of performing a necessary split. We should make
    -- sure that a split does not get too old.
    smallSplitGoalSize = 3

    isInsertTemplateAction (ActionG _ (Fact (ProtoFact _ "Insert" _) _ (t:_)) ) = 
        case t of
            (viewTerm2 -> FPair (viewTerm2 -> Lit2( Con (Name PubName a)))  _) -> isPrefixOf "template" (show a)
            _ -> False
    isInsertTemplateAction _ = False

--  Problematic when using handles.
--    isFreshKnowsGoal goal = case msgPremise goal of
--        Just (viewTerm -> Lit (Var lv)) | lvarSort lv == LSortFresh -> True
--        _                                                           -> False
    -- we recognize any variable starting with h as a handle an deprioritize 
    isHandle lv = isPrefixOf "h" (lvarName lv)

    isKnowsHandleGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | ((lvarSort lv  == LSortFresh) && isHandle lv)-> True
        _                                                           -> False

    isMsgOneCaseGoal goal = case msgPremise goal of
        Just (viewTerm -> FApp o _) | o `elem` oneCaseOnly -> True
        _                                                  -> False

    -- Be conservative on splits that don't exist.
    isSplitGoalSmall (SplitG sid) =
        maybe False (<= smallSplitGoalSize) $ splitSize (L.get sEqStore sys) sid
    isSplitGoalSmall _            = False

    isNoLargeSplitGoal goal@(SplitG _) = isSplitGoalSmall goal
    isNoLargeSplitGoal _               = True


-- | A ranking function tailored for automatic verification of stateful
-- protocols which can make heavy use of injectivity properties
injRanking :: ProofContext
            -> Bool
            -> System
            -> [AnnotatedGoal] -> [AnnotatedGoal]
injRanking ctxt allowLoopBreakers sys =
    (sortOnUsefulness . unmark . sortDecisionTree [notSolveLast] . sortDecisionTree solveFirst . goalNrRanking)
  where
    oneCaseOnly = catMaybes . map getMsgOneCase . L.get pcSources $ ctxt

    getMsgOneCase cd = case msgPremise (L.get cdGoal cd) of
      Just (viewTerm -> FApp o _)
        | length (getDisj (L.get cdCases cd)) == 1 -> Just o
      _                                            -> Nothing

    sortOnUsefulness = sortOn (tagUsefulness . snd . snd)

    tagUsefulness Useful                = 0 :: Int
    tagUsefulness ProbablyConstructible = 1
    tagUsefulness LoopBreaker           = 1
    tagUsefulness CurrentlyDeducible    = 2

    unmark | allowLoopBreakers = map unmarkPremiseG
           | otherwise         = id

    -- move the Last proto facts (L_) and large splits to the end by
    -- putting all goals that shouldn't be solved last in front
    notSolveLast goaltuple = (isNoLargeSplitGoal $ fst goaltuple)
                            && (isNonSolveLastGoal $ fst goaltuple)
                            && (isNotKnowsLastNameGoal $ fst goaltuple)

    solveFirst =
        [ isImmediateGoal . fst         -- Goals with the I_ prefix
        , isHighPriorityGoal . fst      -- Goals with the F_ prefix, by goal number
        , isMedPriorityGoal             -- Various important goals, by goal number
        , isLowPriorityGoal ]
        -- move the rest (mostly more expensive KU-goals) before expensive
        -- equation splits

    smallSplitGoalSize = 3

    -- Putting the goals together like this ranks them by goal number
    -- within the same priority class, so one type of goal doesn't always win
    -- (assuming the same usefulness)
    isHighPriorityGoal goal = (isKnowsFirstNameGoal goal)
                                || (isSolveFirstGoal goal)
                                || (isChainGoal goal)
                                || (isFreshKnowsGoal goal)

    isMedPriorityGoal goaltuple = (isStandardActionGoal $ fst goaltuple)
                                    || (isDisjGoal $ fst goaltuple)
                                    || (isPrivateKnowsGoal $ fst goaltuple)
                                    || (isSplitGoalSmall $ fst goaltuple)
                                    || (isMsgOneCaseGoal $ fst goaltuple)
                                    || (isNonLoopBreakerProtoFactGoal goaltuple)

    isLowPriorityGoal goaltuple = (isDoubleExpGoal $ fst goaltuple)
                                || (isSignatureGoal $ fst goaltuple)
                                || (isProtoFactGoal goaltuple)

    isProtoFactGoal (PremiseG _ fa, (_, _)) = not (isKFact fa)
    isProtoFactGoal _                       = False

    -- Detect 'I_' (immediate) fact and term prefix for heuristics
    isImmediateGoal (PremiseG _ (Fact (ProtoFact _ ('I':'_':_) _) _ _)) = True
    isImmediateGoal (ActionG  _ (Fact (ProtoFact _ ('I':'_':_) _) _ _)) = True
    isImmediateGoal goal = isKnowsImmediateNameGoal goal

    isNonSolveLastGoal (PremiseG _ fa) = not $ isSolveLastFact fa
    isNonSolveLastGoal (ActionG  _ fa) = not $ isSolveLastFact fa
    isNonSolveLastGoal _               = True

    isSolveFirstGoal (PremiseG _ fa) = isSolveFirstFact fa
    isSolveFirstGoal (ActionG  _ fa) = isSolveFirstFact fa
    isSolveFirstGoal _               = False

    isImmediateName lv = isPrefixOf "I_" (lvarName lv)

    isNotKnowsLastNameGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | ((lvarSort lv  == LSortFresh) && isLastName lv)-> False
        _                                                           -> True

    isKnowsImmediateNameGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | ((lvarSort lv  == LSortFresh) && isImmediateName lv)-> True
        _                                                           -> False
    isFreshKnowsGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | (lvarSort lv == LSortFresh) -> True
        _                                                             -> False

    isMsgOneCaseGoal goal = case msgPremise goal of
        Just (viewTerm -> FApp o _) | o `elem` oneCaseOnly -> True
        _                                                  -> False

    isSignatureGoal goal = case msgPremise goal of
        Just (viewTerm -> FApp (NoEq (f, _)) _) | (BC.unpack f) == "sign" -> True
        _                                                                 -> False

    -- Be conservative on splits that don't exist.
    isSplitGoalSmall (SplitG sid) =
        maybe False (<= smallSplitGoalSize) $ splitSize (L.get sEqStore sys) sid
    isSplitGoalSmall _            = False

    isNoLargeSplitGoal goal@(SplitG _) = isSplitGoalSmall goal
    isNoLargeSplitGoal _               = True

-- | A ranking function tuned for the automatic verification of
-- classical security protocols that exhibit a well-founded protocol premise
-- fact flow.
smartRanking :: ProofContext
             -> Bool   -- True if PremiseG loop-breakers should not be delayed
             -> System
             -> [AnnotatedGoal] -> [AnnotatedGoal]
smartRanking ctxt allowPremiseGLoopBreakers sys =
    moveNatToEnd . sortOnUsefulness . unmark . sortDecisionTree notSolveLast . sortDecisionTree solveFirst . goalNrRanking
  where
    oneCaseOnly = catMaybes . map getMsgOneCase . L.get pcSources $ ctxt

    getMsgOneCase cd = case msgPremise (L.get cdGoal cd) of
      Just (viewTerm -> FApp o _)
        | length (getDisj (L.get cdCases cd)) == 1 -> Just o
      _                                            -> Nothing

    sortOnUsefulness = sortOn (tagUsefulness . snd . snd)

    moveNatToEnd = sortOn isNatSubtermSplit
    isNatSubtermSplit (SubtermG st, _) = isNatSubterm st
    isNatSubtermSplit _                = False

    tagUsefulness Useful                = 0 :: Int
    tagUsefulness ProbablyConstructible = 1
    tagUsefulness LoopBreaker           = 1
    tagUsefulness CurrentlyDeducible    = 2

    unmark | allowPremiseGLoopBreakers = map unmarkPremiseG
           | otherwise                 = id

    notSolveLast =
       [ isNonSolveLastGoal . fst ]
       -- move the Last proto facts (L_) to the end by sorting all other goals in front

    solveFirst =
        [ isChainGoal . fst
        , isDisjGoal . fst
        , isSolveFirstGoal . fst
        , isNonLoopBreakerProtoFactGoal
        , isStandardActionGoal . fst
        , isNotAuthOut . fst
        , isPrivateKnowsGoal . fst
        , isFreshKnowsGoal . fst
        , isSplitGoalSmall . fst
        , isMsgOneCaseGoal . fst
        , isSignatureGoal . fst
        , isDoubleExpGoal . fst
        , isNoLargeSplitGoal . fst ]
        -- move the rest (mostly more expensive KU-goals) before expensive
        -- equation splits

    -- FIXME: This small split goal preferral is quite hacky when using
    -- induction. The problem is that we may end up solving message premise
    -- goals all the time instead of performing a necessary split. We should make
    -- sure that a split does not get too old.
    smallSplitGoalSize = 3

    isNonSolveLastGoal (PremiseG _ fa) = not $ isSolveLastFact fa
    isNonSolveLastGoal (ActionG  _ fa) = not $ isSolveLastFact fa
    isNonSolveLastGoal _               = True

    isSolveFirstGoal (PremiseG _ fa) = isSolveFirstFact fa
    isSolveFirstGoal (ActionG _ fa)  = isSolveFirstFact fa
    isSolveFirstGoal _               = False

    isFreshKnowsGoal goal = case msgPremise goal of
        Just (viewTerm -> Lit (Var lv)) | lvarSort lv == LSortFresh -> True
        _                                                           -> False

    isMsgOneCaseGoal goal = case msgPremise goal of
        Just (viewTerm -> FApp o _) | o `elem` oneCaseOnly -> True
        _                                                  -> False

    isSignatureGoal goal = case msgPremise goal of
        Just (viewTerm -> FApp (NoEq (f, _)) _) | (BC.unpack f) == "sign" -> True
        _                                                                 -> False

    -- Be conservative on splits that don't exist.
    isSplitGoalSmall (SplitG sid) =
        maybe False (<= smallSplitGoalSize) $ splitSize (L.get sEqStore sys) sid
    isSplitGoalSmall _            = False

    isNoLargeSplitGoal goal@(SplitG _) = isSplitGoalSmall goal
    isNoLargeSplitGoal _               = True

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
    isTrivialMsgFact (Fact _ _ ts) = case ts of
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
    Invalidated -> lineComment_ "proof may have been invalidated by editing a reuse lemma above. You should "
    Finished Solved -> keyword_ "SOLVED" <-> lineComment_ "trace found"
    Induction  -> keyword_ "induction"
    Finished Unfinishable -> keyword_ "UNFINISHABLE" <-> lineComment_ "reducible operator in subterm"
    Sorry reason ->
        fsep [keyword_ "sorry", maybe emptyDoc closedComment_ reason]
    SolveGoal goal -> keyword_ "solve(" <-> prettyGoal goal <-> keyword_ ")"
    Simplify -> keyword_ "simplify"
    Finished (Contradictory reason) ->
        sep [ keyword_ "contradiction"
            , maybe emptyDoc (closedComment . prettyContradiction) reason
            ]

-- | Pretty-print a diff proof method.
prettyDiffProofMethod :: HighlightDocument d => DiffProofMethod -> d
prettyDiffProofMethod method = case method of
    DiffMirrored             -> keyword_ "MIRRORED"
    DiffAttack               -> keyword_ "ATTACK" <-> lineComment_ "trace found"
    DiffUnfinishable         -> keyword_ "UNFINISHABLEdiff" <-> lineComment_ "reducible operator in subterm"
    DiffSorry reason         ->
        fsep [keyword_ "sorry", maybe emptyDoc lineComment_ reason]
-- MERGED with solved.
--    DiffTrivial              -> keyword_ "trivial"
    DiffRuleEquivalence      -> keyword_ "rule-equivalence"
    DiffBackwardSearch       -> keyword_ "backward-search"  
    DiffBackwardSearchStep s -> keyword_ "step(" <-> prettyProofMethod s <-> keyword_ ")"

