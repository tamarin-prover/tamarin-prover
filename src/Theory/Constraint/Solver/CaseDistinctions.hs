-- |
-- Copyright   : (c) 2011,2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Big-step proofs using case distinctions on the possible sources of a fact.
module Theory.Constraint.Solver.CaseDistinctions (
  -- * Precomputed case distinctions

  -- ** Queries
    unsolvedChainConstraints

  -- ** Construction
  , precomputeCaseDistinctions
  , refineWithTypingAsms

  -- ** Application
  , solveWithCaseDistinction

  ) where

import           Prelude                                 hiding (id, (.))
import           Safe

import           Data.Foldable                           (asum)
import           Data.Maybe                              (isJust)
import qualified Data.Set                                as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.Reader
import           Control.Monad.State                     (gets)
import           Control.Parallel.Strategies

import           Text.PrettyPrint.Highlight

import           Extension.Data.Label
import           Extension.Prelude

import           Theory.Constraint.Solver.Contradictions (contradictorySystem)
import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.Solver.Simplify
import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model


------------------------------------------------------------------------------
-- Precomputing case distinctions
------------------------------------------------------------------------------

-- | The number of remaining chain constraints of each case.
unsolvedChainConstraints :: CaseDistinction -> [Int]
unsolvedChainConstraints =
    map (S.size . get sChains . snd) . getDisj . get cdCases


-- Construction
---------------

-- | The initial case distinction if the given goal is required and the
-- given typing assumptions are justified.
initialCaseDistinction
    :: ProofContext
    -> [LNGuarded]  -- ^ Typing assumptions. PRE: Must be closed formulas!
    -> Goal
    -> CaseDistinction
initialCaseDistinction ctxt typAsms goal =
    CaseDistinction goal cases
  where
    polish ((name, se), _) = ([name], se)
    se0   = set sFormulas (S.fromList typAsms) (emptySystem UntypedCaseDist)
    cases = fmap polish $ runReduction instantiate ctxt se0 (avoid (goal, se0))
    instantiate = solveGoal goal

-- | Refine a source case distinction by applying the additional proof step.
refineCaseDistinction
    :: ProofContext
    -> Reduction (a, [String])  -- proof step with result and path extension
    -> CaseDistinction
    -> ([a], CaseDistinction)
refineCaseDistinction ctxt proofStep th =
    ( map fst $ getDisj refinement
    , set cdCases (snd <$> refinement) th )
  where
    fs         = avoid th
    refinement = do
        (names, se)   <- get cdCases th
        ((x, names'), se') <- fst <$> runReduction proofStep ctxt se fs
        return (x, (combine names names', se'))

    -- Combine names such that the coerce rule is blended out.
    combine []            ns' = ns'
    combine ("coerce":ns) ns' = combine ns ns'
    combine (n       :_)  _   = [n]

-- | Solves all chain and splitting goals as well as all premise goals solvable
-- with one of the given precomputed requires case distinction theorems, while
-- repeatedly simplifying the proof state.
--
-- Returns the names of the steps applied.
solveAllSafeGoals :: [CaseDistinction] -> Reduction [String]
solveAllSafeGoals ths =
    solve []
  where
    safeGoal _            (ChainG _)              = True
    safeGoal _            (PremDnKG _)            = True
    safeGoal _            (ActionG _ fa)          = not $ isKUFact fa
    safeGoal splitAllowed (DisjG _)               = splitAllowed
    -- NOTE: Uncomment the line below to get more extensive case splitting
    -- for precomputed case distinctions.
    -- safeGoal splitAllowed (SplitG _ _) = splitAllowed
    safeGoal _            (PremiseG _ fa mayLoop) = not (mayLoop || isKFact fa)
    safeGoal _            _                       = False

    nonLoopingGoal (PremiseG _ _ mayLoop) = not mayLoop
    nonLoopingGoal _                      = True

    solve caseNames = do
        simplifySystem
        ctxt <- ask
        contradictoryIf =<< gets (contradictorySystem ctxt)
        goals  <- gets openGoals
        chains <- getM sChains
        -- try to either solve a safe goal or use one of the precomputed case
        -- distinctions
        let noChainGoals = null [ () | ChainG _ <- goals ]
            -- we perform equation splits, if there is a chain goal starting
            -- from a message variable; i.e., a chain constraint that is no
            -- open goal.
            splitAllowed    = noChainGoals && not (S.null chains)
            safeGoals       = filter (safeGoal splitAllowed) goals
            nonLoopingGoals = filter nonLoopingGoal goals
            nextStep        =
                ((fmap return . solveGoal) <$> headMay safeGoals) <|>
                (asum $ map (solveWithCaseDistinction ctxt ths) nonLoopingGoals)
        case nextStep of
          Nothing   -> return $ caseNames
          Just step -> solve . (caseNames ++) =<< step


------------------------------------------------------------------------------
-- Applying precomputed case distinctions
------------------------------------------------------------------------------

-- | Match a precomputed 'CaseDistinction' to a goal.
matchToGoal
    :: ProofContext     -- ^ Proof context used for refining the case distinction.
    -> CaseDistinction  -- ^ Case distinction to use.
    -> Goal             -- ^ Goal to match
    -> Maybe CaseDistinction
    -- ^ An adapted version of the case distinction and a matcher of the case
    -- distinction goal to the substitution goal.
matchToGoal ctxt th goalTerm =
  case (goalTerm, get cdGoal th) of
    ( PremiseG      (iTerm, premIdxTerm) faTerm _mayLoopTerm
     ,PremiseG pPat@(iPat,  _          ) faPat  _mayLoopPat  ) ->
        let match = faTerm `matchFact` faPat <> iTerm `matchLVar` iPat in
        case runReader (solveMatchLNTerm match) (get pcMaudeHandle ctxt) of
            []      -> Nothing
            subst:_ ->
                let refine = do
                        modM sEdges (substNodePrem pPat (iPat, premIdxTerm))
                        void (solveSubstEqs SplitNow subst)
                        return ((), [])
                in Just $ snd $ refineCaseDistinction ctxt refine th

    (ActionG iTerm faTerm, ActionG iPat faPat) ->
        let match = faTerm `matchFact` faPat <> iTerm `matchLVar` iPat in
        case runReader (solveMatchLNTerm match) (get pcMaudeHandle ctxt) of
            []      -> Nothing
            subst:_ ->
                let refine = do
                        void (solveSubstEqs SplitNow subst)
                        return ((), [])
                in Just $ snd $ refineCaseDistinction ctxt refine th

    -- No other matches possible, as we only precompute case distinctions for
    -- premises and KU-actions.
    _ -> Nothing
  where
    substNodePrem from to = S.map
        (\ e@(Edge c p) -> if p == from then Edge c to else e)

-- | Try to solve a premise goal or 'Ded' action using the first precomputed
-- case distinction with a matching premise.
solveWithCaseDistinction :: ProofContext
                         -> [CaseDistinction]
                         -> Goal
                         -> Maybe (Reduction [String])
solveWithCaseDistinction hnd ths goal = do
    -- goal <- toBigStepGoal goal0
    asum [ applyCaseDistinction hnd th goal | th <- ths ]

-- | Apply a precomputed case distinction theorem to a required fact.
applyCaseDistinction :: ProofContext
                     -> CaseDistinction    -- ^ Case distinction theorem.
                     -> Goal               -- ^ Required goal
                     -> Maybe (Reduction [String])
applyCaseDistinction ctxt th goal
  | isJust $ matchToGoal ctxt th goal = Just $ do
        markGoalAsSolved "precomputed" goal
        thRenamed <- rename th
        let thInst = fromJustNote "applyCaseDistinction: impossible" $
                         matchToGoal ctxt thRenamed goal
        (names, sysTh) <- disjunctionOfList $ getDisj $ get cdCases thInst
        conjoinSystem sysTh
        return names

  | otherwise = Nothing

-- | Saturate the case distinctions with respect to each other such that no
-- additional splitting is introduced; i.e., only rules with a single or no
-- conclusion are used for the saturation.
saturateCaseDistinctions
    :: ProofContext -> [CaseDistinction] -> [CaseDistinction]
saturateCaseDistinctions ctxt =
    go
  where
    go ths =
        if any or (changes `using` parList rdeepseq)
          then go ths'
          else ths'
      where
        (changes, ths') = unzip $ map (refineCaseDistinction ctxt solver) ths
        goodTh th  = length (getDisj (get cdCases th)) <= 1
        solver     = do names <- solveAllSafeGoals (filter goodTh ths)
                        return (not $ null names, names)

-- | Precompute a saturated set of case distinctions.
precomputeCaseDistinctions
    :: ProofContext
    -> [LNGuarded] -- ^ Typing assumptions.
    -> [CaseDistinction]
precomputeCaseDistinctions ctxt typAsms =
    map cleanupCaseNames $ saturateCaseDistinctions ctxt rawCaseDists
  where
    cleanupCaseNames = modify cdCases $ fmap $ first $
        filter (not . null)
      . map (filter (`elem` '_' : ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']))

    rawCaseDists =
      initialCaseDistinction ctxt typAsms <$> (protoGoals ++ msgGoals)

    -- construct case distinction starting from facts from non-special rules
    protoGoals = someProtoGoal <$> absProtoFacts
    msgGoals   = someKUGoal <$> absMsgFacts

    getProtoFact (Fact KUFact _ ) = mzero
    getProtoFact (Fact KDFact _ ) = mzero
    getProtoFact fa               = return fa

    absFact (Fact tag ts) = (tag, length ts)

    nMsgVars n = [ varTerm (LVar "t" LSortMsg i) | i <- [1..fromIntegral n] ]

    someProtoGoal :: (FactTag, Int) -> Goal
    someProtoGoal (tag, arity) =
        PremiseG (someNodeId, PremIdx 0) (Fact tag (nMsgVars arity)) False

    someKUGoal :: LNTerm -> Goal
    someKUGoal m =
        ActionG someNodeId (Fact KUFact [varTerm (LVar "f_" LSortMsg 0), m])

    someNodeId = LVar "i" LSortNode 0

    -- FIXME: Also use facts from proof context.
    rules = get pcRules ctxt
    absProtoFacts = sortednub $ do
        ru <- joinAllRules rules
        fa <- absFact <$> (getProtoFact =<< (get rConcs ru ++ get rPrems ru))
        -- exclude facts handled specially by the prover
        guard (not $ fst fa `elem` [OutFact, InFact, FreshFact])
        return fa

    absMsgFacts :: [LNTerm]
    absMsgFacts = asum $ sortednub $
      [ do return $ lit $ Var (LVar "t" LSortFresh 1)

      , [ fAppNonAC (s,k) $ nMsgVars k
        | (s,k) <- S.toList . allFunctionSymbols  . mhMaudeSig . get sigmMaudeHandle . get pcSignature $ ctxt
        , (s,k) `S.notMember` implicitFunSig, k > 0 ]
      ]

-- | Refine a set of case distinction by exploiting additional typing
-- assumptions.
refineWithTypingAsms
    :: [FormulaAC]        -- ^ Typing assumptions to use.
    -> ProofContext       -- ^ Proof context to use.
    -> [CaseDistinction]  -- ^ Original, untyped case distinctions.
    -> [CaseDistinction]  -- ^ Refined, typed case distinctions.
refineWithTypingAsms typAsms0 ctxt cases0 =
    fmap (modifySystems removeFormulas) $
    saturateCaseDistinctions ctxt $
    modifySystems updateSystem <$> cases0
  where
    typAsms = map (either error id . formulaToGuarded) typAsms0
    modifySystems = modify cdCases . fmap . second
    updateSystem se =
        modify sFormulas (S.union (S.fromList typAsms)) $
        set sCaseDistKind TypedCaseDist                 $ se
    removeFormulas = set sFormulas S.empty . set sSolvedFormulas S.empty
