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
import qualified Data.Map                                as M
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
    map (length . unsolvedChains . snd) . getDisj . get cdCases


-- Construction
---------------

-- | The initial case distinction if the given goal is required and the
-- given typing assumptions are justified.
initialCaseDistinction
    :: ProofContext
    -> [LNGuarded] -- ^ Axioms.
    -> Goal
    -> CaseDistinction
initialCaseDistinction ctxt axioms goal =
    CaseDistinction goal cases
  where
    polish ((name, se), _) = ([name], se)
    se0   = insertLemmas axioms $ emptySystem UntypedCaseDist
    cases = fmap polish $
        runReduction instantiate ctxt se0 (avoid (goal, se0))
    instantiate = do
        insertGoal goal False
        solveGoal goal

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
    safeGoal _       (_,   (_, LoopBreaker)) = False
    safeGoal doSplit (goal, _              ) =
      case goal of
        ChainG _ _    -> True
        ActionG _ fa  -> not (isKUFact fa)
        PremiseG _ fa -> not (isKUFact fa)
        DisjG _       -> doSplit
        -- Uncomment to get more extensive case splitting
        -- SplitG _   -> doSplit
        SplitG _      -> False

    usefulGoal (_, (_, Useful)) = True
    usefulGoal _                = False

    solve caseNames = do
        simplifySystem
        ctxt <- ask
        contradictoryIf =<< gets (contradictorySystem ctxt)
        goals  <- gets openGoals
        chains <- gets unsolvedChains
        -- try to either solve a safe goal or use one of the precomputed case
        -- distinctions
        let noChainGoals = null [ () | (ChainG _ _, _) <- goals ]
            -- we perform equation splits, if there is a chain goal starting
            -- from a message variable; i.e., a chain constraint that is no
            -- open goal.
            splitAllowed = noChainGoals && not (null chains)
            safeGoals    = fst <$> filter (safeGoal splitAllowed) goals
            usefulGoals  = fst <$> filter usefulGoal goals
            nextStep        =
                ((fmap return . solveGoal) <$> headMay safeGoals) <|>
                (asum $ map (solveWithCaseDistinction ctxt ths) usefulGoals)
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
    -> Maybe (Reduction [String])
    -- ^ A constraint reduction step to apply the resulting case distinction.
    -- Note that this step assumes that the theorem has been imported using
    -- 'someInst' into the context that this reduction is executed in.
    --
    -- FIXME: This is a mess. Factor code such that this inter-dependency
    -- between 'applyCaseDistinction' and 'matchToGoal' goes away.
matchToGoal ctxt th goalTerm =
  case (goalTerm, get cdGoal th) of
    ( PremiseG      (iTerm, premIdxTerm) faTerm
     ,PremiseG pPat@(iPat,  _          ) faPat  ) ->
        let match = faTerm `matchFact` faPat <> iTerm `matchLVar` iPat in
        case runReader (solveMatchLNTerm match) (get pcMaudeHandle ctxt) of
            []      -> Nothing
            subst:_ -> Just $ genericApply subst $
                -- add the missing edge to each case of the theorem
                modify sEdges (substNodePrem pPat (iPat, premIdxTerm))

    (ActionG iTerm faTerm, ActionG iPat faPat) ->
        let match = faTerm `matchFact` faPat <> iTerm `matchLVar` iPat in
        case runReader (solveMatchLNTerm match) (get pcMaudeHandle ctxt) of
            []      -> Nothing
            subst:_ -> Just $ genericApply subst id

    -- No other matches possible, as we only precompute case distinctions for
    -- premises and KU-actions.
    _ -> Nothing
  where
    genericApply subst systemModifier = do
        void (solveSubstEqs SplitNow subst)
        (names, sysTh) <- disjunctionOfList $ getDisj $ get cdCases th
        conjoinSystem (systemModifier sysTh)
        return names

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
        fromJustNote "applyCaseDistinction: impossible" $
            matchToGoal ctxt thRenamed goal

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
    -> [LNGuarded]       -- ^ Axioms.
    -> [CaseDistinction]
precomputeCaseDistinctions ctxt axioms =
    map cleanupCaseNames $ saturateCaseDistinctions ctxt rawCaseDists
  where
    cleanupCaseNames = modify cdCases $ fmap $ first $
        filter (not . null)
      . map (filter (`elem` '_' : ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']))

    rawCaseDists =
        initialCaseDistinction ctxt axioms <$> (protoGoals ++ msgGoals)

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
        PremiseG (someNodeId, PremIdx 0) (Fact tag (nMsgVars arity))

    someKUGoal :: LNTerm -> Goal
    someKUGoal m = ActionG someNodeId (kuFact m)

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
    :: [LNGuarded]        -- ^ Typing assumptions to use.
    -> ProofContext       -- ^ Proof context to use.
    -> [CaseDistinction]  -- ^ Original, untyped case distinctions.
    -> [CaseDistinction]  -- ^ Refined, typed case distinctions.
refineWithTypingAsms assumptions ctxt cases0 =
    fmap (modifySystems removeFormulas) $
    saturateCaseDistinctions ctxt $
    modifySystems updateSystem <$> cases0
  where
    modifySystems   = modify cdCases . fmap . second
    updateSystem se =
        modify sFormulas (S.union (S.fromList assumptions)) $
        set sCaseDistKind TypedCaseDist                     $ se
    removeFormulas =
        modify sGoals (M.filterWithKey isNoDisjGoal)
      . set sFormulas S.empty
      . set sSolvedFormulas S.empty

    isNoDisjGoal (DisjG _)  _ = False
    isNoDisjGoal _          _ = True



