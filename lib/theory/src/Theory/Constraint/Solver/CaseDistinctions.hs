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

  -- ** Redundant cases
  , removeRedundantCases

  ) where

import           Prelude                                 hiding (id, (.))
import           Safe

import           Data.Foldable                           (asum)
import qualified Data.Map                                as M
import qualified Data.Set                                as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.Reader
import           Control.Monad.State                     (gets)
import           Control.Parallel.Strategies

import           System.IO.Error

import           System.Environment
import           System.IO.Unsafe

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

import           Control.Monad.Bind

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
    , set cdCases newCases th )
  where
    newCases =   Disj . removeRedundantCases ctxt stableVars snd
               . map (second (modify sSubst (restrict stableVars)))
               . getDisj $ snd <$> refinement

    stableVars = frees (get cdGoal th)

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
    extensiveSplitting = unsafePerformIO $
      (getEnv "TAMARIN_EXTENSIVE_SPLIT" >> return True) `catchIOError` \_ -> return False
    safeGoal _       (_,   (_, LoopBreaker)) = False
    safeGoal doSplit (goal, _              ) =
      case goal of
        ChainG _ _    -> True
        ActionG _ fa  -> not (isKUFact fa)
        PremiseG _ fa -> not (isKUFact fa) && doSplit
        DisjG _       -> doSplit
        -- Uncomment to get more extensive case splitting
        SplitG _      -> extensiveSplitting && doSplit
        -- SplitG _      -> False

    usefulGoal (_, (_, Useful)) = True
    usefulGoal _                = False

    isKDPrem (PremiseG _ fa,_) = isKDFact fa
    isKDPrem _                 = False
    isChainPrem1 (ChainG _ (_,PremIdx 1),_) = True
    isChainPrem1 _                          = False

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
            kdPremGoals  = fst <$> filter (\g -> isKDPrem g || isChainPrem1 g) goals
            usefulGoals  = fst <$> filter usefulGoal goals
            nextStep     =
                ((fmap return . solveGoal) <$> headMay kdPremGoals) <|>
                ((fmap return . solveGoal) <$> headMay safeGoals) <|>
                (asum $ map (solveWithCaseDistinction ctxt ths) usefulGoals)
        case nextStep of
          Nothing   -> return $ caseNames
          Just step -> solve . (caseNames ++) =<< step



------------------------------------------------------------------------------
-- Redundant Case Distinctions                                              --
------------------------------------------------------------------------------

-- | Given a list of stable variables (that are referenced from outside and cannot be simply
-- renamed) and a list containing systems, this function returns a subsequence of the list
-- such that for all removed systems, there is a remaining system that is equal modulo
-- renaming of non-stable variables.
removeRedundantCases :: ProofContext -> [LVar] -> (a -> System) ->  [a] -> [a]
removeRedundantCases ctxt stableVars getSys cases0 =
    -- usually, redundant cases only occur with the multiset and bilinear pairing theories
    if enableBP msig || enableMSet msig then cases else cases0
  where
    -- decorate with index and normed version of the system
    decoratedCases = map (second addNormSys) $  zip [(0::Int)..] cases0
    -- drop cases where the normed systems coincide
    cases          =   map (fst . snd) . sortOn fst . sortednubOn (snd . snd) $ decoratedCases

    addNormSys = id &&& ((modify sEqStore dropNameHintsBound) . renameDropNameHints . getSys)

    -- this is an ordering that works well in the cases we tried
    orderedVars sys =
        filter ((/= LSortNode) . lvarSort) $ map fst . sortOn snd . varOccurences $ sys

    -- rename except for stable variables, drop name hints, and import ordered vars first
    renameDropNameHints sys =
      (`evalFresh` avoid stableVars) . (`evalBindT` stableVarBindings) $ do
          _ <- renameDropNamehint (orderedVars sys)
          renameDropNamehint sys
      where
        stableVarBindings = M.fromList (map (\v -> (v, v)) stableVars)

    msig = mhMaudeSig . get pcMaudeHandle $ ctxt

------------------------------------------------------------------------------
-- Applying precomputed case distinctions
------------------------------------------------------------------------------

-- | Match a precomputed 'CaseDistinction' to a goal. Returns the instantiated
-- 'CaseDistinction' with the given goal if possible
matchToGoal
    :: ProofContext     -- ^ Proof context used for refining the case distinction.
    -> CaseDistinction  -- ^ Case distinction to use.
    -> Goal             -- ^ Goal to match
    -> Maybe CaseDistinction
    -- ^ An adapted version of the case distinction with the given goal
matchToGoal ctxt th0 goalTerm =
  if not $ maybeMatcher (goalTerm, get cdGoal th0) then Nothing else
  case (goalTerm, get cdGoal th) of
    ( PremiseG      (iTerm, premIdxTerm) faTerm
     ,PremiseG pPat@(iPat,  _          ) faPat  ) ->
        case doMatch (faTerm `matchFact` faPat <> iTerm `matchLVar` iPat) of
            []      -> Nothing
            subst:_ ->
                let refine = do
                        modM sEdges (substNodePrem pPat (iPat, premIdxTerm))
                        refineSubst subst
                in Just $ snd $ refineCaseDistinction ctxt refine (set cdGoal goalTerm th)

    (ActionG iTerm faTerm, ActionG iPat faPat) ->
        case doMatch (faTerm `matchFact` faPat <> iTerm `matchLVar` iPat) of
            []      -> Nothing
            subst:_ -> Just $ snd $ refineCaseDistinction ctxt
                                        (refineSubst subst) (set cdGoal goalTerm th)

    -- No other matches possible, as we only precompute case distinctions for
    -- premises and KU-actions.
    _ -> Nothing
  where
    -- this code reflects the precomputed cases in 'precomputeCaseDistinctions'
    maybeMatcher (PremiseG _ faTerm, PremiseG _ faPat)  = factTag faTerm == factTag faPat
    maybeMatcher ( ActionG _ (Fact KUFact [tTerm])
                 , ActionG _ (Fact KUFact [tPat]))      =
        case (viewTerm tPat, viewTerm tTerm) of
            (Lit  (Var v),_) | lvarSort v == LSortFresh -> sortOfLNTerm tPat == LSortFresh
            (FApp o _, FApp o' _)                       -> o == o'
            _                                           -> True
    maybeMatcher _                                      = False

    th = (`evalFresh` avoid goalTerm) . rename $ th0

    substNodePrem from to = S.map
        (\ e@(Edge c p) -> if p == from then Edge c to else e)

    doMatch match = runReader (solveMatchLNTerm match) (get pcMaudeHandle ctxt)

    refineSubst subst = do
        void (solveSubstEqs SplitNow subst)
        void substSystem
        return ((), [])

-- | Try to solve a premise goal or 'KU' action using the first precomputed
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
applyCaseDistinction ctxt th0 goal = case matchToGoal ctxt th0 goal of
    Just th -> Just $ do
        markGoalAsSolved "precomputed" goal
        (names, sysTh0) <- disjunctionOfList $ getDisj $ get cdCases th
        sysTh <- (`evalBindT` keepVarBindings) . someInst $ sysTh0
        conjoinSystem sysTh
        return names
    Nothing -> Nothing
  where
    keepVarBindings = M.fromList (map (\v -> (v, v)) (frees goal))

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
      [ return $ varTerm (LVar "t" LSortFresh 1)
      , if enableBP msig then return $ fAppC EMap $ nMsgVars (2::Int) else []
      , [ fAppNoEq o $ nMsgVars k
        | o@(_,(k,priv)) <- S.toList . noEqFunSyms  $ msig
        , NoEq o `S.notMember` implicitFunSig, k > 0 || priv==Private]
      ]

    msig = mhMaudeSig . get pcMaudeHandle $ ctxt

-- | Refine a set of case distinction by exploiting additional typing
-- assumptions.
refineWithTypingAsms
    :: [LNGuarded]        -- ^ Typing assumptions to use.
    -> ProofContext       -- ^ Proof context to use.
    -> [CaseDistinction]  -- ^ Original, untyped case distinctions.
    -> [CaseDistinction]  -- ^ Refined, typed case distinctions.
refineWithTypingAsms [] _ cases0 =
    fmap ((modify cdCases . fmap . second) (set sCaseDistKind TypedCaseDist)) $ cases0
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



