-- |
-- Copyright   : (c) 2011,2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Big-step proofs computing possible sources of a fact.
module Theory.Constraint.Solver.Sources (
  -- * Precomputed case distinctions

  -- ** Queries
    unsolvedChainConstraints

  -- ** Construction
  , precomputeSources
  , refineWithSourceAsms

  -- ** Application
  , solveWithSource

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

-- uncomment for use of "EXTENSIVE_SPLIT" only
-- import           System.IO.Error
-- import           System.Environment
-- import           System.IO.Unsafe

import           Text.PrettyPrint.Highlight

import           Extension.Data.Label
import           Extension.Prelude

import           Theory.Constraint.Solver.Contradictions (contradictorySystem)
import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.Solver.Simplify
-- import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model

import           Control.Monad.Bind

import           Debug.Trace

------------------------------------------------------------------------------
-- Precomputing case distinctions
------------------------------------------------------------------------------

-- | The number of remaining chain constraints of each case.
unsolvedChainConstraints :: Source -> [Int]
unsolvedChainConstraints =
    map (length . unsolvedChains . snd) . getDisj . get cdCases


-- Construction
---------------

-- | The initial source if the given goal is required and the
-- given source assumptions are justified.
initialSource
    :: ProofContext
    -> [LNGuarded] -- ^ Restrictions.
    -> Goal
    -> Source
initialSource ctxt restrictions goal =
    Source goal cases
  where
    polish ((name, se), _) = ([name], se)
    se0   = insertLemmas restrictions $ emptySystem RawSource $ get pcDiffContext ctxt
    cases = fmap polish $
        runReduction instantiate ctxt se0 (avoid (goal, se0))
    instantiate = do
        insertGoal goal False
        solveGoal goal

-- | Refine a source by applying the additional proof step.
refineSource
    :: ProofContext
    -> Reduction (a, [String])  -- proof step with result and path extension
    -> Source
    -> ([a], Source)
refineSource ctxt proofStep th =
    ( map fst $ getDisj refinement
    , set cdCases newCases th )
  where
    newCases =   Disj . removeRedundantCases ctxt stableVars snd
               . map (second (modify sSubst (restrict stableVars)))
               . getDisj $ snd <$> refinement

    stableVars = frees (get cdGoal th)

    fs         = avoid th
    refinement = do
        (names, se)        <- get cdCases th
        ((x, names'), se') <- fst <$> runReduction proofStep ctxt se fs
        return (x, (combine names names', se'))

    -- Combine names such that the coerce rule is blended out.
    combine []            ns' = ns'
    combine ("coerce":ns) ns' = combine ns ns'
    combine (n       :_)  _   = [n]

-- | Solves all chain and splitting goals as well as all premise goals solvable
-- with one of the given precomputed requires source theorems, while
-- repeatedly simplifying the proof state.
--
-- Returns the names of the steps applied.
solveAllSafeGoals :: [Source] -> Reduction [String]
solveAllSafeGoals ths' =
    solve ths' [] Nothing 10
  where
--    extensiveSplitting = unsafePerformIO $
--      (getEnv "TAMARIN_EXTENSIVE_SPLIT" >> return True) `catchIOError` \_ -> return False
    safeGoal _       _          (_,   (_, LoopBreaker)) = False
    safeGoal doSplit chainsLeft (goal, _              ) =
      case goal of
        ChainG _ _    -> if (chainsLeft > 0) 
                            then True 
                            else (trace "Stopping precomputation, too many chain goals." False)
        ActionG _ fa  -> not (isKUFact fa)
        PremiseG _ fa -> not (isKUFact fa)
        DisjG _       -> doSplit
        -- Uncomment to get more extensive case splitting
        SplitG _      -> doSplit --extensiveSplitting &&
        -- SplitG _      -> False

    usefulGoal (_, (_, Useful)) = True
    usefulGoal _                = False

    isKDPrem (PremiseG _ fa,_) = isKDFact fa
    isKDPrem _                 = False
    isChainPrem1 (ChainG _ (_,PremIdx 1),_) = True
    isChainPrem1 _                          = False

    solve :: [Source] -> [String] -> Maybe LNTerm -> Integer -> Reduction [String]
    solve ths caseNames lastChainTerm chainsLeft = do
        simplifySystem
        ctxt <- ask
        contradictoryIf =<< (gets (contradictorySystem ctxt))
        goals  <- gets openGoals
        chains <- gets unsolvedChains
        -- Filter out chain goals where the term in the conclusion is identical to one we just solved,
        -- as this indicates our chain can loop
        filteredGoals <- filterM  (\(g,_) -> case g of
            (ChainG c _) -> (\x -> return $ Just True /= liftM2 eqModuloFreshnessNoAC lastChainTerm x) =<< kConcTerm c
            _            -> return True) goals

        -- try to either solve a safe goal or use one of the precomputed case
        -- distinctions
        let noChainGoals = null [ () | (ChainG _ _, _) <- goals ]
            -- we perform equation splits, if there is a chain goal starting
            -- from a message variable; i.e., a chain constraint that is no
            -- open goal.
            splitAllowed    = noChainGoals && not (null chains)
            safeGoals       = fst <$> filter (safeGoal splitAllowed chainsLeft) filteredGoals
            remainingChains ((ChainG _ _):_) = chainsLeft-1
            remainingChains _                = chainsLeft
            kdPremGoals     = fst <$> filter (\g -> isKDPrem g || isChainPrem1 g) goals
            usefulGoals     = fst <$> filter usefulGoal goals
            nextStep :: Maybe (Reduction [String], Maybe Source)
            nextStep     =
                ((\x -> (fmap return (solveGoal x), Nothing)) <$> headMay (kdPremGoals)) <|>
                ((\x -> (fmap return (solveGoal x), Nothing)) <$> headMay (safeGoals)) <|>
                (asum $ map (solveWithSourceAndReturn ctxt ths) usefulGoals)

        -- Update the last chain conclusion term if next step is a 'safe' chain goal (kdPremGoals is empty)
        lastChainTerm' <- case (kdPremGoals, safeGoals) of
            ([], ((ChainG c _):_)) -> (\t -> return $ t <|> lastChainTerm) =<< kConcTerm c
            _                      -> return lastChainTerm

        case nextStep of
          Nothing   -> return caseNames
          Just (step, Nothing) -> (\x -> solve ths (caseNames ++ x) lastChainTerm' (remainingChains safeGoals)) =<< step
          Just (step, Just usedCase) -> (\x -> solve (filterCases usedCase ths) (caseNames ++ x) lastChainTerm' (remainingChains safeGoals)) =<< step

    filterCases :: Source -> [Source] -> [Source]
    filterCases usedCase cds = filter (\x -> usedCase /= x) cds

    kConcTerm :: NodeConc -> Reduction (Maybe LNTerm)
    kConcTerm c = do
        faConc <- gets $ nodeConcFact c
        case kFactView faConc of
            Just (_,t) -> return $ Just t
            _          -> return Nothing


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

-- | Match a precomputed 'Source' to a goal. Returns the instantiated
-- 'Source' with the given goal if possible
matchToGoal
    :: ProofContext     -- ^ Proof context used for refining the source.
    -> Source           -- ^ Source to use.
    -> Goal             -- ^ Goal to match
    -> Maybe Source
    -- ^ An adapted version of the source with the given goal
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
                in Just $ snd $ refineSource ctxt refine (set cdGoal goalTerm th)

    (ActionG iTerm faTerm, ActionG iPat faPat) ->
        case doMatch (faTerm `matchFact` faPat <> iTerm `matchLVar` iPat) of
            []      -> Nothing
            subst:_ -> Just $ snd $ refineSource ctxt
                                        (refineSubst subst) (set cdGoal goalTerm th)

    -- No other matches possible, as we only precompute case distinctions for
    -- premises and KU-actions.
    _ -> Nothing
  where
    -- this code reflects the precomputed cases in 'precomputeSources'
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
-- case distinction with a matching premise. Also returns the used case distinction.
solveWithSourceAndReturn :: ProofContext
                         -> [Source]
                         -> Goal
                         -> Maybe (Reduction [String], Maybe Source)
solveWithSourceAndReturn hnd ths goal = do
    -- goal <- toBigStepGoal goal0
    asum [ applySource hnd th goal | th <- ths ]

-- | Try to solve a premise goal or 'KU' action using the first precomputed
-- source with a matching premise.
solveWithSource :: ProofContext
                -> [Source]
                -> Goal
                -> Maybe (Reduction [String])
solveWithSource hnd ths goal =
    case (solveWithSourceAndReturn hnd ths goal) of
         Nothing     -> Nothing
         Just (x, _) -> Just x


-- | Apply a precomputed source theorem to a required fact.
applySource :: ProofContext
               -> Source     -- ^ Source theorem.
               -> Goal       -- ^ Required goal
               -> Maybe (Reduction [String], Maybe Source)
applySource ctxt th0 goal = case matchToGoal ctxt th0 goal of
    Just th -> Just ((do
        markGoalAsSolved "precomputed" goal
        (names, sysTh0) <- disjunctionOfList $ getDisj $ get cdCases th
        sysTh <- (`evalBindT` keepVarBindings) . someInst $ sysTh0
        conjoinSystem sysTh
        return names), Just th0)
    Nothing -> Nothing
  where
    keepVarBindings = M.fromList (map (\v -> (v, v)) (frees goal))

-- | Saturate the sources with respect to each other such that no
-- additional splitting is introduced; i.e., only rules with a single or no
-- conclusion are used for the saturation.
saturateSources
    :: ProofContext -> [Source] -> [Source]
saturateSources ctxt thsInit =
    (go thsInit 1)
  where
    go :: [Source] -> Integer -> [Source]
    go ths n =
        if (any or (changes `using` parList rdeepseq)) && (n <= 5)
          then go ths' (n + 1)
          else if (n > 5)
            then trace "saturateSources: Saturation aborted, more than 5 iterations." ths'
            else ths'
      where
        (changes, ths') = unzip $ map (refineSource ctxt solver) ths
        goodTh th  = length (getDisj (get cdCases th)) <= 1
        solver     = do names <- solveAllSafeGoals (filter goodTh ths)
                        return (not $ null names, names)

-- | Precompute a saturated set of case distinctions.
precomputeSources
    :: ProofContext
    -> [LNGuarded]       -- ^ Restrictions.
    -> [Source]
precomputeSources ctxt restrictions =
    map cleanupCaseNames (saturateSources ctxt rawSources)
  where
    cleanupCaseNames = modify cdCases $ fmap $ first $
        filter (not . null)
      . map (filter (`elem` '_' : ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']))

    rawSources =
        (initialSource ctxt restrictions <$> (protoGoals ++ msgGoals))

    -- construct source starting from facts from non-special rules
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

-- | Refine a set of sources by exploiting additional source
-- assumptions.
refineWithSourceAsms
    :: [LNGuarded]    -- ^ Source assumptions to use.
    -> ProofContext   -- ^ Proof context to use.
    -> [Source]       -- ^ Original, raw sources.
    -> [Source]       -- ^ Manipulated, refined sources.
refineWithSourceAsms [] _ cases0 =
    fmap ((modify cdCases . fmap . second) (set sSourceKind RefinedSource)) $ cases0
refineWithSourceAsms assumptions ctxt cases0 =
    fmap (modifySystems removeFormulas) $
    saturateSources ctxt $
    modifySystems updateSystem <$> cases0
  where
    modifySystems   = modify cdCases . fmap . second
    updateSystem se =
        modify sFormulas (S.union (S.fromList assumptions)) $
        set sSourceKind RefinedSource                       $ se
    removeFormulas =
        modify sGoals (M.filterWithKey isNoDisjGoal)
      . set sFormulas S.empty
      . set sSolvedFormulas S.empty

    isNoDisjGoal (DisjG _)  _ = False
    isNoDisjGoal _          _ = True



