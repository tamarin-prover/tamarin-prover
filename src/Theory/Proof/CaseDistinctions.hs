{-# LANGUAGE DeriveDataTypeable, TupleSections, TypeOperators #-}
{-# LANGUAGE TemplateHaskell, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Big-step proofs using case distinctions on the possible sources of a fact.
module Theory.Proof.CaseDistinctions (
  -- * Big-step case distinctions
  -- | Types declared in "Theory.Proof.Types"

  -- ** Queries
    unsolvedChainConstraints

  -- ** Construction
  , precomputeCaseDistinctions
  , refineWithTypingAsms

  -- ** Application
  , solveWithCaseDistinction 

  -- ** Pretty-printing
  , prettyBigStepGoal

  -- * Convenience export of used modules
  , module Theory.Proof.Sequent
  ) where

import           Safe
import           Prelude hiding ( (.), id )
import           Debug.Trace

import qualified Data.Set         as S
import qualified Data.DAG.Simple  as D
import           Data.Foldable (asum)

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.Bind
import           Control.Monad.Reader
import           Control.Monad.State (gets)
import           Control.Parallel.Strategies

import           Text.Isar

import           Extension.Prelude
import           Extension.Data.Label

import           Theory.Rule
import           Theory.Proof.Sequent


-- | AC-Matching for big-step goals. MessageBigSteps can be matched
-- to the corresponding K-up facts.
matchBigStepGoal :: BigStepGoal -- ^ Term.
                 -> BigStepGoal -- ^ Pattern.
                 -> WithMaude [LNSubst]
matchBigStepGoal (PremiseBigStep faTerm) (PremiseBigStep faPat) =
    matchLNFact faTerm faPat
matchBigStepGoal (MessageBigStep mTerm) (MessageBigStep mPat) =
    matchLNTerm [mTerm `MatchWith` mPat]
matchBigStepGoal (MessageBigStep mTerm) (PremiseBigStep faPat) =
    case kFactView faPat of
      Just (UpK, _, mPat) -> matchLNTerm [mTerm `MatchWith` mPat]
      _                   -> return []
matchBigStepGoal _ _ = return []


------------------------------------------------------------------------------
-- Big Step Proofs
------------------------------------------------------------------------------

-- | The number of remaining chain constraints of each case.
unsolvedChainConstraints :: CaseDistinction -> [Int]
unsolvedChainConstraints =
    map (S.size . get sChains . snd . snd) . getDisj . get cdCases


-- Construction
---------------

-- | The initial case distinction if the given goal is required and the
-- given typing assumptions are justified.
initialCaseDistinction :: ProofContext 
                       -> [LNGuarded] -- ^ Typing assumptions.
                       -> BigStepGoal -> CaseDistinction
initialCaseDistinction ctxt typAsms goal =
    CaseDistinction goal cases
  where
    polish (((name, prem), se), _) = ([name], (prem, se))
    se0   = set sFormulas (S.fromList typAsms) (emptySequent UntypedCaseDist)
    cases = fmap polish $ runSeProof instantiate ctxt se0 (avoid (goal, se0))
    instantiate = do
        i <- freshLVar "i" LSortNode
        let p   = NodePrem (i, 0)
            err = error . ("requiresCasesThm: no or too many edges: " ++)
        case goal of
            PremiseBigStep fa -> do
                name <- solveGoal (PremiseG p fa)
                edges <- getM sEdges
                case filter ((p ==) . eTgt) (S.toList edges) of
                  [e] -> do modM sEdges (S.delete e)
                            return (name, eSrc e)
                  es  -> err $ show es

            -- FIXME: Probably this code is not required.
            MessageBigStep m  -> do
                name <- solveGoal (PremUpKG p m)
                edges <- getM sMsgEdges
                case filter ((p ==) . meTgt) (S.toList edges) of
                  [e] -> do modM sMsgEdges (S.delete e)
                            return (name, meSrc e)
                  es  -> err $ show es


-- | Refine a source case distinction by applying the additional proof step.
refineCaseDistinction 
    :: ProofContext
    -> SeProof (a, [String])  -- proof step with result and path extension
    -> CaseDistinction 
    -> ([a],CaseDistinction)
refineCaseDistinction ctxt proofStep th = 
    ( map fst $ getDisj refinement
    , set cdCases (snd <$> refinement) th )
  where
    fs         = avoid th
    refinement = do
        (names, (p, se))   <- get cdCases th
        ((x, names'), se') <- fst <$> runSeProof proofStep ctxt se fs
        return (x, (combine names names', (p, se')))

    -- Combine names such that the coerce rule is blended out.
    combine []            ns' = ns'
    combine ("coerce":ns) ns' = combine ns ns'
    combine (n       :_)  _   = [n]

-- | Solves all chain and splitting goals as well as all premise goals solvable
-- with one of the given precomputed requires case distinction theorems, while
-- repeatedly simplifying the proof state. 
--
-- Returns the names of the steps applied.
solveAllSafeGoals 
    :: (LNFact -> Bool) -- ^ True, if this fact may be refined further.
                        -- Required for loop-breaking.
    -> [CaseDistinction] 
    -> SeProof [String]
solveAllSafeGoals nonLoopingFact ths = 
    solve []
  where
    safeGoal _            (ChainG _)      = True
    safeGoal _            (PremDnKG _)    = True
    safeGoal _            (ActionG _ _)   = True
    safeGoal splitAllowed (DisjG _)       = splitAllowed
    -- NOTE: Uncomment the line below to get more extensive case splitting
    -- for precomputed case distinctions.
    -- safeGoal splitAllowed (SplitG _ _) = splitAllowed
    safeGoal _            (PremiseG _ fa) = nonLoopingFact fa
    safeGoal _            _               = False

    nonLoopingGoal (PremiseG _ fa) = nonLoopingFact fa
    nonLoopingGoal _               = True

    solve caseNames = do
        simplifySequent
        sig <- askM pcSignature
        contradictoryIf =<< gets (contradictorySequent sig)
        goals  <- gets openGoals
        chains <- getM sChains
        hnd    <- getMaudeHandle
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
                (asum $ map (solveWithCaseDistinction hnd ths) nonLoopingGoals)
        case nextStep of
          Nothing   -> return $ caseNames
          Just step -> solve . (caseNames ++) =<< step

-- | Try to solve a premise goal using the first precomputed case distinction
-- with a matching premise.
solveWithCaseDistinction :: MaudeHandle
                         -> [CaseDistinction] 
                         -> Goal
                         -> Maybe (SeProof [String])
solveWithCaseDistinction hnd ths goal0 = case goal0 of 
    PremiseG p fa -> applyTo p (PremiseBigStep fa)
    PremUpKG p m  -> applyTo p (MessageBigStep m)
    _             -> mzero
  where
    applyTo p goal = asum [ applyCaseDistinction hnd th p goal | th <- ths ]

-- | Apply a precomputed case distinction theorem to a required fact.
applyCaseDistinction :: MaudeHandle
                     -> CaseDistinction   -- ^ Case distinction theorem.
                     -> NodePrem           -- ^ Premise
                     -> BigStepGoal        -- ^ Required goal
                     -> Maybe (SeProof [String])
applyCaseDistinction hnd th prem goal =
    case (`runReader` hnd) $ matchBigStepGoal goal (get cdGoal th) of
      [] -> Nothing
      _  -> Just $ do (names, subst, seTh) <- instTheorem `evalBindT` noBindings
                      solveSubstEqs SplitNow subst
                      conjoinSequent seTh
                      return names
  where
    instTheorem :: BindT LVar LVar SeProof ([String], LNSubst, Sequent)
    instTheorem = do
        goalTh <- someInst $ get cdGoal th
        -- We only have to choose one matcher, as the theorem holds for all
        -- premises equal modulo AC.
        subst <- disjunctionOfList $ take 1 $ 
                 matchBigStepGoal goal goalTh `runReader` hnd
        (names, (concTh, seTh)) <- someInst =<< 
            (disjunctionOfList $ getDisj $ get cdCases th)

        let seTh' = case goal of
              PremiseBigStep _ -> 
                  modify sEdges (S.insert (Edge concTh prem)) seTh
              MessageBigStep _ -> 
                  modify sMsgEdges (S.insert (MsgEdge concTh prem)) seTh

        -- solving the matcher equalities and 
        -- conjoining the sequent will be done later
        return (names, subst, seTh')

-- | Saturate the case distinctions with respect to each other such that no
-- additional splitting is introduced; i.e., only rules with a single or no
-- conclusion are used for the saturation.
saturateCaseDistinctions 
    :: ProofContext -> [CaseDistinction] -> [CaseDistinction]
saturateCaseDistinctions ctxt = 
    go
  where
    nonLoopingFact = saturationLoopBreakers ctxt

    go ths =
        if any or (changes `using` parList rdeepseq)
          then go ths'
          else ths'
      where
        (changes, ths') = unzip $ map (refineCaseDistinction ctxt solver) ths
        noSplitThs = filter ((<= 1) . length . getDisj . get cdCases) ths
        solver     = do names <- solveAllSafeGoals nonLoopingFact noSplitThs
                        return (not $ null names, names)

{-
    go changed done []
      | changed   = go False [] (reverse done)
      | otherwise = reverse done
    go changed done (th:ths) =
        go (changed || or changes ) (th':done) ths
      where
        solver         = do names <- solveAllSafeGoals nonLoopingFact noSplitThs
                            return (not $ null names, names)
        (changes, th') = refineCaseDistinction ctxt solver th
        noSplitThs     = 
            filter ((<= 1) . length . getDisj . get cdCases) (done ++ ths)
-}

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

    nMsgVars n = [ varTerm (LVar "t" LSortMsg i) | i <- [1..n] ]

    someProtoGoal :: (FactTag, Int) -> BigStepGoal
    someProtoGoal (tag, arity) = PremiseBigStep $ Fact tag (nMsgVars arity)

    someKUGoal :: LNTerm -> BigStepGoal
    someKUGoal m = PremiseBigStep (Fact KUFact [varTerm (LVar "f_" LSortMsg 0), m])

    -- FIXME: Also use facts from proof context.
    rules = get pcRules ctxt
    absProtoFacts = sortednub $ do
        ru <- joinNonSpecialRules rules
        fa <- absFact <$> (getProtoFact =<< (get rConcs ru ++ get rPrems ru))
        -- exclude facts handled specially by the prover
        guard (not $ fst fa `elem` [OutFact, InFact, FreshFact])
        return fa

    absMsgFacts :: [LNTerm]
    absMsgFacts = asum $ sortednub $ 
      [ do return $ Lit $ Var (LVar "t" LSortFresh 1)

      , [ FApp (NonAC (s,k)) $ nMsgVars k
        | (s,k) <- funSigForMaudeSig  . mhMaudeSig . sigmMaudeHandle . get pcSignature $ ctxt
        ,  s `notElem` [ "inv", "pair" ] ]
      ] 

-- | Refine a set of case distinction by exploiting additional typing
-- assumptions.
refineWithTypingAsms 
    :: [LNGuarded]        -- ^ Typing assumptions to use.
    -> ProofContext       -- ^ Proof context to use.
    -> [CaseDistinction]  -- ^ Original, untyped case distinctions.
    -> [CaseDistinction]  -- ^ Refined, typed case distinctions.
refineWithTypingAsms typAsms ctxt cases0 =
    fmap (modifySequents removeFormulas) $
    saturateCaseDistinctions ctxt $ 
    modifySequents updateSequent <$> cases0
  where
    modifySequents = modify cdCases . fmap . second . second
    updateSequent se = 
        modify sFormulas (S.union (S.fromList typAsms)) $
        set sCaseDistKind TypedCaseDist                 $ se
    removeFormulas = set sFormulas S.empty . set sSolvedFormulas S.empty

-- Loop-breaker computation
---------------------------

-- | Compute the loop-breakers for saturating the pre-computated case
-- distinctions.
saturationLoopBreakers :: ProofContext -> (LNFact -> Bool)
saturationLoopBreakers ctxt =
    trace (" loop breakers: " ++ show (loopBreakers absProtoFactRel)) $
      \fa -> absFact fa `S.notMember` loopBreakers absProtoFactRel
  where
    rules = get pcRules ctxt
    -- detect cycles on abstracted protocol facts; i.e.,  (tag, arity) facts
    absFact (Fact tag ts) = (tag, length ts)

    absProtoFactRel = sortednub $ do
        ru <- joinNonSpecialRules rules
        conc <- absFact <$> get rConcs ru
        prem <- absFact <$> get rPrems ru
        return (conc, prem)


-- | Given a relation compute a set of loop-breakers; i.e., a feedback vertex
-- set (<http://en.wikipedia.org/wiki/Feedback_vertex_set>). No guarantee for
-- minimality is made. The current algorithm only removes self-loops and hopes
-- that this is sufficient. We should implement something along the lines of
-- Ann Becker, Dan Geiger, Optimization of Pearl's method of conditioning and
-- greedy-like approximation algorithms for the vertex feedback set problem,
-- Artificial Intelligence, Volume 83, Issue 1, May 1996, Pages 167-188, ISSN
-- 0004-3702, 10.1016/0004-3702(95)00004-6.
-- <http://www.sciencedirect.com/science/article/pii/0004370295000046>.
loopBreakers :: Ord a => [(a,a)] -> S.Set a
loopBreakers rel
  | D.cyclic rel' = 
       error "loopBreakers: trivial loop-breaker computation failed.\
             \The relation is still cyclic."
  | otherwise = breakers
  where
    breakers = S.fromList [ x | (x, y) <- rel, x == y ]
    rel'     = [ r | r@(x, y) <- rel
                   , x `S.notMember` breakers, y `S.notMember` breakers]

------------------------------------------------------------------------------
-- Pretty-printing
------------------------------------------------------------------------------

prettyBigStepGoal :: Document d => BigStepGoal -> d
prettyBigStepGoal (PremiseBigStep fa) = prettyLNFact fa
prettyBigStepGoal (MessageBigStep m)  = prettyLNTerm m
