{-# LANGUAGE DeriveDataTypeable, TupleSections, TypeOperators,
             TemplateHaskell, TypeSynonymInstances, FlexibleInstances,
             FlexibleContexts, GeneralizedNewtypeDeriving, ViewPatterns
  #-}
-- |
-- Copyright   : (c) 2011,2012 Simon Meier
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

import qualified Data.Set         as S
import           Data.Foldable (asum)

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
-- import           Control.Monad.Bind
import           Control.Monad.Reader
import           Control.Monad.State (gets)
import           Control.Parallel.Strategies

import           Text.PrettyPrint.Highlight

import           Extension.Prelude
import           Extension.Data.Label

import           Theory.Rule
import           Theory.Proof.Sequent


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
                       -> LNFact -> CaseDistinction
initialCaseDistinction ctxt typAsms goalFa =
    CaseDistinction goalFa cases
  where
    polish (((name, prem), se), _) = ([name], (prem, se))
    se0   = set sFormulas (S.fromList typAsms) (emptySequent UntypedCaseDist)
    cases = fmap polish $ runSeProof instantiate ctxt se0 (avoid (goalFa, se0))
    instantiate = do
        i <- freshLVar "i" LSortNode
        let p   = (i, PremIdx 0)
            err = error . ("requiresCasesThm: no or too many edges: " ++)
        name <- solveGoal (PremiseG p goalFa False)
        edges <- getM sEdges
        case filter ((p ==) . eTgt) (S.toList edges) of
          [e] -> do modM sEdges (S.delete e)
                    return (name, eSrc e)
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
solveAllSafeGoals :: [CaseDistinction] -> SeProof [String]
solveAllSafeGoals ths = 
    solve []
  where
    safeGoal _            (ChainG _)              = True
    safeGoal _            (PremDnKG _)            = True
    safeGoal _            (ActionG _ _)           = True
    safeGoal splitAllowed (DisjG _)               = splitAllowed
    -- NOTE: Uncomment the line below to get more extensive case splitting
    -- for precomputed case distinctions.
    -- safeGoal splitAllowed (SplitG _ _) = splitAllowed
    safeGoal _            (PremiseG _ fa mayLoop) = not (mayLoop || isKFact fa)
    safeGoal _            _                       = False

    nonLoopingGoal (PremiseG _ _ mayLoop) = not mayLoop
    nonLoopingGoal _                      = True

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


------------------------------------------------------------------------------
-- Applying precomputed case distinctions
------------------------------------------------------------------------------

-- | A goal for a big step case distinction.
data BigStepGoal = 
       PremiseBigStep NodePrem LNFact Bool
     | MessageBigStep (Either NodeId NodePrem) LNTerm
       -- ^ Left means solving a deduction action, Right a node premise.
     deriving( Eq, Ord, Show )

-- | Convert a standard goal to a big-step goal.
toBigStepGoal :: Goal -> Maybe BigStepGoal
toBigStepGoal goal = case goal of
    PremiseG p fa mayLoop             -> return $ PremiseBigStep p fa mayLoop
    PremUpKG p m                      -> return $ MessageBigStep (Right p) m
    ActionG i (dedFactView -> Just m) -> return $ MessageBigStep (Left i)  m
    _                                 -> mzero

fromBigStepGoal :: BigStepGoal -> Goal
fromBigStepGoal goal = case goal of
    PremiseBigStep p fa mayLoop -> PremiseG p fa mayLoop
    MessageBigStep (Left i)  m  -> ActionG i (dedLogFact m)
    MessageBigStep (Right p) m  -> PremUpKG p m


-- | AC-Matching for big-step goals. MessageBigSteps can be matched
-- to the corresponding K-up facts.
matchBigStepGoal :: BigStepGoal -- ^ Term.
                 -> LNFact      -- ^ Pattern.
                 -> WithMaude [LNSubst]
matchBigStepGoal (PremiseBigStep _ faTerm _) faPat = matchLNFact faTerm faPat
matchBigStepGoal (MessageBigStep _ mTerm)    faPat =
    case kFactView faPat of
      Just (UpK, _, mPat) -> matchLNTerm [mTerm `MatchWith` mPat]
      _                   -> return []

-- | Try to solve a premise goal or 'Ded' action using the first precomputed
-- case distinction with a matching premise.
solveWithCaseDistinction :: MaudeHandle
                         -> [CaseDistinction] 
                         -> Goal
                         -> Maybe (SeProof [String])
solveWithCaseDistinction hnd ths goal0 = do
    goal <- toBigStepGoal goal0
    asum [ applyCaseDistinction hnd th goal | th <- ths ]

-- | Apply a precomputed case distinction theorem to a required fact.
applyCaseDistinction :: MaudeHandle
                     -> CaseDistinction    -- ^ Case distinction theorem.
                     -> BigStepGoal        -- ^ Required goal
                     -> Maybe (SeProof [String])
applyCaseDistinction hnd th goal =
    case (`runReader` hnd) $ matchBigStepGoal goal (get cdGoal th) of
      [] -> Nothing
      _  -> Just $ do (names, subst, seTh) <- instTheorem
                      solveSubstEqs SplitNow subst
                      conjoinSequent seTh
                      return names
  where
    instTheorem :: SeProof ([String], LNSubst, Sequent)
    instTheorem = do
        instTh <- rename th
        -- We only have to choose one matcher, as the theorem holds for all
        -- premises equal modulo AC.
        subst <- disjunctionOfList $ take 1 $ 
                 matchBigStepGoal goal (get cdGoal instTh) `runReader` hnd
        (names, (concTh, seTh)) <- disjunctionOfList $ getDisj $ get cdCases instTh

        seTh' <- case goal of
            PremiseBigStep prem _ _ -> 
                return $ modify sEdges (S.insert (Edge concTh prem)) seTh
            MessageBigStep (Right prem) _ -> 
                return $ modify sMsgEdges (S.insert (MsgEdge concTh prem)) seTh
            MessageBigStep (Left i) m -> do
                -- remove solved atom
                modM sAtoms (S.delete (Action (varTerm i) (dedLogFact m)))
                return seTh

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
    go ths =
        if any or (changes `using` parList rdeepseq)
          then go ths'
          else ths'
      where
        (changes, ths') = unzip $ map (refineCaseDistinction ctxt solver) ths
        noSplitThs = filter ((<= 1) . length . getDisj . get cdCases) ths
        solver     = do names <- solveAllSafeGoals noSplitThs
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

    nMsgVars n = [ varTerm (LVar "t" LSortMsg i) | i <- [1..fromIntegral n] ]

    someProtoGoal :: (FactTag, Int) -> LNFact
    someProtoGoal (tag, arity) = Fact tag (nMsgVars arity)

    someKUGoal :: LNTerm -> LNFact
    someKUGoal m = Fact KUFact [varTerm (LVar "f_" LSortMsg 0), m]

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

------------------------------------------------------------------------------
-- Pretty-printing
------------------------------------------------------------------------------

prettyBigStepGoal :: HighlightDocument d => BigStepGoal -> d
prettyBigStepGoal = prettyGoal . fromBigStepGoal


