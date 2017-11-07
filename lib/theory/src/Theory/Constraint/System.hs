{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- This is the public interface for constructing and deconstructing constraint
-- systems. The interface for performing constraint solving provided by
-- "Theory.Constraint.Solver".
module Theory.Constraint.System (
  -- * Constraints
    module Theory.Constraint.System.Constraints

  -- * Proof contexts
  -- | The proof context captures all relevant information about the context
  -- in which we are using the constraint solver. These are things like the
  -- signature of the message theory, the multiset rewriting rules of the
  -- protocol, the available precomputed sources, whether induction should be
  -- applied or not, whether raw or refined sources are used, and whether we
  -- are looking for the existence of a trace or proving the absence of any
  -- trace satisfying the constraint system.
  , ProofContext(..)
  , DiffProofContext(..)
  , InductionHint(..)

  , pcSignature
  , pcRules
  , pcInjectiveFactInsts
  , pcSources
  , pcSourceKind
  , pcUseInduction
  , pcTraceQuantifier
  , pcLemmaName
  , pcHiddenLemmas
  , pcMaudeHandle
  , pcDiffContext
  , pcTrueSubterm
  , pcConstantRHS
  , dpcPCLeft
  , dpcPCRight
  , dpcProtoRules
  , dpcDestrRules
  , dpcConstrRules
  , dpcRestrictions
  , eitherProofContext

  -- ** Classified rules
  , ClassifiedRules(..)
  , emptyClassifiedRules
  , crConstruct
  , crDestruct
  , crProtocol
  , joinAllRules
  , nonSilentRules

  -- ** Precomputed case distinctions
  -- | For better speed, we precompute case distinctions. This is especially
  -- important for getting rid of all chain constraints before actually
  -- starting to verify security properties.
  , Source(..)

  , cdGoal
  , cdCases
  
  , Side(..)
  , opposite
    
  -- * Constraint systems
  , System
  , DiffProofType(..)
  , DiffSystem

  -- ** Construction
  , emptySystem
  , emptyDiffSystem

  , SystemTraceQuantifier(..)
  , formulaToSystem
  
  -- ** Diff proof system
  , dsProofType
  , dsProtoRules
  , dsConstrRules
  , dsDestrRules
  , dsCurrentRule
  , dsSide
  , dsSystem
  , dsProofContext

  -- ** Node constraints
  , sNodes
  , allKDConcs

  , nodeRule
  , nodeRuleSafe
  , nodeConcNode
  , nodePremNode
  , nodePremFact
  , nodeConcFact
  , resolveNodePremFact
  , resolveNodeConcFact

  -- ** Actions
  , allActions
  , allKUActions
  , unsolvedActionAtoms
  -- FIXME: The two functions below should also be prefixed with 'unsolved'
  , kuActionAtoms
  , standardActionAtoms

  -- ** Edge and chain constraints
  , sEdges
  , unsolvedChains

  , isCorrectDG
  , getMirrorDG
  , getMirrorDGandEvaluateRestrictions
  , doRestrictionsHold
  , filterRestrictions
  
  , checkIndependence
  
  , unsolvedPremises
  , unsolvedTrivialGoals
  , allFormulasAreSolved
  , dgIsNotEmpty
  , allOpenFactGoalsAreIndependent
  , allOpenGoalsAreSimpleFacts
  
  -- ** Temporal ordering
  , sLessAtoms

  , rawLessRel
  , rawEdgeRel

  , alwaysBefore
  , isInTrace

  -- ** The last node
  , sLastAtom
  , isLast

  -- ** Equations
  , module Theory.Tools.EquationStore
  , sEqStore
  , sSubst
  , sConjDisjEqs

  -- ** Formulas
  , sFormulas
  , sSolvedFormulas

  -- ** Lemmas
  , sLemmas
  , insertLemmas

  -- ** Keeping track of source assumptions
  , SourceKind(..)
  , sSourceKind

  -- ** Goals
  , GoalStatus(..)
  , gsSolved
  , gsLoopBreaker
  , gsNr

  , sGoals
  , sNextGoalNr
  
  , isDiffSystem
  , sDiffSystem

  -- * Formula simplification
  , impliedFormulas

  -- * Pretty-printing
  , prettySystem
  , prettyNonGraphSystem
  , prettyNonGraphSystemDiff
  , prettySource

  ) where

-- import           Debug.Trace

import           Prelude                              hiding (id, (.))

import           GHC.Generics                         (Generic)

import           Data.Binary
import qualified Data.ByteString.Char8                as BC
import qualified Data.DAG.Simple                      as D
import           Data.List                            (foldl', partition, intersect)
import qualified Data.Map                             as M
import           Data.Maybe                           (fromMaybe)
-- import           Data.Monoid                          (Monoid(..))
import qualified Data.Monoid                             as Mono
import qualified Data.Set                             as S
import           Data.Either                          (partitionEithers)

import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Fresh
import           Control.Monad.Reader

import           Data.Label                           ((:->), mkLabels)
import qualified Extension.Data.Label                 as L

import           Logic.Connectives
import           Theory.Constraint.System.Constraints
import           Theory.Model
import           Theory.Text.Pretty
import           Theory.Tools.EquationStore

----------------------------------------------------------------------
-- ClassifiedRules
----------------------------------------------------------------------

data ClassifiedRules = ClassifiedRules
     { _crProtocol      :: [RuleAC] -- all protocol rules
     , _crDestruct      :: [RuleAC] -- destruction rules
     , _crConstruct     :: [RuleAC] -- construction rules
     }
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''ClassifiedRules])

-- | The empty proof rule set.
emptyClassifiedRules :: ClassifiedRules
emptyClassifiedRules = ClassifiedRules [] [] []

-- | @joinAllRules rules@ computes the union of all rules classified in
-- @rules@.
joinAllRules :: ClassifiedRules -> [RuleAC]
joinAllRules (ClassifiedRules a b c) = a ++ b ++ c

-- | Extract all non-silent rules.
nonSilentRules :: ClassifiedRules -> [RuleAC]
nonSilentRules = filter (not . null . L.get rActs) . joinAllRules

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- | In the diff type, we have either the Left Hand Side or the Right Hand Side
data Side = LHS | RHS deriving ( Show, Eq, Ord, Read, Generic, NFData, Binary )

opposite :: Side -> Side
opposite LHS = RHS
opposite RHS = LHS

-- | Whether we are checking for the existence of a trace satisfiying a the
-- current constraint system or whether we're checking that no traces
-- satisfies the current constraint system.
data SystemTraceQuantifier = ExistsSomeTrace | ExistsNoTrace
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | Source kind that are allowed. The order of the kinds
-- corresponds to the subkinding relation: raw < refined.
data SourceKind = RawSource | RefinedSource
       deriving( Eq, Generic, NFData, Binary )

instance Show SourceKind where
    show RawSource     = "raw"
    show RefinedSource = "refined"

-- Adapted from the output of 'derive'.
instance Read SourceKind where
        readsPrec p0 r
          = readParen (p0 > 10)
              (\ r0 ->
                 [(RawSource, r1) | ("untyped", r1) <- lex r0])
              r
              ++
              readParen (p0 > 10)
                (\ r0 -> [(RefinedSource, r1) | ("typed", r1) <- lex r0])
                r

instance Ord SourceKind where
    compare RawSource     RawSource     = EQ
    compare RawSource     RefinedSource = LT
    compare RefinedSource RawSource     = GT
    compare RefinedSource RefinedSource = EQ

-- | The status of a 'Goal'. Use its 'Semigroup' instance to combine the
-- status info of goals that collapse.
data GoalStatus = GoalStatus
    { _gsSolved :: Bool
       -- True if the goal has been solved already.
    , _gsNr :: Integer
       -- The number of the goal: we use it to track the creation order of
       -- goals.
    , _gsLoopBreaker :: Bool
       -- True if this goal should be solved with care because it may lead to
       -- non-termination.
    }
    deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A constraint system.
data System = System
    { _sNodes          :: M.Map NodeId RuleACInst
    , _sEdges          :: S.Set Edge
    , _sLessAtoms      :: S.Set (NodeId, NodeId)
    , _sLastAtom       :: Maybe NodeId
    , _sEqStore        :: EqStore
    , _sFormulas       :: S.Set LNGuarded
    , _sSolvedFormulas :: S.Set LNGuarded
    , _sLemmas         :: S.Set LNGuarded
    , _sGoals          :: M.Map Goal GoalStatus
    , _sNextGoalNr     :: Integer
    , _sSourceKind     :: SourceKind
    , _sDiffSystem     :: Bool
    }
    -- NOTE: Don't forget to update 'substSystem' in
    -- "Constraint.Solver.Reduction" when adding further fields to the
    -- constraint system.
    deriving( Eq, Ord, Generic, NFData, Binary )

$(mkLabels [''System, ''GoalStatus])

deriving instance Show System

-- Further accessors
--------------------

-- | Label to access the free substitution of the equation store.
sSubst :: System :-> LNSubst
sSubst = eqsSubst . sEqStore

-- | Label to access the conjunction of disjunctions of fresh substutitution in
-- the equation store.
sConjDisjEqs :: System :-> Conj (SplitId, S.Set (LNSubstVFresh))
sConjDisjEqs = eqsConj . sEqStore

------------------------------------------------------------------------------
-- Proof Context
------------------------------------------------------------------------------

-- | A big-step source. (Formerly known as case distinction.)
data Source = Source
     { _cdGoal     :: Goal   -- start goal of source
       -- disjunction of named sequents with premise being solved; each name
       -- being the path of proof steps required to arrive at these cases
     , _cdCases    :: Disj ([String], System)
     }
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

data InductionHint = UseInduction | AvoidInduction
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A proof context contains the globally fresh facts, classified rewrite
-- rules and the corresponding precomputed premise source theorems.
data ProofContext = ProofContext
       { _pcSignature          :: SignatureWithMaude
       , _pcRules              :: ClassifiedRules
       , _pcInjectiveFactInsts :: S.Set FactTag
       , _pcSourceKind         :: SourceKind
       , _pcSources            :: [Source]
       , _pcUseInduction       :: InductionHint
       , _pcTraceQuantifier    :: SystemTraceQuantifier
       , _pcLemmaName          :: String
       , _pcHiddenLemmas       :: [String]
       , _pcDiffContext        :: Bool -- true if diff proof
       , _pcTrueSubterm        :: Bool -- true if in all rules the RHS is a subterm of the LHS
       , _pcConstantRHS        :: Bool -- true if there are rules with a constant RHS
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A diff proof context contains the two proof contexts for either side
-- and all rules.
data DiffProofContext = DiffProofContext
       {
         _dpcPCLeft               :: ProofContext
       , _dpcPCRight              :: ProofContext
       , _dpcProtoRules           :: [ProtoRuleE]
       , _dpcConstrRules          :: [RuleAC]
       , _dpcDestrRules           :: [RuleAC]
       , _dpcRestrictions               :: [(Side, [LNGuarded])]
       }
       deriving( Eq, Ord, Show )

       
$(mkLabels [''ProofContext, ''DiffProofContext, ''Source])


-- | The 'MaudeHandle' of a proof-context.
pcMaudeHandle :: ProofContext :-> MaudeHandle
pcMaudeHandle = sigmMaudeHandle . pcSignature

-- | Returns the LHS or RHS proof-context of a diff proof context.
eitherProofContext :: DiffProofContext -> Side -> ProofContext
eitherProofContext ctxt s = if s==LHS then L.get dpcPCLeft ctxt else L.get dpcPCRight ctxt

-- Instances
------------

instance HasFrees Source where
    foldFrees f th =
        foldFrees f (L.get cdGoal th)   `mappend`
        foldFrees f (L.get cdCases th)

    foldFreesOcc  _ _ = const mempty

    mapFrees f th = Source <$> mapFrees f (L.get cdGoal th)
                                    <*> mapFrees f (L.get cdCases th)

data DiffProofType = RuleEquivalence | None
    deriving( Eq, Ord, Show, Generic, NFData, Binary )
    
-- | A system used in diff proofs. 
data DiffSystem = DiffSystem
    { _dsProofType      :: Maybe DiffProofType              -- The diff proof technique used
    , _dsSide           :: Maybe Side                       -- The side for backward search, when doing rule equivalence
    , _dsProofContext   :: Maybe ProofContext               -- The proof context used
    , _dsSystem         :: Maybe System                     -- The constraint system used
    , _dsProtoRules     :: S.Set ProtoRuleE                 -- the rules of the protocol
    , _dsConstrRules    :: S.Set RuleAC                     -- the construction rules of the theory
    , _dsDestrRules     :: S.Set RuleAC                     -- the descruction rules of the theory
    , _dsCurrentRule    :: Maybe String                     -- the name of the rule under consideration
    }
    deriving( Eq, Ord, Generic, NFData, Binary )

$(mkLabels [''DiffSystem])

------------------------------------------------------------------------------
-- Constraint system construction
------------------------------------------------------------------------------

-- | The empty constraint system, which is logically equivalent to true.
emptySystem :: SourceKind -> Bool -> System
emptySystem d isdiff = System
    M.empty S.empty S.empty Nothing emptyEqStore
    S.empty S.empty S.empty
    M.empty 0 d isdiff

-- | The empty diff constraint system.
emptyDiffSystem :: DiffSystem
emptyDiffSystem = DiffSystem
    Nothing Nothing Nothing Nothing S.empty S.empty S.empty Nothing

-- | Returns the constraint system that has to be proven to show that given
-- formula holds in the context of the given theory.
formulaToSystem :: [LNGuarded]           -- ^ Restrictions to add
                -> SourceKind            -- ^ Source kind
                -> SystemTraceQuantifier -- ^ Trace quantifier
                -> Bool                  -- ^ In diff proofs, all action goals have to be resolved
                -> LNFormula
                -> System
formulaToSystem restrictions kind traceQuantifier isdiff fm = 
      insertLemmas safetyRestrictions
    $ L.set sFormulas (S.singleton gf2)
    $ (emptySystem kind isdiff)
  where
    (safetyRestrictions, otherRestrictions) = partition isSafetyFormula restrictions
    gf0 = formulaToGuarded_ fm
    gf1 = case traceQuantifier of
      ExistsSomeTrace -> gf0
      ExistsNoTrace   -> gnot gf0
    -- Non-safety restrictions must be added to the formula, as they render the set
    -- of traces non-prefix-closed, which makes the use of induction unsound.
    gf2 = gconj $ gf1 : otherRestrictions

-- | Add a lemma / additional assumption to a constraint system.
insertLemma :: LNGuarded -> System -> System
insertLemma =
    go
  where
    go (GConj conj) = foldr (.) id $ map go $ getConj conj
    go fm           = L.modify sLemmas (S.insert fm)

-- | Add lemmas / additional assumptions to a constraint system.
insertLemmas :: [LNGuarded] -> System -> System
insertLemmas fms sys = foldl' (flip insertLemma) sys fms

------------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------------


-- Nodes
------------

-- | A list of all KD-conclusions in the 'System'.
allKDConcs :: System -> [(NodeId, RuleACInst, LNTerm)]
allKDConcs sys = do
    (i, ru)                            <- M.toList $ L.get sNodes sys
    (_, kFactView -> Just (DnK, m)) <- enumConcs ru
    return (i, ru, m)

-- | @nodeRule v@ accesses the rule label of node @v@ under the assumption that
-- it is present in the sequent.
nodeRule :: NodeId -> System -> RuleACInst
nodeRule v se =
    fromMaybe errMsg $ M.lookup v $ L.get sNodes se
  where
    errMsg = error $
        "nodeRule: node '" ++ show v ++ "' does not exist in sequent\n" ++
        render (nest 2 $ prettySystem se)

-- | @nodeRuleSafe v@ accesses the rule label of node @v@.
nodeRuleSafe :: NodeId -> System -> Maybe RuleACInst
nodeRuleSafe v se = M.lookup v $ L.get sNodes se

-- | @nodePremFact prem se@ computes the fact associated to premise @prem@ in
-- sequent @se@ under the assumption that premise @prem@ is a a premise in
-- @se@.
nodePremFact :: NodePrem -> System -> LNFact
nodePremFact (v, i) se = L.get (rPrem i) $ nodeRule v se

-- | @nodePremNode prem@ is the node that this premise is referring to.
nodePremNode :: NodePrem -> NodeId
nodePremNode = fst

-- | All facts associated to this node premise.
resolveNodePremFact :: NodePrem -> System -> Maybe LNFact
resolveNodePremFact (v, i) se = lookupPrem i =<< M.lookup v (L.get sNodes se)

-- | The fact associated with this node conclusion, if there is one.
resolveNodeConcFact :: NodeConc -> System -> Maybe LNFact
resolveNodeConcFact (v, i) se = lookupConc i =<< M.lookup v (L.get sNodes se)

-- | @nodeConcFact (NodeConc (v, i))@ accesses the @i@-th conclusion of the
-- rule associated with node @v@ under the assumption that @v@ is labeled with
-- a rule that has an @i@-th conclusion.
nodeConcFact :: NodeConc -> System -> LNFact
nodeConcFact (v, i) = L.get (rConc i) . nodeRule v

-- | 'nodeConcNode' @c@ compute the node-id of the node conclusion @c@.
nodeConcNode :: NodeConc -> NodeId
nodeConcNode = fst

-- | Returns a node premise fact from a node map
nodePremFactMap :: NodePrem -> M.Map NodeId RuleACInst -> LNFact
nodePremFactMap (v, i) nodes = L.get (rPrem i) $ nodeRuleMap v nodes

-- | Returns a node conclusion fact from a node map
nodeConcFactMap :: NodeConc -> M.Map NodeId RuleACInst -> LNFact
nodeConcFactMap (v, i) nodes = L.get (rConc i) $ nodeRuleMap v nodes

-- | Returns a rule instance from a node map
nodeRuleMap :: NodeId -> M.Map NodeId RuleACInst -> RuleACInst
nodeRuleMap v nodes =
    fromMaybe errMsg $ M.lookup v $ nodes
  where
    errMsg = error $
        "nodeRuleMap: node '" ++ show v ++ "' does not exist in sequent\n"


-- | 'getMaudeHandle' @ctxt@ @side@ returns the maude handle on side @side@ in diff proof context @ctxt@.
getMaudeHandle :: DiffProofContext -> Side -> MaudeHandle
getMaudeHandle ctxt side = if side == RHS then L.get (pcMaudeHandle . dpcPCRight) ctxt else L.get (pcMaudeHandle . dpcPCLeft) ctxt

-- | 'getAllRulesOnOtherSide' @ctxt@ @side@ returns all rules in diff proof context @ctxt@ on the opposite side of side @side@.
getAllRulesOnOtherSide :: DiffProofContext -> Side -> [RuleAC]
getAllRulesOnOtherSide ctxt side = getAllRulesOnSide ctxt $ if side == LHS then RHS else LHS

-- | 'getAllRulesOnSide' @ctxt@ @side@ returns all rules in diff proof context @ctxt@ on the side @side@.
getAllRulesOnSide :: DiffProofContext -> Side -> [RuleAC]
getAllRulesOnSide ctxt side = joinAllRules $ L.get pcRules $ if side == RHS then L.get dpcPCRight ctxt else L.get dpcPCLeft ctxt

-- | 'protocolRuleWithName' @rules@ @name@ returns all rules with protocol rule name @name@ in rules @rules@.
protocolRuleWithName :: [RuleAC] -> ProtoRuleName -> [RuleAC]
protocolRuleWithName rules name = filter (\(Rule x _ _ _) -> case x of
                                             ProtoInfo p -> (L.get pracName p) == name
                                             IntrInfo  _ -> False) rules

-- | 'intruderRuleWithName' @rules@ @name@ returns all rules with intruder rule name @name@ in rules @rules@.
--   This ignores the number of remaining consecutive rule applications.
intruderRuleWithName :: [RuleAC] -> IntrRuleACInfo -> [RuleAC]
intruderRuleWithName rules name = filter (\(Rule x _ _ _) -> case x of
                                             IntrInfo  (DestrRule i _ _ _) -> case name of
                                                                                 (DestrRule j _ _ _) -> i == j
                                                                                 _                   -> False
                                             IntrInfo  i -> i == name
                                             ProtoInfo _ -> False) rules
    
-- | 'getOppositeRules' @ctxt@ @side@ @rule@ returns all rules with the same name as @rule@ in diff proof context @ctxt@ on the opposite side of side @side@.
getOppositeRules :: DiffProofContext -> Side -> RuleACInst -> [RuleAC]
getOppositeRules ctxt side (Rule rule prem _ _) = case rule of
               ProtoInfo p -> case protocolRuleWithName (getAllRulesOnOtherSide ctxt side) (L.get praciName p) of
                                   [] -> error $ "No other rule found for protocol rule " ++ show (L.get praciName p) ++ show (getAllRulesOnOtherSide ctxt side)
                                   x  -> x
               IntrInfo  i -> case i of
                                   (ConstrRule x) | x == BC.pack "_mult"  -> [(multRuleInstance (length prem))]
                                   (ConstrRule x) | x == BC.pack "_union" -> [(unionRuleInstance (length prem))]
                                   _                                      -> case intruderRuleWithName (getAllRulesOnOtherSide ctxt side) i of
                                                                                 [] -> error $ "No other rule found for intruder rule " ++ show i ++ show (getAllRulesOnOtherSide ctxt side)
                                                                                 x  -> x
                                                                                 
-- | 'getOriginalRule' @ctxt@ @side@ @rule@ returns the original rule of protocol rule @rule@ in diff proof context @ctxt@ on side @side@.
getOriginalRule :: DiffProofContext -> Side -> RuleACInst -> RuleAC
getOriginalRule ctxt side (Rule rule _ _ _) = case rule of
               ProtoInfo p -> case protocolRuleWithName (getAllRulesOnSide ctxt side) (L.get praciName p) of
                                   [x]  -> x
                                   _    -> error $ "getOriginalRule: No or more than one other rule found for protocol rule " ++ show (L.get praciName p) ++ show (getAllRulesOnSide ctxt side)
               IntrInfo  _ -> error $ "getOriginalRule: This should be a protocol rule: " ++ show rule


-- | Returns true if the graph is correct, i.e. complete and conclusions and premises match
-- | Note that this does not check if all goals are solved, nor if any restrictions are violated!
-- FIXME: consider implicit deduction
isCorrectDG :: System -> Bool
isCorrectDG sys = M.foldrWithKey (\k x y -> y && (checkRuleInstance sys k x)) True (L.get sNodes sys)
  where
    checkRuleInstance :: System -> NodeId -> RuleACInst -> Bool
    checkRuleInstance sys' idx rule = foldr (\x y -> y && (checkPrems sys' idx x)) True (enumPrems rule)
      
    checkPrems :: System -> NodeId -> (PremIdx, LNFact) -> Bool
    checkPrems sys' idx (premidx, fact) = case S.toList (S.filter (\(Edge _ y) -> y == (idx, premidx)) (L.get sEdges sys')) of
                                               [(Edge x _)] -> fact == nodeConcFact x sys'
                                               _            -> False
                                               
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
safePartialAtomValuation :: ProofContext -> System -> LNAtom -> Maybe Bool
safePartialAtomValuation ctxt sys =
    eval
  where
    runMaude   = (`runReader` L.get pcMaudeHandle ctxt)
    before     = alwaysBefore sys
    lessRel    = rawLessRel sys
    nodesAfter = \i -> filter (i /=) $ S.toList $ D.reachableSet [i] lessRel

    -- | 'True' iff there in every solution to the system the two node-ids are
    -- instantiated to a different index *in* the trace.
    nonUnifiableNodes :: NodeId -> NodeId -> Bool
    nonUnifiableNodes i j = maybe False (not . runMaude) $
        (unifiableRuleACInsts) <$> M.lookup i (L.get sNodes sys)
                               <*> M.lookup j (L.get sNodes sys)

    -- | Try to evaluate the truth value of this atom in all models of the
    -- constraint system 'sys'.
    eval ato = case ato of
          Action (ltermNodeId' -> i) fa
            | otherwise ->
                case M.lookup i (L.get sNodes sys) of
                  Just ru
                    | any (fa ==) (L.get rActs ru)                                -> Just True
                    | all (not . runMaude . unifiableLNFacts fa) (L.get rActs ru) -> Just False
                  _                                                               -> Nothing

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
                case L.get sLastAtom sys of
                  Just j | nonUnifiableNodes i j -> Just False
                  _                              -> Nothing

-- | @impliedFormulas se imp@ returns the list of guarded formulas that are
-- implied by @se@.
impliedFormulas :: MaudeHandle -> System -> LNGuarded -> [LNGuarded]
impliedFormulas hnd sys gf0 = res
  where
    res = case (openGuarded gf `evalFresh` avoid gf) of
      Just (All, _vs, antecedent, succedent) -> do
        let (actionsEqs, otherAtoms) = first sortGAtoms . partitionEithers $
                                        map prepare antecedent
            succedent'               = gall [] otherAtoms succedent
        subst <- candidateSubsts emptySubst actionsEqs
        return $ unskolemizeLNGuarded $ applySkGuarded subst succedent'
      _ -> []
    gf = skolemizeGuarded gf0

    prepare (Action i fa) = Left  (GAction i fa)
    prepare (EqE s t)     = Left  (GEqE s t)
    prepare ato           = Right (fmap (fmapTerm (fmap Free)) ato)

    sysActions = do (i, fa) <- allActions sys
                    return (skolemizeTerm (varTerm i), skolemizeFact fa)

    candidateSubsts subst []               = return $ subst
    candidateSubsts subst ((GAction a fa):as) = do
        sysAct <- sysActions
        subst' <- (`runReader` hnd) $ matchAction sysAct (applySkAction subst (a, fa))
        candidateSubsts (compose subst' subst) as
    candidateSubsts subst ((GEqE s' t'):as)   = do
        let s = applySkTerm subst s'
            t = applySkTerm subst t'
            (term,pat) | frees s == [] = (s,t)
                       | frees t == [] = (t,s)
                       | otherwise     = error $ "impliedFormulas: impossible, "
                                           ++ "equality not guarded as checked"
                                           ++"by 'Guarded.formulaToGuarded'."
        subst' <- (`runReader` hnd) $ matchTerm term pat
        candidateSubsts (compose subst' subst) as

-- | @impliedFormulasAndSystems se imp@ returns the list of guarded formulas that are
-- *potentially* implied by @se@, together with the updated system.
impliedFormulasAndSystems :: MaudeHandle -> System -> LNGuarded -> [(LNGuarded, System)]
impliedFormulasAndSystems hnd sys gf = res
  where
    res = case (openGuarded gf `evalFresh` avoid (gf, sys)) of
      Just (All, _vs, antecedent, succedent) -> map (\x -> apply x (succedent', sys)) subst
        where
          (actionsEqs, otherAtoms) = first sortGAtoms . partitionEithers $ map prepare antecedent
          succedent'               = gall [] otherAtoms succedent
          subst' = concat $ map (\(x, y) ->
            if null ((`runReader` hnd) (unifyLNTerm x))
               then []
               else (`runReader` hnd) (unifyLNTerm y)) (equalities actionsEqs)
          subst  = map (\x -> freshToFreeAvoiding x ((gf, x), sys)) subst'
      _ -> []

    prepare (Action i fa) = Left  (GAction i fa)
    prepare (EqE s t)     = Left  (GEqE s t)
    prepare ato           = Right (fmap (fmapTerm (fmap Free)) ato)

    sysActions = allActions sys

    equalities :: [GAtom (Term (Lit Name LVar))] -> [([Equal LNTerm], [Equal LNTerm])]
    equalities []                  = [([], [])]
    equalities ((GAction a fa):as) = go sysActions
      where
        go :: [(NodeId, LNFact)] -> [([Equal LNTerm], [Equal LNTerm])]
        go []                                                  = []
        go ((nid, sysAct):acts) | factTag sysAct == factTag fa =
            (map (\(x, y) -> ((((Equal (toConst nid) a):(zipWith Equal (factTerms sysAct) (factTerms fa))) ++ x),
                              (((Equal (varTerm nid) a):(zipWith Equal (factTerms sysAct) (factTerms fa))) ++ y))) $ equalities as)
                                  ++ (go acts)
        go ((_  , _     ):acts) | otherwise                    = go acts
    equalities ((GEqE s t):as)     = map (\(x, y) -> ((Equal s t):x, (Equal s t):y)) $ equalities as

    toConst cvar = constTerm (Name NodeName (NameId ("constVar_" ++ toConstName cvar)))
    toConstName (LVar name vsort idx) = (show vsort) ++ "_" ++ (show idx) ++ "_" ++ name

-- | Removes all restrictions that are not relevant for the system, i.e. that only contain atoms not present in the system.
filterRestrictions :: ProofContext -> System -> [LNGuarded] -> [LNGuarded]
filterRestrictions ctxt sys formulas = filter (unifiableNodes) formulas
  where
    runMaude   = (`runReader` L.get pcMaudeHandle ctxt)

    -- | 'True' iff there in every solution to the system the two node-ids are
    -- instantiated to a different index *in* the trace.
    unifiableNodes :: LNGuarded -> Bool
    unifiableNodes fm = case fm of
         (GAto ato)  -> unifiableAtoms {-$ trace ("atom on which bvarToLVar will be applied [ato]: " ++ show ato)-} $ [bvarToLVar ato]
         (GDisj fms) -> any unifiableNodes $ getDisj fms
         (GConj fms) -> any unifiableNodes $ getConj fms
         gg@(GGuarded _ _ _ _) -> case evalFreshAvoiding (openGuarded gg) (L.get sNodes sys) of
                                          Nothing               -> error "Bug in filterRestrictions, please report."
                                          Just (_, _, atos, gf) -> (unifiableNodes gf) || (unifiableAtoms atos)

    unifiableAtoms :: [Atom (VTerm Name (LVar))] -> Bool
    unifiableAtoms []                   = False
    unifiableAtoms ((Action _ fact):fs) = unifiableFact fact || unifiableAtoms fs
    unifiableAtoms (_:fs)               = unifiableAtoms fs

    unifiableFact :: LNFact -> Bool
    unifiableFact fact = mapper fact

    mapper fact = any (runMaude . unifiableLNFacts fact) $ concat $ map (L.get rActs . snd) $ M.toList (L.get sNodes sys)

-- | Computes the mirror dependency graph and evaluates whether the restrictions hold.
-- Returns Just True and a list of mirrors if all hold, Just False and a list of attacks (if found) if at least one does not hold and Nothing otherwise.
getMirrorDGandEvaluateRestrictions :: DiffProofContext -> DiffSystem -> Bool -> Maybe (Bool, [System])
getMirrorDGandEvaluateRestrictions dctxt dsys isSolved = do
    side <- L.get dsSide dsys
    sys  <- L.get dsSystem dsys
    case getMirrorDG dctxt side sys of
        Just sys' -> {-trace ("RE: restrictions: " ++ (show (restrictions (opposite s) sys'')) ++ " " ++ (show s) ++ " " ++ show (isSolved s sys'))-} (doRestrictionsHold oppositeCtxt sys' restrictions isSolved)
            where
                oppositeCtxt = eitherProofContext dctxt (opposite side)

                restrictions = filterRestrictions oppositeCtxt sys' $ restrictions' (opposite side) $ L.get dpcRestrictions dctxt

                restrictions' _  []               = []
                restrictions' s' ((s'', form):xs) = if s' == s'' then form ++ (restrictions' s' xs) else (restrictions' s' xs)

        Nothing  -> {-trace ("No mirror DG") $-} Just (False, [])


-- | Evaluates whether the formulas hold using safePartialAtomValuation and impliedFormulas.
-- Returns Just True if all hold, Just False if at least one does not hold and Nothing otherwise.
doRestrictionsHold :: ProofContext -> System -> [LNGuarded] -> Bool -> Maybe (Bool, [System])
doRestrictionsHold _    sys []       _        = Just (True, [sys])
doRestrictionsHold ctxt sys formulas isSolved = -- Just (True, [sys]) -- FIXME Jannik: This is a temporary simulation of diff-safe restrictions!
  if (all (\(x, _) -> x == gtrue) simplifiedForms)
    then Just {-$ trace ("doRestrictionsHold: True " ++ (render. vsep $ map (prettyGuarded) formulas) ++ " - " ++ (render. vsep $ map (\(x, _) -> prettyGuarded x) simplifiedForms))-} (True, map snd simplifiedForms)
    else if (any (\(x, _) -> x == gfalse) simplifiedForms)
          then Just {-$ trace ("doRestrictionsHold: False " ++ (render. vsep $ map (prettyGuarded) formulas) ++ " - " ++ (render. vsep $ map (\(x, _) -> prettyGuarded x) simplifiedForms))-} (False, map snd $ filter (\(x, _) -> x == gfalse) simplifiedForms)
          else {-trace ("doRestrictionsHold: Nothing " ++ (render. vsep $ map (prettyGuarded) formulas) ++ " - " ++ (render. vsep $ map (\(x, _) -> prettyGuarded x) simplifiedForms))-} Nothing
  where
    simplifiedForms = simplify (map (\x -> (x, sys)) formulas) isSolved

    simplify :: [(LNGuarded, System)] -> Bool -> [(LNGuarded, System)]
    simplify forms solved =
        if ({-trace ("step: " ++ (render. vsep $ map (\(x, _) -> prettyGuarded x) forms) ++ " " ++ (render. vsep $ map (\(x, _) -> prettyGuarded x) res))-} res) == forms
            then res
            else simplify res solved
      where
        res = step forms solved

    step :: [(LNGuarded, System)] -> Bool -> [(LNGuarded, System)]
    step forms solved = map simpGuard $ concat {-$ trace (show (map (impliedOrInitial solved) forms))-} $ map (impliedOrInitial solved) forms

    valuation s' = safePartialAtomValuation ctxt s'

    simpGuard :: (LNGuarded, System) -> (LNGuarded, System)
    simpGuard (f, sys') = (simplifyGuardedOrReturn (valuation sys') f, sys')

    impliedOrInitial :: Bool -> (LNGuarded, System) -> [(LNGuarded, System)]
    impliedOrInitial solved (f, sys') = if isAllGuarded f && (solved || not (null imps)) then imps else [(f, sys')]
      where
        imps = map (fmap (normDG ctxt)) $ impliedFormulasAndSystems (L.get pcMaudeHandle ctxt) sys' f

-- | Normalizes all terms in the dependency graph.
normDG :: ProofContext -> System -> System
normDG ctxt sys = L.set sNodes normalizedNodes sys
  where
    normalizedNodes = M.map (\r -> runReader (normRule r) (L.get pcMaudeHandle ctxt)) (L.get sNodes sys)

-- | Returns the mirrored DG, if it exists.
getMirrorDG :: DiffProofContext -> Side -> System -> Maybe System
getMirrorDG ctxt side sys = fmap (normDG $ eitherProofContext ctxt side) $ unifyInstances sys $ evalFreshAvoiding newNodes freshAndPubConstrRules
  where
    (freshAndPubConstrRules, notFreshNorPub) = (M.partition (\rule -> (isFreshRule rule) || (isPubConstrRule rule)) (L.get sNodes sys))
    (newProtoRules, otherRules) = (M.partition (\rule -> (containsNewVars rule) && (isProtocolRule rule)) notFreshNorPub)
    newNodes = (M.foldrWithKey (transformRuleInstance) (M.foldrWithKey (transformRuleInstance) (return [freshAndPubConstrRules]) newProtoRules) otherRules)

    -- We keep instantiations of fresh and public variables. Currently new public variables in protocol rule instances 
    -- are instantiated correctly in someRuleACInstAvoiding, but if this is changed we need to fix this part.
    transformRuleInstance :: MonadFresh m => NodeId -> RuleACInst -> m ([M.Map NodeId RuleACInst]) -> m ([M.Map NodeId RuleACInst])
    transformRuleInstance idx rule nodes = genNodeMapsForAllRuleVariants <$> nodes <*> (getOtherRulesAndVariants rule)
      where
        genNodeMapsForAllRuleVariants :: [M.Map NodeId RuleACInst] -> [RuleACInst] -> [M.Map NodeId RuleACInst]
        genNodeMapsForAllRuleVariants nodes' rules = (\x y -> M.insert idx y x) <$> nodes' <*> rules

        getOtherRulesAndVariants :: MonadFresh m => RuleACInst -> m ([RuleACInst])
        getOtherRulesAndVariants r = mapGetVariants (getOppositeRules ctxt side r)
          where       
            mapGetVariants :: MonadFresh m => [RuleAC] -> m ([RuleACInst])
            mapGetVariants []     = return []
            mapGetVariants (x:xs) = do
              instances <- if isProtocolRule r 
                              then someRuleACInstFixing x $ getSubstitutionsFixingNewVars r $ getOriginalRule ctxt side r
                              else someRuleACInst x
              variants <- getVariants instances
              rest <- mapGetVariants xs
              return (variants++rest)
            
        getVariants :: MonadFresh m => (RuleACInst, Maybe RuleACConstrs) -> m ([RuleACInst])
        getVariants (r, Nothing)       = return [r]
        getVariants (r, Just (Disj v)) = appSubst v
          where
            appSubst :: MonadFresh m => [LNSubstVFresh] -> m ([RuleACInst])
            appSubst []     = return []
            appSubst (x:xs) = do
              subst <- freshToFree x
              inst <- return (apply subst r)
              rest <- appSubst xs
              return (inst:rest)
                                              
    unifyInstances :: System -> [M.Map NodeId RuleACInst] -> Maybe System
    unifyInstances sys' newrules = 
--      trace ("unifyInstances:" ++  (show $ head $ map (unifiers . equalities sys' True) newrules) ++ " |\n " ++ (show $ head $ map (equalities sys' True) newrules) ++ " |\n " {-++ show (map avoid newrules) ++ " - " ++ show (avoid sys') ++ " |\n "-} ++ (show $ head newrules) ++ " |\n " ++ (show sys')) $
      foldl (\ret x -> if (ret /= Nothing) || (null $ unifiers $ equalities sys' True x) then ret else Just $ L.set sNodes (foldl (\y z -> apply z y) x (freeUnifiers x)) sys') Nothing newrules
      -- We can stop if a corresponding system is found for one variant. Otherwise we continue until we find a system which we can unify, or return Nothing if no such system exists.
        where
          freeUnifiers :: M.Map NodeId RuleACInst -> [LNSubst]
          freeUnifiers newnodes = map (\y -> freshToFreeAvoiding y newnodes) (unifiers $ equalities sys' False newnodes)
        
    unifiers :: Maybe [Equal LNFact] -> [SubstVFresh Name LVar]
    unifiers (Nothing)         = []
    unifiers (Just equalfacts) = runReader (unifyLNFactEqs equalfacts) (getMaudeHandle ctxt side)
    
    equalities :: System -> Bool -> M.Map NodeId RuleACInst -> Maybe [Equal LNFact]
    equalities sys' fixNewVars newrules' = (++) <$> (Just ((getGraphEqualities newrules' sys') ++ (getKUEqualities ({-trace (show (getKUEqualities newrules' sys'))-} newrules') sys'))) <*> (if fixNewVars then (getNewVarEqualities newrules' sys') else Just [])
        
    getGraphEqualities :: M.Map NodeId RuleACInst -> System -> [Equal LNFact]
    getGraphEqualities nodes sys' = map (\(Edge x y) -> Equal (nodePremFactMap y nodes) (nodeConcFactMap x nodes)) $ S.toList (L.get sEdges sys')
    
    getKUEqualities :: M.Map NodeId RuleACInst -> System -> [Equal LNFact]
    getKUEqualities nodes sys' = map (\(Edge y x) -> Equal (nodePremFactMap x nodes) (nodeConcFactMap y nodes)) $ getEdgesFromLessRelation sys'

    getNewVarEqualities :: M.Map NodeId RuleACInst -> System -> Maybe ([Equal LNFact])
    getNewVarEqualities nodes sys' = (++) <$> (genTrivialEqualities nodes sys') <*> (Just (concat $ map (\(_, r) -> genEqualities $ map (\(x, y) -> (x, y, y)) $ getNewVariables r) $ M.toList nodes))
      where
        genEqualities :: [(LNFact, LVar, LVar)] -> [Equal LNFact]
        genEqualities = map (\(x, y, z) -> Equal x (replaceNewVarWithConstant x y z))
        
        genTrivialEqualities :: M.Map NodeId RuleACInst -> System -> Maybe ([Equal LNFact])
        genTrivialEqualities nodes' sys'' = genEqualities <$> getTrivialFacts nodes' sys''
                
        replaceNewVarWithConstant :: LNFact -> LVar -> LVar -> LNFact
        replaceNewVarWithConstant fact v cvar = apply subst fact
          where
            subst = Subst (M.fromList [(v, constTerm (Name (pubOrFresh v) (NameId ("constVar_" ++ toConstName cvar))))])
            
            toConstName (LVar name vsort idx) = (show vsort) ++ "_" ++ (show idx) ++ "_" ++ name

            pubOrFresh (LVar _ LSortFresh _) = FreshName
            pubOrFresh (LVar _ _          _) = PubName

-- | Returns the set of edges of a system saturated with all edges deducible from the nodes and the less relation                                                 
saturateEdgesWithLessRelation :: System -> S.Set Edge 
saturateEdgesWithLessRelation sys = S.union (S.fromList $ getEdgesFromLessRelation sys) (L.get sEdges sys)

-- | Returns the set of implicit edges of a system, which are implied by the nodes and the less relation                                                 
getEdgesFromLessRelation :: System -> [Edge] 
getEdgesFromLessRelation sys = map (\(x, y) -> Edge y x) $ concat $ map (\x -> getAllMatchingConcs sys x $ getAllLessPreds sys $ fst x) (getOpenNodePrems sys)



-- | Given a system, a node premise, and a set of node ids from the less relation returns the set of implicit edges for this premise, if the rule instances exist                                                 
getAllMatchingConcs :: System -> NodePrem -> [NodeId] -> [(NodePrem, NodeConc)]
getAllMatchingConcs sys premid (x:xs) =
    case (nodeRuleSafe x sys) of
        Nothing   -> getAllMatchingConcs sys premid xs
        Just rule -> (map (\(cid, _) -> (premid, (x, cid))) (filter (\(_, cf) -> nodePremFact premid sys == cf) $ enumConcs rule))
            ++ (getAllMatchingConcs sys premid xs)
getAllMatchingConcs _    _     []     = []

-- | Given a system, a fact, and a set of node ids from the less relation returns the set of matching premises, if the rule instances exist                                                 
getAllMatchingPrems :: System -> LNFact -> [NodeId] -> [NodePrem]
getAllMatchingPrems sys fa (x:xs) =
    case (nodeRuleSafe x sys) of
        Nothing   -> getAllMatchingPrems sys fa xs
        Just rule -> (map (\(pid, _) -> (x, pid)) (filter (\(_, pf) -> fa == pf) $ enumPrems rule))
            ++ (getAllMatchingPrems sys fa xs)
getAllMatchingPrems _   _     []  = []

-- | Given a system and a node, gives the list of all nodes that have a "less" edge to this node
getAllLessPreds :: System -> NodeId -> [NodeId]
getAllLessPreds sys nid = map fst $ filter (\(_, y) -> nid == y) (S.toList (L.get sLessAtoms sys))

-- | Given a system and a node, gives the list of all nodes that have a "less" edge to this node
getAllLessSucs :: System -> NodeId -> [NodeId]
getAllLessSucs sys nid = map snd $ filter (\(x, _) -> nid == x) (S.toList (L.get sLessAtoms sys))

-- | Given a system, returns all node premises that have no incoming edge
getOpenNodePrems :: System -> [NodePrem]
getOpenNodePrems sys = getOpenIncoming (M.toList $ L.get sNodes sys)
  where
    getOpenIncoming :: [(NodeId, RuleACInst)] -> [NodePrem]
    getOpenIncoming []          = []
    getOpenIncoming ((k, r):xs) = (filter hasNoIncomingEdge $ map (\(x, _) -> (k, x)) (enumPrems r)) ++ (getOpenIncoming xs)
    
    hasNoIncomingEdge np = S.null (S.filter (\(Edge _ y) -> y == np) (L.get sEdges sys))
       
-- | Returns a list of all open trivial facts of nodes in the current system, and the variable they need to be unified with
getTrivialFacts :: M.Map NodeId RuleACInst -> System -> Maybe ([(LNFact, LVar, LVar)])
getTrivialFacts nodes sys = case (unsolvedTrivialGoals sys) of
                                 []     -> Just []
                                 (x:xs) -> foldl foldTreatGoal (treatGoal nodes x) xs
  where
    foldTreatGoal :: Maybe [(LNFact, LVar, LVar)] -> (Either NodePrem LVar, LNFact) -> Maybe [(LNFact, LVar, LVar)]
    foldTreatGoal eqdata goal = (++) <$> (treatGoal eqdata goal) <*> eqdata
    
    treatGoal :: HasFrees t => t -> (Either NodePrem LVar, LNFact) -> Maybe [(LNFact, LVar, LVar)]
    treatGoal _ (Left pidx, _ ) = (map (\(x, y) -> (x, y, y))) <$> getFactAndVars nodes pidx
    treatGoal a (Right var, fa) = premiseFacts (nodes, a) var fa
    
    premisesForKUAction :: LVar -> LNFact -> [NodePrem]
    premisesForKUAction var fa = getAllMatchingPrems sys fa $ getAllLessSucs sys var
    
    premiseFacts :: HasFrees t => t -> LVar -> LNFact -> Maybe ([(LNFact, LVar, LVar)])
    premiseFacts av var fa = fmap concat $ sequence $ map (getAllEqData (renameAvoiding fa av)) (premisesForKUAction var fa)

    getAllEqData :: LNFact -> NodePrem -> Maybe ([(LNFact, LVar, LVar)])
    getAllEqData fact p = zipWith (\(x, y) z -> (x, y, z)) <$> getFactAndVars nodes p <*> (isTrivialFact fact)

-- | If the fact at premid in nodes is trivial, returns the fact and its (trivial) variables. Otherwise returns nothing
getFactAndVars :: M.Map NodeId RuleACInst -> NodePrem -> Maybe ([(LNFact, LVar)])
getFactAndVars nodes premid = (map (\x -> (fact, x))) <$> (isTrivialFact fact)
  where
    fact = (nodePremFactMap premid nodes)
                
-- | Assumption: the goal is trivial. Returns true if it is independent wrt the rest of the system.                                                 
checkIndependence :: System -> (Either NodePrem LVar, LNFact) -> Bool
checkIndependence sys (eith, fact) = not (D.cyclic (rawLessRel sys))
    && (checkNodes $ case eith of
                         (Left premidx) -> checkIndependenceRec (L.get sNodes sys) premidx
                         (Right lvar)   -> foldl checkIndependenceRec (L.get sNodes sys) $ identifyPremises lvar fact)
  where
    edges = S.toList $ saturateEdgesWithLessRelation sys
    variables = fromMaybe (error $ "checkIndependence: This fact " ++ show fact ++ " should be trivial! System: " ++ show sys) (isTrivialFact fact)
    
    identifyPremises :: LVar -> LNFact -> [NodePrem]
    identifyPremises var' fact' = getAllMatchingPrems sys fact' (getAllLessSucs sys var')
    
    checkIndependenceRec :: M.Map NodeId RuleACInst -> NodePrem -> M.Map NodeId RuleACInst
    checkIndependenceRec nodes (nid, _) = foldl checkIndependenceRec (M.delete nid nodes) $ map (\(Edge _ tgt) -> tgt) $ filter (\(Edge (srcn, _) _) -> srcn == nid) edges
    
    checkNodes :: M.Map NodeId RuleACInst -> Bool
    checkNodes nodes = all (\(_, r) -> null $ filter (\f -> not $ null $ intersect variables (getFactVariables f)) (facts r)) $ M.toList nodes
      where
        facts ru = (map snd (enumPrems ru)) ++ (map snd (enumConcs ru))


-- | All premises that still need to be solved.
unsolvedPremises :: System -> [(NodePrem, LNFact)]
unsolvedPremises sys =
      do (PremiseG premidx fa, status) <- M.toList (L.get sGoals sys)
         guard (not $ L.get gsSolved status)
         return (premidx, fa)

-- | All trivial goals that still need to be solved.
unsolvedTrivialGoals :: System -> [(Either NodePrem LVar, LNFact)]
unsolvedTrivialGoals sys = foldl f [] $ M.toList (L.get sGoals sys)
  where
    f l (PremiseG premidx fa, status) = if ((isTrivialFact fa /= Nothing) && (not $ L.get gsSolved status)) then (Left premidx, fa):l else l 
    f l (ActionG var fa, status)      = if ((isTrivialFact fa /= Nothing) && (isKUFact fa) && (not $ L.get gsSolved status)) then (Right var, fa):l else l 
    f l (ChainG _ _, _)               = l 
    f l (SplitG _, _)                 = l 
    f l (DisjG _, _)                  = l 

-- | Tests whether there are common Variables in the Facts
noCommonVarsInGoals :: [(Either NodePrem LVar, LNFact)] -> Bool
noCommonVarsInGoals goals = noCommonVars $ map (getFactVariables . snd) goals
  where
    noCommonVars :: [[LVar]] -> Bool
    noCommonVars []     = True
    noCommonVars (x:xs) = (all (\y -> null $ intersect x y) xs) && (noCommonVars xs)

    
-- | Returns true if all formulas in the system are solved.
allFormulasAreSolved :: System -> Bool
allFormulasAreSolved sys = S.null $ L.get sFormulas sys

-- | Returns true if all the depedency graph is not empty.
dgIsNotEmpty :: System -> Bool
dgIsNotEmpty sys = not $ M.null $ L.get sNodes sys

-- | Assumption: all open goals in the system are "trivial" fact goals. Returns true if these goals are independent from each other and the rest of the system.
allOpenFactGoalsAreIndependent :: System -> Bool
allOpenFactGoalsAreIndependent sys = (noCommonVarsInGoals unsolvedGoals) && (all (checkIndependence sys) unsolvedGoals)
  where
    unsolvedGoals = unsolvedTrivialGoals sys

-- | Returns true if all open goals in the system are "trivial" fact goals.
allOpenGoalsAreSimpleFacts :: DiffProofContext -> System -> Bool
allOpenGoalsAreSimpleFacts ctxt sys = M.foldlWithKey goalIsSimpleFact True (L.get sGoals sys)
  where
    goalIsSimpleFact :: Bool -> Goal -> GoalStatus -> Bool
    goalIsSimpleFact ret (ActionG _ fact)         (GoalStatus solved _ _) = ret && (solved || ((isTrivialFact fact /= Nothing) && (isKUFact fact)))
    goalIsSimpleFact ret (ChainG _ _)             (GoalStatus solved _ _) = ret && solved
    goalIsSimpleFact ret (PremiseG (nid, _) fact) (GoalStatus solved _ _) = ret && (solved || (isTrivialFact fact /= Nothing) && (not (isProtocolRule r) || (getOriginalRule ctxt LHS r == getOriginalRule ctxt RHS r)))
      where
        r = nodeRule nid sys
    goalIsSimpleFact ret (SplitG _)               (GoalStatus solved _ _) = ret && solved
    goalIsSimpleFact ret (DisjG _)                (GoalStatus solved _ _) = ret && solved

-- | Returns true if the current system is a diff system
isDiffSystem :: System -> Bool
isDiffSystem = L.get sDiffSystem
        
-- Actions
----------

-- | All actions that hold in a sequent.
unsolvedActionAtoms :: System -> [(NodeId, LNFact)]
unsolvedActionAtoms sys =
      do (ActionG i fa, status) <- M.toList (L.get sGoals sys)
         guard (not $ L.get gsSolved status)
         return (i, fa)

-- | All actions that hold in a sequent.
allActions :: System -> [(NodeId, LNFact)]
allActions sys =
      unsolvedActionAtoms sys
  <|> do (i, ru) <- M.toList $ L.get sNodes sys
         (,) i <$> L.get rActs ru

-- | All actions that hold in a sequent.
allKUActions :: System -> [(NodeId, LNFact, LNTerm)]
allKUActions sys = do
    (i, fa@(kFactView -> Just (UpK, m))) <- allActions sys
    return (i, fa, m)

-- | The standard actions, i.e., non-KU-actions.
standardActionAtoms :: System -> [(NodeId, LNFact)]
standardActionAtoms = filter (not . isKUFact . snd) . unsolvedActionAtoms

-- | All KU-actions.
kuActionAtoms :: System -> [(NodeId, LNFact, LNTerm)]
kuActionAtoms sys = do
    (i, fa@(kFactView -> Just (UpK, m))) <- unsolvedActionAtoms sys
    return (i, fa, m)

-- Destruction chains
---------------------

-- | All unsolved destruction chains in the constraint system.
unsolvedChains :: System -> [(NodeConc, NodePrem)]
unsolvedChains sys = do
    (ChainG from to, status) <- M.toList $ L.get sGoals sys
    guard (not $ L.get gsSolved status)
    return (from, to)


-- The temporal order
---------------------

-- | @(from,to)@ is in @rawEdgeRel se@ iff we can prove that there is an
-- edge-path from @from@ to @to@ in @se@ without appealing to transitivity.
rawEdgeRel :: System -> [(NodeId, NodeId)]
rawEdgeRel sys = map (nodeConcNode *** nodePremNode) $
     [(from, to) | Edge from to <- S.toList $ L.get sEdges sys]
  ++ unsolvedChains sys

-- | @(from,to)@ is in @rawLessRel se@ iff we can prove that there is a path
-- (possibly using the 'Less' relation) from @from@ to @to@ in @se@ without
-- appealing to transitivity.
rawLessRel :: System -> [(NodeId,NodeId)]
rawLessRel se = S.toList (L.get sLessAtoms se) ++ rawEdgeRel se

-- | Returns a predicate that is 'True' iff the first argument happens before
-- the second argument in all models of the sequent.
alwaysBefore :: System -> (NodeId -> NodeId -> Bool)
alwaysBefore sys =
    check -- lessRel is cached for partial applications
  where
    lessRel   = rawLessRel sys
    check i j =
         -- speed-up check by first checking less-atoms
         ((i, j) `S.member` L.get sLessAtoms sys)
      || (j `S.member` D.reachableSet [i] lessRel)

-- | 'True' iff the given node id is guaranteed to be instantiated to an
-- index in the trace.
isInTrace :: System -> NodeId -> Bool
isInTrace sys i =
     i `M.member` L.get sNodes sys
  || isLast sys i
  || any ((i ==) . fst) (unsolvedActionAtoms sys)

-- | 'True' iff the given node id is guaranteed to be instantiated to the last
-- index of the trace.
isLast :: System -> NodeId -> Bool
isLast sys i = Just i == L.get sLastAtom sys

------------------------------------------------------------------------------
-- Pretty printing                                                          --
------------------------------------------------------------------------------

-- | Pretty print a sequent
prettySystem :: HighlightDocument d => System -> d
prettySystem se = vcat $ 
    map combine
      [ ("nodes",          vcat $ map prettyNode $ M.toList $ L.get sNodes se)
      , ("actions",        fsepList ppActionAtom $ unsolvedActionAtoms se)
      , ("edges",          fsepList prettyEdge   $ S.toList $ L.get sEdges se)
      , ("less",           fsepList prettyLess   $ S.toList $ L.get sLessAtoms se)
      , ("unsolved goals", prettyGoals False se)
      ]
    ++ [prettyNonGraphSystem se]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppActionAtom (i, fa) = prettyNAtom (Action (varTerm i) fa)

-- | Pretty print the non-graph part of the sequent; i.e. equation store and
-- clauses.
prettyNonGraphSystem :: HighlightDocument d => System -> d
prettyNonGraphSystem se = vsep $ map combine -- text $ show se
  [ ("last",            maybe (text "none") prettyNodeId $ L.get sLastAtom se)
  , ("formulas",        vsep $ map prettyGuarded {-(text . show)-} $ S.toList $ L.get sFormulas se)
  , ("equations",       prettyEqStore $ L.get sEqStore se)
  , ("lemmas",          vsep $ map prettyGuarded $ S.toList $ L.get sLemmas se)
  , ("allowed cases",   text $ show $ L.get sSourceKind se)
  , ("solved formulas", vsep $ map prettyGuarded $ S.toList $ L.get sSolvedFormulas se)
  , ("unsolved goals",  prettyGoals False se)
  , ("solved goals",    prettyGoals True se)
--   , ("DEBUG: Goals",    text $ show $ M.toList $ L.get sGoals se) -- prettyGoals False se)
--   , ("DEBUG: Nodes",    text $ show $ M.toList $ L.get sNodes se) -- prettyGoals False se)
--   , ("DEBUG",           text $ "dgIsNotEmpty: " ++ (show (dgIsNotEmpty se)) ++ " allFormulasAreSolved: " ++ (show (allFormulasAreSolved se)) ++ " allOpenGoalsAreSimpleFacts: " ++ (show (allOpenGoalsAreSimpleFacts se)) ++ " allOpenFactGoalsAreIndependent " ++ (show (allOpenFactGoalsAreIndependent se)) ++ " " ++ (if (dgIsNotEmpty se) && (allOpenGoalsAreSimpleFacts se) && (allOpenFactGoalsAreIndependent se) then ((show (map (checkIndependence se) $ unsolvedTrivialGoals se)) ++ " " ++ (show {-$ map (\(premid, x) -> getAllMatchingConcs se premid x)-} $ map (\(nid, pid) -> ((nid, pid), getAllLessPreds se nid)) $ getOpenNodePrems se) ++ " ") else " not trivial ") ++ (show $ unsolvedTrivialGoals se) ++ " " ++ (show $ getOpenNodePrems se))
  ]
  where
    combine (header, d)  = fsep [keyword_ header <> colon, nest 2 d]

-- | Pretty print the non-graph part of the sequent; i.e. equation store and
-- clauses.
prettyNonGraphSystemDiff :: HighlightDocument d => DiffProofContext -> DiffSystem -> d
prettyNonGraphSystemDiff _ se = vsep $ map combine
  [ ("proof type",          prettyProofType $ L.get dsProofType se)
  , ("current rule",        maybe (text "none") text $ L.get dsCurrentRule se)
  , ("system",              maybe (text "none") prettyNonGraphSystem $ L.get dsSystem se)
--   , ("mirror system",       case ((L.get dsSide se), (L.get dsSystem se)) of
--                                  (Just s, Just sys) | (dgIsNotEmpty sys) && (allOpenGoalsAreSimpleFacts ctxt sys) && (allOpenFactGoalsAreIndependent sys) -> maybe (text "none") prettySystem $ getMirrorDG ctxt s sys
--                                  _                                                                                                                        -> text "none")
--   , ("DEBUG",               maybe (text "none") (\x -> vsep $ map prettyGuarded x) help)
--   , ("DEBUG2",              maybe (text "none") (\x -> vsep $ map prettyGuarded x) help2)
  , ("protocol rules",      vsep $ map prettyProtoRuleE $ S.toList $ L.get dsProtoRules se)
  , ("construction rules",  vsep $ map prettyRuleAC $ S.toList $ L.get dsConstrRules se)
  , ("destruction rules",   vsep $ map prettyRuleAC $ S.toList $ L.get dsDestrRules se)
  ]
  where
    combine (header, d)  = fsep [keyword_ header <> colon, nest 2 d]
--     help :: Maybe [LNGuarded]
--     help = do 
--       side <- L.get dsSide se
-- --       system <- L.get dsSystem se
--       restrictions <- Just $ L.get dpcRestrictions ctxt
--       siderestrictions <- Just $ filter (\x -> fst x == side) restrictions
-- --       formulas <- Just $ concat $ map snd siderestrictions
-- --       evalFms <- Just $ doRestrictionsHold (if side == LHS then L.get dpcPCLeft ctxt else L.get dpcPCRight ctxt) system formulas
-- --       strings <- Just $ (concat $ map (\x -> (show x) ++ " ") evalFms) ++ (concat $ map (\x -> (show x) ++ " ") formulas)
--       return $ concat $ map snd siderestrictions
-- 
--     help2 :: Maybe [LNGuarded]
--     help2 = do 
--       side2 <- L.get dsSide se
--       side <- Just $ if side2 == LHS then RHS else LHS
-- --       system <- L.get dsSystem se
--       restrictions <- Just $ L.get dpcRestrictions ctxt
--       siderestrictions <- Just $ filter (\x -> fst x == side) restrictions
-- --       formulas <- Just $ concat $ map snd siderestrictions
-- --       evalFms <- Just $ doRestrictionsHold (if side == LHS then L.get dpcPCLeft ctxt else L.get dpcPCRight ctxt) system formulas
-- --       strings <- Just $ (concat $ map (\x -> (show x) ++ " ") evalFms) ++ (concat $ map (\x -> (show x) ++ " ") formulas)
--       return $ concat $ map snd siderestrictions

-- | Pretty print the proof type.
prettyProofType :: HighlightDocument d => Maybe DiffProofType -> d
prettyProofType Nothing  = text "none"
prettyProofType (Just p) = text $ show p

-- | Pretty print solved or unsolved goals.
prettyGoals :: HighlightDocument d => Bool -> System -> d
prettyGoals solved sys = vsep $ do
    (goal, status) <- M.toList $ L.get sGoals sys
    guard (solved == L.get gsSolved status)
    let nr  = L.get gsNr status
        loopBreaker | L.get gsLoopBreaker status = " (loop breaker)"
                    | otherwise                  = ""
        useful = case goal of
          _ | L.get gsLoopBreaker status              -> " (loop breaker)"
          ActionG i (kFactView -> Just (UpK, m))
              -- if there are KU-guards then all knowledge goals are useful
            | hasKUGuards             -> " (useful1)"
            | currentlyDeducible i m  -> " (currently deducible)"
            | probablyConstructible m -> " (probably constructible)"
          _                           -> " (useful2)"
    return $ prettyGoal goal <-> lineComment_ ("nr: " ++ show nr ++ loopBreaker ++ show useful)
  where
    existingDeps = rawLessRel sys
    hasKUGuards  =
        any ((KUFact `elem`) . guardFactTags) $ S.toList $ L.get sFormulas sys

    checkTermLits :: (LSort -> Bool) -> LNTerm -> Bool
    checkTermLits p =
        Mono.getAll . foldMap (Mono.All . p . sortOfLit)

    -- KU goals of messages that are likely to be constructible by the
    -- adversary. These are terms that do not contain a fresh name or a fresh
    -- name variable. For protocols without loops they are very likely to be
    -- constructible. For protocols with loops, such terms have to be given
    -- similar priority as loop-breakers.
    probablyConstructible  m = checkTermLits (LSortFresh /=) m
                               && not (containsPrivate m)

    -- KU goals of messages that are currently deducible. Either because they
    -- are composed of public names only and do not contain private function
    -- symbols or because they can be extracted from a sent message using
    -- unpairing or inversion only.
    currentlyDeducible i m = (checkTermLits (LSortPub ==) m
                              && not (containsPrivate m))
                          || extractible i m

    extractible i m = or $ do
        (j, ru) <- M.toList $ L.get sNodes sys
        -- We cannot deduce a message from a last node.
        guard (not $ isLast sys j)
        let derivedMsgs = concatMap toplevelTerms $
                [ t | Fact OutFact [t] <- L.get rConcs ru] <|>
                [ t | Just (DnK, t)    <- kFactView <$> L.get rConcs ru]
        -- m is deducible from j without an immediate contradiction
        -- if it is a derived message of 'ru' and the dependency does
        -- not make the graph cyclic.
        return $ m `elem` derivedMsgs &&
                 not (j `S.member` D.reachableSet [i] existingDeps)

    toplevelTerms t@(viewTerm2 -> FPair t1 t2) =
        t : toplevelTerms t1 ++ toplevelTerms t2
    toplevelTerms t@(viewTerm2 -> FInv t1) = t : toplevelTerms t1
    toplevelTerms t = [t]

-- | Pretty print a case distinction
prettySource :: HighlightDocument d => Source -> d
prettySource th = vcat $
   [ prettyGoal $ L.get cdGoal th ]
   ++ map combine (zip [(1::Int)..] $ map snd . getDisj $ (L.get cdCases th))
  where
    combine (i, sys) = fsep [keyword_ ("Case " ++ show i) <> colon, nest 2 (prettySystem sys)]


-- Additional instances
-----------------------

deriving instance Show DiffSystem

instance Apply SourceKind where
    apply = const id

instance Apply System where
    apply subst (System a b c d e f g h i j k l) =
        System (apply subst a)
        -- we do not apply substitutions to node variables, so we do not apply them to the edges either
        b
        (apply subst c) (apply subst d)
        (apply subst e) (apply subst f) (apply subst g) (apply subst h)
        i j (apply subst k) (apply subst l)

instance HasFrees SourceKind where
    foldFrees = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees  = const pure

instance HasFrees GoalStatus where
    foldFrees = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees  = const pure

instance HasFrees System where
    foldFrees fun (System a b c d e f g h i j k l) =
        foldFrees fun a `mappend`
        foldFrees fun b `mappend`
        foldFrees fun c `mappend`
        foldFrees fun d `mappend`
        foldFrees fun e `mappend`
        foldFrees fun f `mappend`
        foldFrees fun g `mappend`
        foldFrees fun h `mappend`
        foldFrees fun i `mappend`
        foldFrees fun j `mappend`
        foldFrees fun k `mappend`
        foldFrees fun l

    foldFreesOcc fun ctx (System a _b _c _d _e _f _g _h _i _j _k _l) =
        foldFreesOcc fun ("a":ctx') a {- `mappend`
        foldFreesCtx fun ("b":ctx') b `mappend`
        foldFreesCtx fun ("c":ctx') c `mappend`
        foldFreesCtx fun ("d":ctx') d `mappend`
        foldFreesCtx fun ("e":ctx') e `mappend`
        foldFreesCtx fun ("f":ctx') f `mappend`
        foldFreesCtx fun ("g":ctx') g `mappend`
        foldFreesCtx fun ("h":ctx') h `mappend`
        foldFreesCtx fun ("i":ctx') i `mappend`
        foldFreesCtx fun ("j":ctx') j `mappend`
        foldFreesCtx fun ("k":ctx') k -}
      where ctx' = "system":ctx

    mapFrees fun (System a b c d e f g h i j k l) =
        System <$> mapFrees fun a
               <*> mapFrees fun b
               <*> mapFrees fun c
               <*> mapFrees fun d
               <*> mapFrees fun e
               <*> mapFrees fun f
               <*> mapFrees fun g
               <*> mapFrees fun h
               <*> mapFrees fun i
               <*> mapFrees fun j
               <*> mapFrees fun k
               <*> mapFrees fun l
