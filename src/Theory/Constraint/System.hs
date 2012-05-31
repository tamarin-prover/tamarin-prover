{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
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

  -- * Goals
  , Goal(..)
  , isActionGoal
  , isStandardActionGoal
  , isPremiseGoal
  , isPremDnKGoal
  , isChainGoal
  , isSplitGoal
  , isDisjGoal

  , prettyGoal

  -- * Constraint systems
  , System

  -- ** Construction
  , emptySystem

  , SystemTraceQuantifier(..)
  , formulaToSystem

  -- ** Node constraints
  , sNodes
  , allKDConcs

  , nodeConcNode
  , nodePremNode
  , nodePremFact
  , nodeConcFact
  , resolveNodePremFact
  , resolveNodeConcFact

  -- ** Actions
  , sActionAtoms

  , allActions
  , allKUActions
  , kuActionAtoms
  , standardActionAtoms

  -- ** Edge and chain constraints
  , sEdges
  , sChains

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
  , insertLemma

  -- ** Keeping track of typing assumptions
  , CaseDistKind(..)
  , sCaseDistKind

  -- * Pretty-printing
  , prettySystem
  , prettyNonGraphSystem

  ) where

import           Prelude                              hiding (id, (.))

import           Data.Binary
import qualified Data.DAG.Simple                      as D
import           Data.DeriveTH
import qualified Data.Foldable                        as F
import qualified Data.Map                             as M
import           Data.Maybe                           (fromMaybe)
import           Data.Monoid                          (Monoid(..))
import qualified Data.Set                             as S

import           Control.Basics
import           Control.Category
import           Control.DeepSeq

import           Data.Label                           ((:->), mkLabels)
import qualified Extension.Data.Label                 as L

import           Logic.Connectives
import           Theory.Constraint.System.Constraints
import           Theory.Model
import           Theory.Text.Pretty
import           Theory.Tools.EquationStore


------------------------------------------------------------------------------
-- Goals
------------------------------------------------------------------------------

-- | A 'Goal' denotes that a constraint reduction rule is applicable, which
-- might result in case splits. We either use a heuristic to decide what goal
-- to solve next or leave the choice to user (in case of the interactive UI).
data Goal =
       ActionG LVar LNFact
       -- ^ An action that must exist in the trace.
     | PremiseG NodePrem LNFact Bool
       -- ^ A premise that must have an incoming direct edge. The 'Bool'
       -- argument is 'True' if this premise is marked as a loop-breaker;
       -- i.e., if care must be taken to avoid solving such a premise too
       -- often.
     | PremDnKG NodePrem
       -- ^ A KD goal that must be solved using a destruction chain.
     | ChainG Chain
       -- A destruction chain that does not start from a message variable.
     | SplitG SplitId
       -- ^ A case split over equalities.
     | DisjG (Disj LNGuarded)
       -- ^ A case split over a disjunction.
     | ImplG LNGuarded
       -- ^ The consequent of a universally quantified clause that could be
       -- added to the sequent. For debugging mode only; currently commented
       -- out.
     deriving( Eq, Ord, Show )

-- | Pretty print a goal.
prettyGoal :: HighlightDocument d => Goal -> d
prettyGoal (ActionG i fa)          = prettyNAtom (Action (varTerm i) fa)
prettyGoal (ChainG ch)             = prettyChain ch
prettyGoal (PremiseG p fa mayLoop) =
    prettyNodePrem p <> brackets (prettyLNFact fa) <->
    (if mayLoop then comment_ "/* may loop */" else emptyDoc)
prettyGoal (PremDnKG p)            = text "KD" <> parens (prettyNodePrem p)
prettyGoal (ImplG gf)              =
    (text "Consequent" <>) $ nest 1 $ parens $ prettyGuarded gf
prettyGoal (DisjG (Disj gfs)) = (text "Disj" <>) $ fsep $
    punctuate (operator_ " |") (map (nest 1 . parens . prettyGuarded) gfs)
prettyGoal (SplitG x) =
    text "splitEqs" <> parens (text $ show (succ x))

-- Indicators
-------------

isActionGoal :: Goal -> Bool
isActionGoal (ActionG _ _) = True
isActionGoal _             = False

isStandardActionGoal :: Goal -> Bool
isStandardActionGoal (ActionG _ fa) = not (isKUFact fa)
isStandardActionGoal _              = False

isPremiseGoal :: Goal -> Bool
isPremiseGoal (PremiseG _ _ _) = True
isPremiseGoal _                = False

isPremDnKGoal :: Goal -> Bool
isPremDnKGoal (PremDnKG _) = True
isPremDnKGoal _            = False

isChainGoal :: Goal -> Bool
isChainGoal (ChainG _) = True
isChainGoal _          = False

isSplitGoal :: Goal -> Bool
isSplitGoal (SplitG _) = True
isSplitGoal _          = False

isDisjGoal :: Goal -> Bool
isDisjGoal (DisjG _) = True
isDisjGoal _         = False



-- Instances
------------

instance HasFrees Goal where
    foldFrees f goal = case goal of
        ActionG i fa          -> foldFrees f i `mappend` foldFrees f fa
        PremiseG p fa mayLoop -> foldFrees f p `mappend` foldFrees f fa `mappend` foldFrees f mayLoop
        PremDnKG p            -> foldFrees f p
        ChainG ch             -> foldFrees f ch
        SplitG i              -> foldFrees f i
        DisjG x               -> foldFrees f x
        ImplG x               -> foldFrees f x

    mapFrees f goal = case goal of
        ActionG i fa          -> ActionG  <$> mapFrees f i <*> mapFrees f fa
        PremiseG p fa mayLoop -> PremiseG <$> mapFrees f p <*> mapFrees f fa <*> mapFrees f mayLoop
        PremDnKG p            -> PremDnKG <$> mapFrees f p
        ChainG ch             -> ChainG   <$> mapFrees f ch
        SplitG i              -> SplitG   <$> mapFrees f i
        DisjG x               -> DisjG    <$> mapFrees f x
        ImplG x               -> ImplG    <$> mapFrees f x

instance Apply Goal where
    apply subst goal = case goal of
        ActionG i fa          -> ActionG  (apply subst i)     (apply subst fa)
        PremiseG p fa mayLoop -> PremiseG (apply subst p)     (apply subst fa) (apply subst mayLoop)
        PremDnKG p            -> PremDnKG (apply subst p)
        ChainG ch             -> ChainG   (apply subst ch)
        SplitG i              -> SplitG   (apply subst i)
        DisjG x               -> DisjG    (apply subst x)
        ImplG x               -> ImplG    (apply subst x)



------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- | Whether we are checking for the existence of a trace satisfiying a the
-- current constraint system or whether we're checking that no traces
-- satisfies the current constraint system.
data SystemTraceQuantifier = ExistsSomeTrace | ExistsNoTrace
       deriving( Eq, Ord, Show )

-- | Case dinstinction kind that are allowed. The order of the kinds
-- corresponds to the subkinding relation: untyped < typed.
data CaseDistKind = UntypedCaseDist | TypedCaseDist
       deriving( Eq, Ord )

instance Show CaseDistKind where
    show UntypedCaseDist = "untyped"
    show TypedCaseDist   = "typed"

-- | A constraint system.
data System = System {
      _sNodes          :: M.Map NodeId RuleACInst
    , _sEdges          :: S.Set Edge
    , _sChains         :: S.Set Chain
    , _sEqStore        :: EqStore
    , _sActionAtoms    :: S.Set (NodeId, LNFact)
    , _sLessAtoms      :: S.Set (NodeId, NodeId)
    , _sLastAtom       :: Maybe NodeId
    , _sFormulas       :: S.Set LNGuarded
    , _sSolvedFormulas :: S.Set LNGuarded
    , _sLemmas         :: S.Set LNGuarded
    , _sCaseDistKind   :: CaseDistKind
    }
    deriving( Eq, Ord )

$(mkLabels [''System])


-- Further accessors
--------------------

-- | Label to access the free substitution of the equation store.
sSubst :: System :-> LNSubst
sSubst = eqsSubst . sEqStore

-- | Label to access the conjunction of disjunctions of fresh substutitution in
-- the equation store.
sConjDisjEqs :: System :-> Conj (S.Set (LNSubstVFresh))
sConjDisjEqs = eqsConj . sEqStore


------------------------------------------------------------------------------
-- Constraint system construction
------------------------------------------------------------------------------

-- | The empty constraint system, which is logically equivalent to true.
emptySystem :: CaseDistKind -> System
emptySystem = System
    M.empty S.empty S.empty emptyEqStore
    S.empty S.empty Nothing S.empty S.empty S.empty

-- | Returns the constraint system that has to be proven to show that given
-- formula holds in the context of the given theory.
formulaToSystem :: CaseDistKind -> SystemTraceQuantifier -> LNFormula -> System
formulaToSystem kind traceQuantifier fm =
    L.set sFormulas (S.singleton gf) (emptySystem kind)
  where
    adapt = case traceQuantifier of
      ExistsSomeTrace -> id
      ExistsNoTrace   -> gnot
    gf = either error id (adapt <$> formulaToGuarded fm)

-- | Add a lemma / additional assumption to a constraint system.
insertLemma :: LNFormula -> System -> System
insertLemma fm =
    L.modify sLemmas (S.insert (either error id $ formulaToGuarded fm))


------------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------------


-- Nodes
------------

-- | A list of all KD-conclusions in the 'System'.
allKDConcs :: System -> [(NodeId, RuleACInst, LNTerm)]
allKDConcs sys = do
    (i, ru)                            <- M.toList $ L.get sNodes sys
    (_, kFactView -> Just (DnK, _, m)) <- enumConcs ru
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


-- Actions
----------

-- | All actions that hold in a sequent.
allActions :: System -> [(NodeId, LNFact)]
allActions se =
     S.toList (L.get sActionAtoms se)
  ++ do (i, ru) <- M.toList $ L.get sNodes se
        (,) i <$> L.get rActs ru
-- | All actions that hold in a sequent.
allKUActions :: System -> [(NodeId, LNFact, LNTerm)]
allKUActions se = do
    (i, fa@(kFactView -> Just (UpK, _, m))) <- allActions se
    return (i, fa, m)

-- | The standard actions, i.e., non-KU-actions.
standardActionAtoms :: System -> [(NodeId, LNFact)]
standardActionAtoms =
    filter (not . isKUFact . snd) . S.toList . L.get sActionAtoms

-- | All KU-actions.
kuActionAtoms :: System -> [(NodeId, LNFact, LNTerm)]
kuActionAtoms sys = do
    (i, fa@(kFactView -> Just (UpK, _, m))) <- S.toList $ L.get sActionAtoms sys
    return (i, fa, m)


-- The temporal order
---------------------

-- | @(from,to)@ is in @rawEdgeRel se@ iff we can prove that there is an
-- edge-path from @from@ to @to@ in @se@ without appealing to transitivity.
rawEdgeRel :: System -> [(NodeId, NodeId)]
rawEdgeRel se =
    map (nodeConcNode *** nodePremNode)
      ([ (from, to) | Edge from to <- S.toList $ L.get sEdges se ] ++
       [ (from, to) | Chain from to <- S.toList $ L.get sChains se ])

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
  || F.any ((i ==) . fst) (L.get sActionAtoms sys)

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
      [ ("nodes",     vcat $ map prettyNode $ M.toList $ L.get sNodes se)
      , ("actions",   ppSet ppActionAtom    $ L.get sActionAtoms se)
      , ("edges",     ppSet prettyEdge      $ L.get sEdges se)
      , ("chains",    ppSet prettyChain     $ L.get sChains se)
      , ("less",      ppSet prettyLess      $ L.get sLessAtoms se)
      ]
    ++ [prettyNonGraphSystem se]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppSet :: HighlightDocument d => (a -> d) -> S.Set a -> d
    ppSet f = fsep . punctuate comma . map f . S.toList
    ppActionAtom (i, fa) = prettyNAtom (Action (varTerm i) fa)

-- | Pretty print the non-graph part of the sequent; i.e. equation store and
-- clauses.
prettyNonGraphSystem :: HighlightDocument d => System -> d
prettyNonGraphSystem se = foldr ($--$) emptyDoc $ map combine
  [ ("last",            maybe (text "none") prettyNodeId $ L.get sLastAtom se)
  , ("allowed cases",   text $ show $ L.get sCaseDistKind se)
  , ("formulas",        foldr ($--$) emptyDoc $ map prettyGuarded $ S.toList $ L.get sFormulas se)
  , ("equations",       prettyEqStore $ L.get sEqStore se)
  , ("solved formulas", foldr ($--$) emptyDoc $ map prettyGuarded $ S.toList $ L.get sSolvedFormulas se)
  , ("lemmas",          foldr ($--$) emptyDoc $ map prettyGuarded $ S.toList $ L.get sLemmas se)
  ]
  where
    combine (header, d)  = fsep [keyword_ header <> colon, nest 2 d]


-- Additional instances
-----------------------

deriving instance Show System

instance Apply CaseDistKind where
    apply = const id

instance HasFrees CaseDistKind where
    foldFrees = const mempty
    mapFrees  = const pure

instance HasFrees System where
    foldFrees fun (System a b c d e f g h i j k) =
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
        foldFrees fun k

    mapFrees fun (System a b c d e f g h i j k) =
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


$( derive makeBinary ''CaseDistKind)
$( derive makeBinary ''System)
$( derive makeBinary ''SystemTraceQuantifier)
$( derive makeBinary ''Goal)

$( derive makeNFData ''CaseDistKind)
$( derive makeNFData ''System)
$( derive makeNFData ''SystemTraceQuantifier)
$( derive makeNFData ''Goal)
