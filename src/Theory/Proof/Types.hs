{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable, TemplateHaskell #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Common types for reasoning about sequents: Graph part of a sequent,
-- clauses, and equation store.
module Theory.Proof.Types (

  -- * Graph part of a sequent
    NodeId
  , NodePrem(..)
  , NodeConc(..)
  , Edge(..)
  , MsgEdge(..)
  , Chain(..)

  -- * The first-order logic part of a sequent


  -- ** Typing and equation store
  , SplitId

  , EqStore(..)
  , emptyEqStore
  , eqsSubst
  , eqsConj

  -- ** Equalitiy constraint conjunctions
  , falseEqConstrConj

  -- ** Queries
  , eqsIsFalse

  -- * Goals
  , Goal(..)

  -- * Keeping track of typing
  , CaseDistKind(..)

  -- * Sequents
  , Sequent(..)
  , emptySequent

  -- ** Accessors
  , sNodes
  , sEdges
  , sMsgEdges
  , sChains
  , sEqStore
  , sAtoms
  , sFormulas
  , sSolvedFormulas
  , sLemmas
  , sSubst
  , sConjDisjEqs 
  , sCaseDistKind

  -- ** Queries
  , sLessAtoms
  , sActionAtoms
  , sLastAtoms
  , sDedBeforeAtoms
  , sActions
  , sRawLessRel
  , sRawGreaterRel
  , deducibleBefore
  , happensBefore

  , nodeRule
  , nodeConcFact
  , nodeConcNode
  , nodePremNode
  , nodePremFact
  , resolveNodePremFact
  -- , resolveNodePremMsg
  , resolveNodeConcFact
  -- , resolveNodeConcMsg

  -- * Pretty-printing
  , prettyNodeId
  , prettyNode
  , prettyNodePrem
  , prettyNodeConc
  , prettyEdge
  , prettyMsgEdge
  , prettyChain

  , prettyEqStore

  , prettyGoal
  , prettySequent
  , prettyNonGraphSequent

  -- * Proof context
  , ProofContext(..)

  , pcSignature
  , pcRules
  , pcCaseDists


  -- ** Classified rules
  , ClassifiedRules(..)
  , emptyClassifiedRules
  , crConstruct
  , crDestruct
  , crProtocol
  , crSpecial
  , joinAllRules
  , joinNonSpecialRules
  , nonSilentRules

  -- ** Big-step case distinctions
  -- | See the module "Theory.Proof.CaseDistinction" for ways
  -- to construct case distinctions.
  , BigStepGoal(..)
  , CaseDistinction(..)
  
  , cdGoal
  , cdCases

  -- * Convenience exports
  , module Theory.Rule
  , module Theory.Formula
  , module Theory.Signature
  , module Logic.Connectives
  , module Theory.Proof.Guarded
  ) where

import Prelude hiding ( (.), id )

import Safe

import Data.Maybe (mapMaybe, fromMaybe)
import qualified Data.Set         as S
import qualified Data.Map         as M
import qualified Data.DAG.Simple  as D
import Data.Monoid (Monoid(..))
import Data.Generics
import Data.Label

import Control.Category
import Control.Basics

import Text.Isar

import Logic.Connectives

import Theory.Pretty
import Theory.Rule
import Theory.Proof.Guarded
import Theory.Formula
import Theory.Signature

------------------------------------------------------------------------------
-- Graph part of a sequent                                                  --
------------------------------------------------------------------------------

-- | The graph part of our sequent consists of nodes labelled with instances of
-- rules modulo AC. We identify these nodes using 'NodeId's.
type NodeId = LVar

-- | A premise (index) of a node.
newtype NodePrem = NodePrem { getNodePrem :: (NodeId, Int) }
   deriving( Eq, Ord, Show, Data, Typeable )

-- | A conclusion (index) of a node.
newtype NodeConc = NodeConc { getNodeConc :: (NodeId, Int) }
  deriving( Eq, Ord, Show, Data, Typeable )

-- | A labeled edge in a derivation graph.
data Edge = Edge {
      eSrc :: NodeConc
    , eTgt :: NodePrem
    }
  deriving (Show, Ord, Eq, Data, Typeable)

-- | A message edge.
data MsgEdge = MsgEdge {
      meSrc  :: NodeConc
    , meTgt  :: NodePrem
    }
  deriving (Show, Ord, Eq, Data, Typeable)

-- | A chain always starts at a rule with only one conclusion.
data Chain = Chain {
      cSrc :: NodeConc
    , cTgt :: NodePrem
    }
  deriving (Show, Ord, Eq, Data, Typeable)


-- Instances
------------

instance Apply NodePrem where
    apply subst = NodePrem . first (apply subst) . getNodePrem

instance Apply NodeConc where
    apply subst = NodeConc . first (apply subst) . getNodeConc

instance Apply Edge where
    apply subst (Edge from to) = Edge (apply subst from) (apply subst to)

instance Apply MsgEdge where
    apply subst (MsgEdge from to) = MsgEdge (apply subst from) (apply subst to)

instance Apply Chain where
    apply subst (Chain from to) = Chain (apply subst from) (apply subst to)

instance HasFrees NodePrem where
    foldFrees f = foldFrees f . fst . getNodePrem
    mapFrees f (NodePrem (v, i)) = 
        NodePrem <$> ((,) <$> mapFrees f v <*> pure i)

instance HasFrees NodeConc where
    foldFrees f = foldFrees f . fst . getNodeConc
    mapFrees f (NodeConc (v, i)) = 
        NodeConc <$> ((,) <$> mapFrees f v <*> pure i)

instance HasFrees Edge where
    foldFrees f (Edge x y) = foldFrees f x `mappend` foldFrees f y
    mapFrees  f (Edge x y) = Edge <$> mapFrees f x <*> mapFrees f y

instance HasFrees MsgEdge where
    foldFrees f (MsgEdge x y) = foldFrees f x `mappend` foldFrees f y
    mapFrees  f (MsgEdge x y) = MsgEdge <$> mapFrees f x <*> mapFrees f y

instance HasFrees Chain where
    foldFrees f (Chain x y) = foldFrees f x `mappend` foldFrees f y
    mapFrees  f (Chain x y) = Chain <$> mapFrees f x <*> mapFrees f y


------------------------------------------------------------------------------
-- The first-order logic part of a sequent                                  --
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Typing and equation store                                                --
------------------------------------------------------------------------------

-- | Index of disjunction in equation store
type SplitId = Int

-- FIXME: Make comment parse.
--
-- The semantics of an equation store
-- > EqStore sigma_free
-- >         [ [sigma_i1,..,sigma_ik_i] | i <- [1..l] ]
-- where sigma_free = {t1/x1, .., tk/xk} is
-- >    (x1 = t1 /\ .. /\ xk = tk)
-- > /\_{i in [1..l]}
-- >    ([|sigma_i1|] \/ .. \/ [|sigma_ik_1|] \/ [|mtinfo_i|]
-- where @[|{t_1/x_1,..,t_l/x_l}|] = EX vars(t1,..,tl). x_1 = t1 /\ .. /\ x_l = t_l@.
-- Note that the 'LVar's in the range of a substitution are interpreted as
-- fresh variables, i.e., different by construction from the x_i which are
-- free variables.
--
-- The variables in the domain of the substitutions sigma_ij and all
-- variables in sigma_free are free (usually globally existentially quantified).
-- We use Conj [] as a normal form to denote True and Conj [Disj []]
-- as a normal form to denote False.
-- We say a variable @x@ is constrained by a disjunction if there is a substition
-- @s@ in the disjunction with @x `elem` dom s@.
data EqStore = EqStore {
      _eqsSubst :: LNSubst
    , _eqsConj  :: Conj (Disj (LNSubstVFresh))
    }
  deriving( Eq, Ord )

$(mkLabels [''EqStore])

-- | @emptyEqStore@ is the empty equation store.
emptyEqStore :: EqStore
emptyEqStore = EqStore emptySubst (Conj [])

-- | @True@ iff the 'EqStore' is contradictory.
eqsIsFalse :: EqStore -> Bool
eqsIsFalse = (== falseEqConstrConj) . get eqsConj

-- | The false typing conjunction.
falseEqConstrConj :: Conj (Disj (LNSubstVFresh))
falseEqConstrConj = Conj [(Disj [])]


-- Instances
------------

instance HasFrees EqStore where
    foldFrees f (EqStore subst substs) = foldFrees f subst `mappend` foldFrees f substs
    mapFrees f (EqStore subst substs) = EqStore <$> mapFrees f subst <*> mapFrees f substs


------------------------------------------------------------------------------
-- New goaling infrastructure
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Goals
------------------------------------------------------------------------------

data Goal = 
       ActionG LVar LNFact       -- ^ Splitting over protocol rules
     | PremiseG NodePrem LNFact  -- ^ Splitting over all rules
     | PremDnKG NodePrem         -- ^ Chain and splitting over send concs
     | PremUpKG NodePrem LNTerm  -- ^ Splitting over construction rules
     | ChainG Chain              -- ^ Splitting over destruction rules
     | SplitG SplitId            -- ^ Splitting over equalities
     | DisjG (Disj LNGuarded)    -- ^ Splitting over a disjunction
     | ImplG LNGuarded           -- ^ Consequent of a universally quantified
                                 -- clause that could be added to the sequent.
     deriving( Eq, Ord, Show )

-- Instances
------------

instance HasFrees Goal where
    foldFrees f goal = case goal of
        ActionG i fa   -> foldFrees f i `mappend` foldFrees f fa
        PremiseG p fa  -> foldFrees f p `mappend` foldFrees f fa
        PremDnKG p     -> foldFrees f p
        PremUpKG p m   -> foldFrees f p `mappend` foldFrees f m
        ChainG ch      -> foldFrees f ch
        SplitG i       -> foldFrees f i
        DisjG x        -> foldFrees f x
        ImplG x        -> foldFrees f x

    mapFrees f goal = case goal of
        ActionG i fa   -> ActionG  <$> mapFrees f i <*> mapFrees f fa
        PremiseG p fa  -> PremiseG <$> mapFrees f p <*> mapFrees f fa
        PremDnKG p     -> PremDnKG <$> mapFrees f p
        PremUpKG p m   -> PremUpKG <$> mapFrees f p <*> mapFrees f m
        ChainG ch      -> ChainG   <$> mapFrees f ch
        SplitG i       -> SplitG   <$> mapFrees f i
        DisjG x        -> DisjG    <$> mapFrees f x
        ImplG x        -> ImplG    <$> mapFrees f x

instance Apply Goal where
    apply subst goal = case goal of
        ActionG i fa   -> ActionG  (apply subst i)     (apply subst fa)
        PremiseG p fa  -> PremiseG (apply subst p)     (apply subst fa)
        PremDnKG p     -> PremDnKG (apply subst p)    
        PremUpKG p m   -> PremUpKG (apply subst p)     (apply subst m)
        ChainG ch      -> ChainG   (apply subst ch)
        SplitG i       -> SplitG   (apply subst i)
        DisjG x        -> DisjG    (apply subst x)
        ImplG x        -> ImplG    (apply subst x)


------------------------------------------------------------------------------
-- Keeping track of what case distinctions are allowed.
------------------------------------------------------------------------------

-- | Case dinstinction kind that are allowed. The order of the kinds
-- corresponds to the subkinding relation: untyped < typed.
data CaseDistKind = UntypedCaseDist | TypedCaseDist
       deriving( Eq, Ord )

instance Show CaseDistKind where
    show UntypedCaseDist = "untyped"
    show TypedCaseDist   = "typed"


instance Apply CaseDistKind where
    apply = const id

instance HasFrees CaseDistKind where
    foldFrees = const mempty
    mapFrees  = const pure

------------------------------------------------------------------------------
-- Sequents                                                                 --
------------------------------------------------------------------------------

-- | A sequent / constraint system.
--
data Sequent = Sequent {
      _sNodes          :: M.Map NodeId RuleACInst
    , _sEdges          :: S.Set Edge
    , _sMsgEdges       :: S.Set MsgEdge
    , _sChains         :: S.Set Chain
    , _sEqStore        :: EqStore
    , _sAtoms          :: S.Set LNAtom
    , _sFormulas       :: S.Set LNGuarded
    , _sSolvedFormulas :: S.Set LNGuarded
    , _sLemmas         :: S.Set LNGuarded
    , _sCaseDistKind   :: CaseDistKind
    }
    deriving( Eq, Ord )

$(mkLabels [''Sequent])

-- | The empty sequent. Logically equivalent to true.
emptySequent :: CaseDistKind -> Sequent
emptySequent = Sequent 
  M.empty S.empty S.empty S.empty emptyEqStore S.empty S.empty S.empty S.empty

-- Custom accessors for atoms
-----------------------------

-- | All actions that hold in a sequent.
sActions :: Sequent -> [(NodeId, LNFact)]
sActions se = 
    sActionAtoms se <|> do (i, ru) <- M.toList $ get sNodes se
                           (,) i <$> get rActs ru

-- | The less-relation.
sLessAtoms :: Sequent -> [(NodeId, NodeId)]

-- | The actions.
sActionAtoms :: Sequent -> [(NodeId, LNFact)]

-- | The last nodes.
sLastAtoms :: Sequent -> [NodeId]

-- | The deduced before atoms.
sDedBeforeAtoms :: Sequent -> [(LNTerm, NodeId)]

(sLessAtoms, sActionAtoms, sLastAtoms, sDedBeforeAtoms) = 
    (accessor aLess, accessor aAction, accessor aLast, accessor aDedBefore)
  where
    accessor :: (LNAtom -> Maybe a) -> Sequent -> [a]
    accessor f = mapMaybe f . S.toList . get sAtoms

    malformed ato = error $ "malformed atom in sequent: " ++ show ato

    aLess (Less (Lit (Var from)) (Lit (Var to))) = Just (from, to)
    aLess ato@(Less _ _)                         = malformed ato
    aLess _                                      = Nothing

    aAction (Action (Lit (Var i)) fa) = Just (i, fa)
    aAction ato@(Action _ _)          = malformed ato
    aAction _                         = Nothing

    aLast (Last (Lit (Var i))) = Just i
    aLast ato@(Last _)         = malformed ato
    aLast _                    = Nothing

    aDedBefore (DedBefore t (Lit (Var i))) = Just (t, i)
    aDedBefore ato@(DedBefore _ _)         = malformed ato
    aDedBefore _                           = Nothing


-- | @(from,to)@ is in @sRawLessRel se@ iff we can prove that there is a path
-- from @from@ to @to@ in @se@ without appealing to transitivity.
sRawLessRel :: Sequent -> [(NodeId,NodeId)]
sRawLessRel se =
    sLessAtoms se ++
    map (nodeConcNode *** nodePremNode)
      ([ (from, to) | Edge from to <- S.toList $ get sEdges se ] ++
       [ (from, to) | MsgEdge from to <- S.toList $ get sMsgEdges se ] ++
       [ (from, to) | Chain from to <- S.toList $ get sChains se ])

-- | 'sRawGreaterRel' is the inverse of 'sRawLessRel'. 
sRawGreaterRel :: Sequent -> [(NodeId,NodeId)]
sRawGreaterRel = map (\(x,y) -> (y,x)) . sRawLessRel

-- | Returns a predicate that is 'True' iff the first argument happens before
-- the second argument in all models of the sequent.
happensBefore :: Sequent -> (NodeId -> NodeId -> Bool)
happensBefore se =
    check -- lessRel is cached for partial applications
  where
    lessRel   = sRawLessRel se
    check i j = j `S.member` D.reachableSet [i] lessRel

-- | Returns a predicate that is 'True' iff the given term is deducible
-- before the given node in all models of the sequent.
deducibleBefore :: Sequent -> (LNTerm -> NodeId -> Bool)
deducibleBefore se = 
    check -- lessRel is cached for partial applications
  where
    lessRel = sRawLessRel se
    check t i = 
        i `S.member` D.reachableSet startNodes lessRel
      where
        startNodes = 
            [ j | (t', j) <- sDedBeforeAtoms se, t == t' ] ++
            do (j, ru) <- M.toList $ get sNodes se
               fa <- get rPrems ru
               case kFactView fa of
                 Just (_, _, m) | t `elem` input m -> return j
                 _                                 -> []


-- Instances for sequents
-------------------------

instance HasFrees Sequent where
    foldFrees fun (Sequent a b c d e f g h i j) =
        foldFrees fun a `mappend`
        foldFrees fun b `mappend`
        foldFrees fun c `mappend`
        foldFrees fun d `mappend`
        foldFrees fun e `mappend`
        foldFrees fun f `mappend`
        foldFrees fun g `mappend`
        foldFrees fun h `mappend`
        foldFrees fun i `mappend`
        foldFrees fun j

    mapFrees fun (Sequent a b c d e f g h i j) =
        Sequent <$> mapFrees fun a
                <*> mapFrees fun b
                <*> mapFrees fun c
                <*> mapFrees fun d
                <*> mapFrees fun e
                <*> mapFrees fun f
                <*> mapFrees fun g
                <*> mapFrees fun h
                <*> mapFrees fun i
                <*> mapFrees fun j

-- Accessors
------------

-- | @nodeRule v@ accesses the rule label of node @v@ under the assumption that
-- it is present in the sequent.
nodeRule :: NodeId -> Sequent -> RuleACInst
nodeRule v se = 
    fromMaybe errMsg $ M.lookup v $ get sNodes se
  where
    errMsg = error $ 
        "nodeRule: node '" ++ show v ++ "' does not exist in sequent\n" ++
        render (nest 2 $ prettySequent se)


-- | @nodePremFact prem se@ computes the fact associated to premise @prem@ in
-- sequent @se@ under the assumption that premise @prem@ is a a premise in
-- @se@.
nodePremFact :: NodePrem -> Sequent -> LNFact
nodePremFact (NodePrem (v, i)) se = get (rPrem i) $ nodeRule v se

-- | @nodePremNode prem@ is the node that this premise is referring to.
nodePremNode :: NodePrem -> NodeId
nodePremNode (NodePrem (v, _)) = v

-- | All facts associated to this node premise.
resolveNodePremFact :: NodePrem -> Sequent -> Maybe LNFact
resolveNodePremFact (NodePrem (v, i)) se = 
    (`atMay` i) =<< get rPrems <$> M.lookup v (get sNodes se)

{-
-- | All msg fact premises required by the sequent for the given node premise.
resolveNodePremMsg :: NodePrem -> Sequent -> Maybe LTerm
resolveNodePremMsg prem = msgFactTerm <=< resolveNodePremFact prem
-}
    
-- | The fact associated with this node conclusion, if there is one.
resolveNodeConcFact :: NodeConc -> Sequent -> Maybe LNFact
resolveNodeConcFact (NodeConc (v, i)) se = 
    (`atMay` i) =<< get rConcs <$> M.lookup v (get sNodes se)

{-
-- | The msg fact provided by the sequent for the given node conclusion
resolveNodeConcMsg :: NodeConc -> Sequent -> Maybe LTerm
resolveNodeConcMsg conc = msgFactTerm <=< resolveNodeConcFact conc
-}

-- | @nodeConcFact (NodeConc (v, i))@ accesses the @i@-th conclusion of the
-- rule associated with node @v@ under the assumption that @v@ is labeled with
-- a rule that has an @i@-th conclusion.
nodeConcFact :: NodeConc -> Sequent -> LNFact
nodeConcFact (NodeConc (v, i)) = get (rConc i) . nodeRule v

-- | 'nodeConcNode' @c@ compute the node-id of the node conclusion @c@.
nodeConcNode :: NodeConc -> NodeId
nodeConcNode = fst . getNodeConc

-- | Label to access the free substitution of the equation store.
sSubst :: Sequent :-> LNSubst
sSubst = eqsSubst . sEqStore

-- | Label to access the conjunction of disjunctions of fresh substutitution in
-- the equation store.
sConjDisjEqs :: Sequent :-> Conj (Disj (LNSubstVFresh))
sConjDisjEqs = eqsConj . sEqStore


------------------------------------------------------------------------------
-- Pretty printing                                                          --
------------------------------------------------------------------------------

-- | Pretty print a node id
prettyNodeId :: Document d => NodeId -> d
prettyNodeId = text . show

-- | Pretty print a node.
prettyNode :: HighlightDocument d => (NodeId, RuleACInst) -> d
prettyNode (v,ru) = prettyNodeId v <> colon <-> prettyRuleACInst ru

-- | Pretty print a node conclusion.
prettyNodeConc :: HighlightDocument d => NodeConc -> d
prettyNodeConc (NodeConc (v, i)) = parens (prettyNodeId v <> comma <-> int i)

-- | Pretty print a node premise.
prettyNodePrem :: HighlightDocument d => NodePrem -> d
prettyNodePrem (NodePrem (v, i)) = parens (prettyNodeId v <> comma <-> int i)

-- | Pretty print a edge as @src >-i--j-> tgt@.
prettyEdge :: HighlightDocument d => Edge -> d
prettyEdge (Edge c p) = 
    prettyNodeConc c <-> operator_ ">-->" <-> prettyNodePrem p

-- | Pretty print a edge as @src >-i--j-> tgt@.
prettyMsgEdge :: HighlightDocument d => MsgEdge -> d
prettyMsgEdge (MsgEdge c p) = 
    prettyNodeConc c <-> operator_ "-->>" <-> prettyNodePrem p

-- | Pretty print a chain as @src ~~> tgt@.
prettyChain :: HighlightDocument d => Chain -> d
prettyChain (Chain c p) = 
    prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p

-- | Pretty print a sequent
prettySequent :: HighlightDocument d => Sequent -> d
prettySequent se = vcat $ 
    map combine
      [ ("nodes",     vcat $ map prettyNode $ M.toList $ get sNodes se)
      , ("edges",     commasep $ map prettyEdge $ S.toList $ get sEdges se)
      , ("msg-edges", commasep $ map prettyMsgEdge $ S.toList $ get sMsgEdges se)
      , ("chains",    commasep $ map prettyChain $ S.toList $ get sChains se)
      ]
    ++ [prettyNonGraphSequent se]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    commasep = fsep . punctuate comma

-- | Pretty print the non-graph part of the sequent; i.e. equation store and
-- clauses.
prettyNonGraphSequent :: HighlightDocument d => Sequent -> d
prettyNonGraphSequent se = foldr ($--$) emptyDoc $ map combine  
  [ ("atoms",           ppAtoms $ S.toList $ get sAtoms se)
  , ("allowed cases",   text $ show $ get sCaseDistKind se)
  , ("formulas",        foldr ($--$) emptyDoc $ map prettyGuarded $ S.toList $ get sFormulas se)
  , ("equations",       prettyEqStore $ get sEqStore se)
  , ("solved formulas", foldr ($--$) emptyDoc $ map prettyGuarded $ S.toList $ get sSolvedFormulas se)
  , ("lemmas",          foldr ($--$) emptyDoc $ map prettyGuarded $ S.toList $ get sLemmas se)
  ]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppAtoms             = fsep . punctuate comma . map prettyNAtom


-- | Pretty print an equation store
prettyEqStore :: HighlightDocument d => EqStore -> d
prettyEqStore eqs@(EqStore subst (Conj disjs)) = vcat $
  [if eqsIsFalse eqs then text "CONTRADICTORY" else emptyDoc] ++
  map combine
    [ ("subst", vcat $ prettySubst (text . show) (text . show) subst)
    , ("conj",  numbered' $ map ppDisj disjs)
    ]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppDisj (Disj substs) =
        numbered' conjs
      where 
        conjs = map ppConj substs
        ppConj = vcat . map prettyEq . substToListVFresh
        prettyEq (a,b) = 
          prettyNTerm (Lit (Var a)) $$ nest (6::Int) (opEqual <-> prettyNTerm b)
        
-- | Pretty print a goal.
prettyGoal :: HighlightDocument d => Goal -> d
prettyGoal (ActionG i fa)     = prettyNAtom (Action (varTerm i) fa)
prettyGoal (ChainG ch)        = prettyChain ch
prettyGoal (PremiseG p fa)    = prettyNodePrem p <> brackets (prettyLNFact fa)
prettyGoal (PremDnKG p)       = text "KD" <> parens (prettyNodePrem p)
prettyGoal (ImplG gf)         = 
    (text "Consequent" <>) $ nest 1 $ parens $ prettyGuarded gf
prettyGoal (DisjG (Disj gfs)) = (text "Disj" <>) $ fsep $
    punctuate (operator_ " |") (map (nest 1 . parens . prettyGuarded) gfs)
prettyGoal (PremUpKG p m)  =
    text "KU" <> parens (prettyNodePrem p <> comma <-> prettyLNTerm m)
prettyGoal (SplitG x) =
    text "splitEqs" <> parens (text $ show (succ x))

-- Additional Show instances moved here due to TemplateHaskell splicing rules
-----------------------------------------------------------------------------

instance Show EqStore where
  show = render . prettyEqStore

deriving instance Show Sequent

----------------------------------------------------------------------
-- ClassifiedRules
----------------------------------------------------------------------

data ClassifiedRules = ClassifiedRules
     { _crProtocol      :: [RuleAC] -- all protocol rules
     , _crDestruct      :: [RuleAC] -- destruction rules
     , _crConstruct     :: [RuleAC] -- construction rules
     , _crSpecial       :: [RuleAC] -- rules that are handled by other means
                                     -- than unification.
     }
     deriving( Eq, Ord, Show )

$(mkLabels [''ClassifiedRules])

-- | The empty proof rule set.
emptyClassifiedRules :: ClassifiedRules
emptyClassifiedRules = ClassifiedRules [] [] [] []

-- | @joinNonSpecialRules rules@ computes the union of all non-special @rules@.
joinNonSpecialRules :: ClassifiedRules -> [RuleAC]
joinNonSpecialRules (ClassifiedRules a b c _) = a ++ b ++ c

-- | @joinAllRules rules@ computes the union of all rules classified in
-- @rules@.
joinAllRules :: ClassifiedRules -> [RuleAC]
joinAllRules (ClassifiedRules a b c d) = a ++ b ++ c ++ d

-- | Extract all non-silent rules.
nonSilentRules :: ClassifiedRules -> [RuleAC]
nonSilentRules = filter (not . null . get rActs) . get crProtocol


------------------------------------------------------------------------------
-- Proof Context
------------------------------------------------------------------------------

-- | A goal for a big step case distinction.
data BigStepGoal = 
       PremiseBigStep LNFact
     | MessageBigStep LNTerm
     deriving( Eq, Ord, Show )

-- | A big-step case distinction.
data CaseDistinction = CaseDistinction
     { _cdGoal     :: BigStepGoal   -- start goal of case distinction
       -- disjunction of named sequents with premise being solved; each name
       -- being the path of proof steps required to arrive at these cases
     , _cdCases    :: Disj ([String], (NodeConc, Sequent))
     }
     deriving( Eq, Ord, Show )

-- | A proof context contains the globally fresh facts, classified rewrite
-- rules and the corresponding precomputed premise case distinction theorems.
data ProofContext = ProofContext 
       { _pcSignature  :: SignatureWithMaude
       , _pcRules      :: ClassifiedRules
       , _pcCaseDists  :: [CaseDistinction]
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''ProofContext, ''CaseDistinction])


-- Instances
------------

instance HasFrees CaseDistinction where
    foldFrees f th = 
        foldFrees f (get cdGoal th)   `mappend` 
        foldFrees f (get cdCases th)

    mapFrees f th = CaseDistinction <$> mapFrees f (get cdGoal th)
                                    <*> mapFrees f (get cdCases th)


-- Instances
------------

instance HasFrees BigStepGoal where
    foldFrees f (PremiseBigStep fa) = foldFrees f fa
    foldFrees f (MessageBigStep m)  = foldFrees f m

    mapFrees f (PremiseBigStep fa) = PremiseBigStep <$> mapFrees f fa
    mapFrees f (MessageBigStep m)  = MessageBigStep <$> mapFrees f m

instance Apply BigStepGoal where
    apply subst (PremiseBigStep fa) = PremiseBigStep (apply subst fa)
    apply subst (MessageBigStep m)  = MessageBigStep (apply subst m)

