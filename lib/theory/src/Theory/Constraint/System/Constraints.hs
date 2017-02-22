{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveAnyClass     #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Types representing constraints.
module Theory.Constraint.System.Constraints (
  -- * Guarded formulas
    module Theory.Constraint.System.Guarded

  -- * Graph constraints
  , NodePrem
  , NodeConc
  , Edge(..)
  , Less

  -- * Goal constraints
  , Goal(..)
  , isActionGoal
  , isStandardActionGoal
  , isPremiseGoal
  , isChainGoal
  , isSplitGoal
  , isDisjGoal

  -- ** Pretty-printing
  , prettyNode
  , prettyNodePrem
  , prettyNodeConc
  , prettyEdge
  , prettyLess
  , prettyGoal
  ) where
import           GHC.Generics (Generic)
import           Data.Binary
import           Data.Data
-- import           Extension.Data.Monoid            (Monoid(..))

-- import           Control.Basics
import           Control.DeepSeq

import           Text.PrettyPrint.Class
import           Text.Unicode

import           Logic.Connectives
import           Theory.Constraint.System.Guarded
import           Theory.Model
import           Theory.Text.Pretty
import           Theory.Tools.EquationStore

------------------------------------------------------------------------------
-- Graph part of a sequent                                                  --
------------------------------------------------------------------------------

-- | A premise of a node.
type NodePrem = (NodeId, PremIdx)

-- | A conclusion of a node.
type NodeConc = (NodeId, ConcIdx)

-- | A labeled edge in a derivation graph.
data Edge = Edge {
      eSrc :: NodeConc
    , eTgt :: NodePrem
    }
  deriving (Show, Ord, Eq, Data, Typeable, Generic, NFData, Binary)

-- | A *⋖* constraint between 'NodeId's.
type Less = (NodeId, NodeId)

-- Instances
------------

instance Apply Edge where
    apply subst (Edge from to) = Edge (apply subst from) (apply subst to)

instance HasFrees Edge where
    foldFrees f (Edge x y) = foldFrees f x `mappend` foldFrees f y
    foldFreesOcc  f c (Edge x y) = foldFreesOcc f ("edge":c) (x, y)
    mapFrees  f (Edge x y) = Edge <$> mapFrees f x <*> mapFrees f y


------------------------------------------------------------------------------
-- Goals
------------------------------------------------------------------------------

-- | A 'Goal' denotes that a constraint reduction rule is applicable, which
-- might result in case splits. We either use a heuristic to decide what goal
-- to solve next or leave the choice to user (in case of the interactive UI).
data Goal =
       ActionG LVar LNFact
       -- ^ An action that must exist in the trace.
     | ChainG NodeConc NodePrem
       -- A destruction chain.
     | PremiseG NodePrem LNFact
       -- ^ A premise that must have an incoming direct edge.
     | SplitG SplitId
       -- ^ A case split over equalities.
     | DisjG (Disj LNGuarded)
       -- ^ A case split over a disjunction.
     deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- Indicators
-------------

isActionGoal :: Goal -> Bool
isActionGoal (ActionG _ _) = True
isActionGoal _             = False

isStandardActionGoal :: Goal -> Bool
isStandardActionGoal (ActionG _ fa) = not (isKUFact fa)
isStandardActionGoal _              = False

isPremiseGoal :: Goal -> Bool
isPremiseGoal (PremiseG _ _) = True
isPremiseGoal _              = False

isChainGoal :: Goal -> Bool
isChainGoal (ChainG _ _) = True
isChainGoal _            = False

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
        ActionG i fa  -> foldFrees f i <> foldFrees f fa
        PremiseG p fa -> foldFrees f p <> foldFrees f fa
        ChainG c p    -> foldFrees f c <> foldFrees f p
        SplitG i      -> foldFrees f i
        DisjG x       -> foldFrees f x

    foldFreesOcc  f c goal = case goal of
        ActionG i fa -> foldFreesOcc f ("ActionG":c) (i, fa)
        ChainG co p  -> foldFreesOcc f ("ChainG":c)  (co, p)
        _            -> mempty

    mapFrees f goal = case goal of
        ActionG i fa  -> ActionG  <$> mapFrees f i <*> mapFrees f fa
        PremiseG p fa -> PremiseG <$> mapFrees f p <*> mapFrees f fa
        ChainG c p    -> ChainG   <$> mapFrees f c <*> mapFrees f p
        SplitG i      -> SplitG   <$> mapFrees f i
        DisjG x       -> DisjG    <$> mapFrees f x

instance Apply Goal where
    apply subst goal = case goal of
        ActionG i fa  -> ActionG  (apply subst i) (apply subst fa)
        PremiseG p fa -> PremiseG (apply subst p) (apply subst fa)
        ChainG c p    -> ChainG   (apply subst c) (apply subst p)
        SplitG i      -> SplitG   (apply subst i)
        DisjG x       -> DisjG    (apply subst x)


------------------------------------------------------------------------------
-- Pretty printing                                                          --
------------------------------------------------------------------------------

-- | Pretty print a node.
prettyNode :: HighlightDocument d => (NodeId, RuleACInst) -> d
prettyNode (v,ru) = prettyNodeId v <> colon <-> prettyRuleACInst ru

-- | Pretty print a node conclusion.
prettyNodeConc :: HighlightDocument d => NodeConc -> d
prettyNodeConc (v, ConcIdx i) = parens (prettyNodeId v <> comma <-> int i)

-- | Pretty print a node premise.
prettyNodePrem :: HighlightDocument d => NodePrem -> d
prettyNodePrem (v, PremIdx i) = parens (prettyNodeId v <> comma <-> int i)

-- | Pretty print a edge as @src >-i--j-> tgt@.
prettyEdge :: HighlightDocument d => Edge -> d
prettyEdge (Edge c p) =
    prettyNodeConc c <-> operator_ ">-->" <-> prettyNodePrem p

-- | Pretty print a less-atom as @src < tgt@.
prettyLess :: HighlightDocument d => Less -> d
prettyLess (i, j) = prettyNAtom $ Less (varTerm i) (varTerm j)

-- | Pretty print a goal.
prettyGoal :: HighlightDocument d => Goal -> d
prettyGoal (ActionG i fa) = prettyNAtom (Action (varTerm i) fa)
prettyGoal (ChainG c p)   =
    prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p
prettyGoal (PremiseG (i, (PremIdx v)) fa) =
    -- Note that we can use "▷" for conclusions once we need them.
    prettyLNFact fa <-> text ("▶" ++ subscript (show v)) <-> prettyNodeId i
    -- prettyNodePrem p <> brackets (prettyLNFact fa)
prettyGoal (DisjG (Disj []))  = text "Disj" <-> operator_ "(⊥)"
prettyGoal (DisjG (Disj gfs)) = fsep $
    punctuate (operator_ "  ∥") (map (nest 1 . parens . prettyGuarded) gfs)
    -- punctuate (operator_ " |") (map (nest 1 . parens . prettyGuarded) gfs)
prettyGoal (SplitG x) =
    text "splitEqs" <> parens (text $ show (unSplitId x))

