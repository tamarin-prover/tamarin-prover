{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable,
             TemplateHaskell, ViewPatterns
  #-}
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
  , Chain(..)
  , Less

  -- ** Pretty-printing
  , prettyNode
  , prettyNodePrem
  , prettyNodeConc
  , prettyEdge
  , prettyChain
  , prettyLess
  ) where

import           Prelude                          hiding ( (.), id )

import           Data.Binary
import           Data.DeriveTH
import           Data.Generics
import           Data.Monoid                      (Monoid(..))

import           Control.Basics
import           Control.DeepSeq

import           Text.PrettyPrint.Class

import           Theory.Constraint.System.Guarded
import           Theory.Model
import           Theory.Text.Pretty

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
  deriving (Show, Ord, Eq, Data, Typeable)

-- | A chain always starts at a rule with only one conclusion.
data Chain = Chain {
      cSrc :: NodeConc
    , cTgt :: NodePrem
    }
  deriving (Show, Ord, Eq, Data, Typeable)

-- | A *⋖* constraint between 'NodeId's.
type Less = (NodeId, NodeId)

-- Instances
------------

instance Apply Edge where
    apply subst (Edge from to) = Edge (apply subst from) (apply subst to)

instance Apply Chain where
    apply subst (Chain from to) = Chain (apply subst from) (apply subst to)

instance HasFrees Edge where
    foldFrees f (Edge x y) = foldFrees f x `mappend` foldFrees f y
    mapFrees  f (Edge x y) = Edge <$> mapFrees f x <*> mapFrees f y

instance HasFrees Chain where
    foldFrees f (Chain x y) = foldFrees f x `mappend` foldFrees f y
    mapFrees  f (Chain x y) = Chain <$> mapFrees f x <*> mapFrees f y


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

-- | Pretty print a chain as @src ~~> tgt@.
prettyChain :: HighlightDocument d => Chain -> d
prettyChain (Chain c p) =
    prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p

-- | Pretty print a less-atom as @src < tgt@.
prettyLess :: HighlightDocument d => Less -> d
prettyLess (i, j) = prettyNAtom $ Less (varTerm i) (varTerm j)

-- Derived instances
--------------------

$( derive makeBinary ''Chain)
$( derive makeBinary ''Edge)

$( derive makeNFData ''Chain)
$( derive makeNFData ''Edge)

