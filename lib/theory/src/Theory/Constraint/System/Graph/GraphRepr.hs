{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE ViewPatterns #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Representation of a graph as a collection of nodes, edges and clusters that can be used for rendering a System.
module Theory.Constraint.System.Graph.GraphRepr (
      GraphRepr
    , Node(..)
    , nNodeType
    , nNodeId
    , NodeType(..)
    , Edge(..)
    , Cluster(..)
    , cName
    , cNodes
    , cEdges
    , toEdgeList
  ) where

import           Extension.Data.Label
import qualified Theory.Constraint.System as Sys
import qualified Theory.Model             as M
import qualified Theory                   as Th
import Data.Maybe (mapMaybe)

-- | All nodes are identified by their NodeId.
-- Then we have different types of nodes depending on what data of the System they use.
data Node = Node {
    _nNodeId    :: M.NodeId,
    _nNodeType  :: NodeType
  }
  deriving( Eq, Ord, Show )

-- | Nodes can be rule instances, unsolved actions, missing (only applicable for sources), or last actions atoms (only applicable for induction).
data NodeType =
    SystemNode M.RuleACInst
  | UnsolvedActionNode [Th.LNFact]
  | LastActionAtom
  | MissingNode (Either Th.ConcIdx Th.PremIdx)
  deriving( Eq, Ord, Show )


-- | Edges can either transport facts from premises to conclusions, represent a temporal-before relationship, or be part of an unsolved chain between premises and conclusions.
data Edge =
    SystemEdge (Sys.NodeConc, Sys.NodePrem)
  | LessEdge (M.NodeId, M.NodeId, Sys.Reason)
  | UnsolvedChain (Sys.NodeConc, Sys.NodePrem)
  deriving( Eq, Ord, Show )

-- | A cluster contains nodes, edges, and a name, which is the common prefix of the contained nodes.
data Cluster = Cluster {
    _cName  :: String,
    _cNodes :: [Node],
    _cEdges :: [Edge]
  }
  deriving( Eq, Ord, Show )

$(mkLabels [''Node, ''Cluster])

-- | A graph consists of nodes, edges and clusters which are only one level deep to represent a collection of derivation rules with the same prefix.
type GraphRepr = ([Cluster], [Node], [Edge])

-- | Conversion function to a list of edges as used by Data.Graph.
toEdgeList :: GraphRepr -> [(Node, M.NodeId, [M.NodeId])]
toEdgeList (clusters, nodes, edges) = 
  let allNodes = nodes ++ concatMap (get cNodes) clusters 
      allEdges = edges ++ concatMap (get cEdges) clusters in
  map (\node -> (node, get nNodeId node, findSinkIndices allEdges node)) allNodes
  where
    -- | For each node, find all connected nodes using allEdges and return their NodeId's.
    findSinkIndices :: [Edge] -> Node -> [M.NodeId]
    findSinkIndices allEdges node = 
      let srcId = get nNodeId node in
      mapMaybe (findEdgeTarget srcId) allEdges
    
    -- | For a given source node id and an edge, check if the edge belongs to the node and return the target node id.
    findEdgeTarget :: M.NodeId -> Edge -> Maybe M.NodeId
    findEdgeTarget srcId (SystemEdge ((srcId', _), (tgtId, _)))    | srcId == srcId' = Just tgtId
    findEdgeTarget srcId (LessEdge (srcId', tgtId, _))             | srcId == srcId' = Just tgtId
    findEdgeTarget srcId (UnsolvedChain ((srcId', _), (tgtId, _))) | srcId == srcId' = Just tgtId
    findEdgeTarget _     _                                                           = Nothing
      