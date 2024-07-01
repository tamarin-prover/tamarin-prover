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
      GraphRepr(..)
    , grNodes
    , grClusters
    , grEdges
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
    , extractAgent
    , isAgentAttribute
  ) where

import           Extension.Data.Label
import qualified Theory.Constraint.System as Sys
import qualified Theory.Model             as M
import qualified Theory                   as Th
import Data.Maybe (mapMaybe)
import Data.List (find) -- Ajout de l'importation pour find
import qualified Data.Map as Map -- Ajout de l'importation pour Map

-- | All nodes are identified by their NodeId.
-- Then we have different types of nodes depending on what data of the System they use.
data Node = Node {
    _nNodeId    :: M.NodeId,
    _nNodeType  :: NodeType
  }
  deriving( Eq, Ord, Show )

-- | Different types of graph nodes.
data NodeType =
    SystemNode Th.RuleACInst                    -- ^ Nodes from rule instances
  | UnsolvedActionNode [Th.LNFact]             -- ^ Nodes from unsolved adversary actions. 
  | LastActionAtom                             -- ^ Nodes that are only used for induction.
  | MissingNode (Either Th.ConcIdx Th.PremIdx) -- ^ Nodes referenced by edges which don't exist elsewhere.
  deriving( Eq, Ord, Show )


-- | Different types of graph edges. 
data Edge =
    SystemEdge (Sys.NodeConc, Sys.NodePrem)    -- ^ Edges that transport facts from premises to conclusions entre rules.
  | LessEdge (M.NodeId, M.NodeId, Sys.Reason)  -- ^ Edges that represent a temporal-before relationship.
  | UnsolvedChain (Sys.NodeConc, Sys.NodePrem) -- ^ Edges that are part of an unsolved chain between premises and conclusions.
  deriving( Eq, Ord, Show )

-- | A cluster contains nodes, edges, and a name, which is the common prefix of the contained nodes.
data Cluster = Cluster {
    _cName  :: String
  , _cNodes :: [Node]
  , _cEdges :: [Edge]
  }
  deriving( Eq, Ord, Show )

-- | A graph consists of nodes, edges and clusters which are only one level deep to represent a collection of derivation rules with the same prefix.
data GraphRepr = GraphRepr {
    _grClusters :: [Cluster]
  , _grNodes    :: [Node]
  , _grEdges    :: [Edge]
  }
  deriving ( Eq, Ord, Show )

$(mkLabels [''GraphRepr, ''Node, ''Cluster])

extractAgent :: Th.RuleACInst -> String
extractAgent ru = case find isAgentAttribute (Th.ruleAttributes ru) of
  Just (Th.Agent agentName) -> agentName
  _                         -> "Unknown"

isAgentAttribute :: Th.RuleAttribute -> Bool
isAgentAttribute (Th.Agent _) = True
isAgentAttribute _            = False

-- | Conversion function to a list of edges as used by Data.Graph.
toEdgeList :: GraphRepr -> [(Node, M.NodeId, [M.NodeId])]
toEdgeList repr = 
  let allNodes = get grNodes repr ++ concatMap (get cNodes) (get grClusters repr)
      allEdges = get grEdges repr ++ concatMap (get cEdges) (get grClusters repr) in
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
