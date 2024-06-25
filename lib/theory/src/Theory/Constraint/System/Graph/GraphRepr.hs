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
    , nodeIsAttackerDerivation
    , collapseNodes
    , Edge(..)
    , edgeSourceId
    , edgeTargetId
    , Cluster(..)
    , cName
    , cNodes
    , cEdges
    , toEdgeList
    , GraphAdjMap
    , toAdjMap
    , fromAdjMap
  ) where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty       as NE
import           Extension.Data.Label
import qualified Theory.Constraint.System as Sys
import qualified Theory                   as Th
import qualified Data.Map                 as M
import Data.Maybe (mapMaybe)

-- | All nodes are identified by their NodeId.
-- Then we have different types of nodes depending on what data of the System they use.
data Node = Node {
    _nNodeId    :: Th.NodeId,
    _nNodeType  :: NodeType
  }
  deriving( Eq, Ord, Show )

-- | Different types of graph nodes.
data NodeType =
    SystemNode Th.RuleACInst                   -- ^ Nodes from rule instances
  | UnsolvedActionNode [Th.LNFact]             -- ^ Nodes from unsolved adversary actions. 
  | LastActionAtom                             -- ^ Nodes that are only used for inductin.
  | MissingNode (Either Th.ConcIdx Th.PremIdx) -- ^ Nodes referenced by edges which don't exist elsewhere.
  | CollapseNode [Node]                        -- ^ A number of nodes that have been collapsed together. The nodeId in the containing 'Node' must be the id from a node in the list.
  deriving( Eq, Ord, Show )

-- | We classify those nodes resulting in an ellipsis in the dot rendering as attacker-derived.
-- a.d. TODO those rules might have to be more specific.
nodeIsAttackerDerivation :: Node -> Bool
nodeIsAttackerDerivation (Node _ (SystemNode ru)) 
  | (Th.isIntruderRule ru || Th.isFreshRule ru)          = True
nodeIsAttackerDerivation (Node _ (UnsolvedActionNode _)) = True
nodeIsAttackerDerivation _                               = False

-- | Different types of graph edges. 
data Edge =
    SystemEdge (Sys.NodeConc, Sys.NodePrem)    -- ^ Edges that transport facts from premises to conclusions between rules.
  | LessEdge Th.LessAtom                       -- ^ Edges that represent a temporal-before relationship.
  | UnsolvedChain (Sys.NodeConc, Sys.NodePrem) -- ^ Edges that are part of an unsolved chain between premises and conclusions.
  deriving( Eq, Ord, Show )

-- | For a given source node id and an edge, check if the edge belongs to the node and return the target node id.
edgeSourceId :: Edge -> Th.NodeId
edgeSourceId (SystemEdge ((srcId, _), _))    = srcId
edgeSourceId (LessEdge (srcId, _, _))        = srcId
edgeSourceId (UnsolvedChain ((srcId, _), _)) = srcId

edgeTargetId :: Edge -> Th.NodeId
edgeTargetId (SystemEdge (_, (tgtId, _)))    = tgtId
edgeTargetId (LessEdge (_, tgtId, _))        = tgtId
edgeTargetId (UnsolvedChain (_, (tgtId, _))) = tgtId
      

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

-- | Turn a nonempty list of nodes into a single collapsed node.
collapseNodes :: NonEmpty Node -> Node
collapseNodes (node :| nodes) = 
  let nodeId = get nNodeId node
      nodeType = CollapseNode (flattenNodes (node : nodes)) 
  in
    Node nodeId nodeType
  where
    -- | Flatten a collection of 'Node's.
    flattenNodes :: [Node] -> [Node]
    flattenNodes nodes = concatMap flattenNode nodes
    
    -- | Flatten a 'Node' by pulling out all the sub-nodes of a 'CollapseNode'.
    flattenNode :: Node -> [Node]
    flattenNode (Node _ (CollapseNode children)) = flattenNodes children
    flattenNode n = [n]


-- | Conversion function to a list of edges as used by Data.Graph.
toEdgeList :: GraphRepr -> [(Node, Th.NodeId, [Th.NodeId])]
toEdgeList repr = 
  let allNodes = get grNodes repr ++ concatMap (get cNodes) (get grClusters repr)
      allEdges = get grEdges repr ++ concatMap (get cEdges) (get grClusters repr) in
  map (\node -> (node, get nNodeId node, findSinkIndices allEdges node)) allNodes
  where
    -- | For each node, find all connected nodes using allEdges and return their NodeId's.
    findSinkIndices :: [Edge] -> Node -> [Th.NodeId]
    findSinkIndices allEdges node = 
      let srcId = get nNodeId node in
      mapMaybe (findEdgeTarget srcId) allEdges
    
    -- | For a given source node id and an edge, check if the edge belongs to the node and return the target node id.
    findEdgeTarget :: Th.NodeId -> Edge -> Maybe Th.NodeId
    findEdgeTarget srcId (SystemEdge ((srcId', _), (tgtId, _)))    | srcId == srcId' = Just tgtId
    findEdgeTarget srcId (LessEdge (Th.LessAtom srcId' tgtId _))   | srcId == srcId' = Just tgtId
    findEdgeTarget srcId (UnsolvedChain ((srcId', _), (tgtId, _))) | srcId == srcId' = Just tgtId
    findEdgeTarget _     _                                                           = Nothing

type GraphAdjMap = M.Map Th.NodeId (Node, [Edge])

-- | Note that this assumes that no clusters exist.
toAdjMap :: GraphRepr -> GraphAdjMap
toAdjMap repr =
  let allNodes = get grNodes repr
      allEdges = get grEdges repr
      adjMap = M.fromList $ map (\node -> (get nNodeId node, (node, filterEdges allEdges node))) allNodes
  in
    adjMap
  where
    -- | For each node, find all connected nodes using allEdges and return their NodeId's.
    filterEdges :: [Edge] -> Node -> [Edge]
    filterEdges allEdges node = 
      let srcId = get nNodeId node in
      mapMaybe (\edge -> if srcId == edgeSourceId edge then Just edge else Nothing) allEdges

fromAdjMap :: GraphAdjMap -> GraphRepr
fromAdjMap adjMap = 
  let (nodes, edges) = unzip $ M.elems adjMap in
  GraphRepr [] nodes (concat edges)