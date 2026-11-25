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
    , extractRole
    , getNodeRole
    , getNodeName
    , groupNodesByRole
    , addClusterByRole
    , addIntelligentClusterUsingSimilarNames
    , extractBaseName
    , getRuleNameByNode
  ) where

import           Extension.Data.Label
import qualified Theory.Constraint.System as Sys
import qualified Theory.Model             as M
import qualified Theory                   as Th
import qualified Data.Map                 as Map

import qualified Data.Set                 as S

import Data.Char (isDigit)
import Data.List.Split (splitOn)
import Data.List (find, intercalate)
import Data.Maybe

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
    SystemEdge (Sys.NodeConc, Sys.NodePrem)    -- ^ Edges that transport facts from premises to conclusions between rules.
  | LessEdge Th.LessAtom                       -- ^ Edges that represent a temporal-before relationship.
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
    findEdgeTarget srcId (LessEdge (Th.LessAtom srcId' tgtId _))   | srcId == srcId' = Just tgtId
    findEdgeTarget srcId (UnsolvedChain ((srcId', _), (tgtId, _))) | srcId == srcId' = Just tgtId
    findEdgeTarget _     _                                                           = Nothing


----------------------------------------------------
-- Clusturing
----------------------------------------------------

-- Function to add clusters to a GraphRepr
addCluster :: GraphRepr -> Map.Map String [Node] -> String -> GraphRepr
addCluster repr nodesByGroup nameSuffix =
    let edges = get grEdges repr
        createSubClusters name nodes =
            let connectedComponents = findConnectedComponents nodes (filterEdgesForCluster nodes edges)
            in zipWith (\i component -> createCluster (name ++ nameSuffix ++ show (i :: Integer)) component (filterEdgesForCluster component edges)) [1..] connectedComponents
        subClusters = concatMap (uncurry createSubClusters) (Map.toList nodesByGroup)
        clusterEdges = concatMap (get cEdges) subClusters
        clusteredNodes = concatMap (get cNodes) subClusters
        remainingEdges = filter (`notElem` clusterEdges) edges
        remainingNodes = filter (`notElem` clusteredNodes) (get grNodes repr)
    in set grClusters subClusters $
       set grEdges remainingEdges $
       set grNodes remainingNodes repr

----------------------------------------------------
-- Clusturing by role name
----------------------------------------------------

extractRole :: Th.RuleACInst -> Maybe String
extractRole ru = Th.role (Th.ruleAttributes ru)

groupNodesByRole :: [Node] -> Map.Map String [Node]
groupNodesByRole = foldr groupByRole Map.empty
  where
    groupByRole node acc = case getNodeRole node of
      Just role     -> Map.insertWith (++) role [node] acc
      Nothing        -> acc


getNodeName :: Node -> String
getNodeName node = "node" ++ show (get nNodeId node)

getNodeRole :: Node -> Maybe String
getNodeRole node = case get nNodeType node of
  SystemNode ru -> extractRole ru
  _             -> Nothing


-- Function to create a cluster from an role's nodes and relevant edges
createCluster :: String -> [Node] -> [Edge] -> Cluster
createCluster = Cluster

-- Filters edges to include only those relevant for the nodes of a cluster
filterEdgesForCluster :: [Node] -> [Edge] -> [Edge]
filterEdgesForCluster nodes edges =
    let nodeIds = S.fromList (map (get nNodeId) nodes)
    in filter (\edge -> case edge of
                            SystemEdge ((srcNode, _), (tgtNode, _)) -> srcNode `S.member` nodeIds && tgtNode `S.member` nodeIds
                            UnsolvedChain ((srcNode, _), (tgtNode, _)) -> srcNode `S.member` nodeIds && tgtNode `S.member` nodeIds
                            LessEdge (Th.LessAtom srcNode tgtNode _) -> srcNode `S.member` nodeIds && tgtNode `S.member` nodeIds) edges

-- Function to find the connected components within a cluster
findConnectedComponents :: [Node] -> [Edge] -> [[Node]]
findConnectedComponents nodes edges = go nodes []
  where
    -- Recursive function to find all nodes connected from a given node
    expandCluster :: Node -> S.Set Th.NodeId -> [Node] -> [Edge] -> S.Set Th.NodeId
    expandCluster node visited allNodes allEdges =
      let nodeId = get nNodeId node
          connectedNodes = [ tgt | SystemEdge ((src, _), (tgt, _)) <- allEdges, src == nodeId, tgt `S.notMember` visited ] ++
                           [ src | SystemEdge ((src, _), (tgt, _)) <- allEdges, tgt == nodeId, src `S.notMember` visited ]
          newVisited = S.insert nodeId visited
      in foldr (\nid acc -> if nid `S.member` visited then acc else expandCluster (findNodeById nid allNodes) newVisited allNodes allEdges `S.union` acc) (S.singleton nodeId) connectedNodes

    findNodeById :: Th.NodeId -> [Node] -> Node
    findNodeById nodeId allNodes = head $ filter (\n -> get nNodeId n == nodeId) allNodes

    -- Main function to find all connected components
    go :: [Node] -> [[Node]] -> [[Node]]
    go [] components = components
    go (n:ns) components =
      let componentIds = S.toList $ expandCluster n S.empty (n:ns) edges
          component = filter (\node -> get nNodeId node `elem` componentIds) (n:ns)
          remainingNodes = filter (`notElem` component) ns
      in go remainingNodes (component : components)


-- Function to add sub-clusters by role
addClusterByRole :: GraphRepr -> GraphRepr
addClusterByRole repr =
    let nodesByRole = groupNodesByRole (get grNodes repr)
    in addCluster repr nodesByRole "_Session_"



----------------------------------------------------
-- Clustering based on the name of the rules.
----------------------------------------------------

-- Function to get the rule name from a node
getRuleNameByNode :: Node -> Maybe String
getRuleNameByNode node =
    case _nNodeType node of
        SystemNode ru -> case Th.ruleName ru of
                           Th.ProtoInfo _ -> Just (Th.showRuleCaseName ru)
                           _ -> Nothing
        _ -> Nothing

-- Function to extract the base name based on underscores
extractBaseName :: String -> Maybe String
extractBaseName name =
    let parts = splitOn "_" name
        lastPart = last parts
        isNumber = all isDigit lastPart
        baseName = if isNumber && length parts > 1
                   then Just (intercalate "_" (init parts))
                   else Nothing
    in baseName

-- Function to group nodes by similar rule names
groupBySimilarName :: [Node] -> Map.Map String [Node]
groupBySimilarName nodes =
    let result = foldr (\node acc ->
                    case getRuleNameByNode node >>= extractBaseName of
                        Just baseName -> Map.insertWith (++) baseName [node] acc
                        Nothing       -> acc
                ) Map.empty nodes
    in result

-- Function to add intelligent clusters using similar rule names
addIntelligentClusterUsingSimilarNames :: GraphRepr -> GraphRepr
addIntelligentClusterUsingSimilarNames repr =
    let nodesBySimilarName = groupBySimilarName (get grNodes repr)
    in addCluster repr nodesBySimilarName "_Session_"
