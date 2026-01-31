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
    , nIsCollapsed
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
    , collapseAdversaryClusters
  ) where

import           Extension.Data.Label
import qualified Theory.Constraint.System as Sys
import qualified Theory.Model             as M
import qualified Theory                   as Th
import qualified Data.Map                 as Map

import qualified Data.Set                 as S
import qualified Data.DAG.Simple          as Dag

import Data.Char (isDigit)
import Data.List.Split (splitOn)
import Data.List (intercalate, maximumBy)
import Data.Maybe
import Data.Ord (comparing)

-- | All nodes are identified by their NodeId.
-- Then we have different types of nodes depending on what data of the System they use.
data Node = Node {
    _nNodeId       :: M.NodeId,
    _nNodeType     :: NodeType,
    _nIsCollapsed  :: Bool  -- ^ True if this node represents a collapsed set of nodes
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
        bothInCluster (src, tgt) = src `S.member` nodeIds && tgt `S.member` nodeIds
    in filter (bothInCluster . edgeEndpoints) edges

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

----------------------------------------------------
-- Adversary cluster collapsing
----------------------------------------------------

-- | Check if a node represents an intruder/adversary rule
isIntruderNode :: Node -> Bool
isIntruderNode (Node _ (SystemNode ru) _) = Th.isIntruderRule ru
isIntruderNode _ = False

-- | Extract source and target node IDs from an edge
edgeEndpoints :: Edge -> (M.NodeId, M.NodeId)
edgeEndpoints (SystemEdge ((src, _), (tgt, _))) = (src, tgt)
edgeEndpoints (LessEdge (Th.LessAtom src tgt _)) = (src, tgt)
edgeEndpoints (UnsolvedChain ((src, _), (tgt, _))) = (src, tgt)

-- | Redirect an edge to a new target node
redirectEdge :: Edge -> M.NodeId -> Edge
redirectEdge (SystemEdge ((src, srcIdx), (_, tgtIdx))) newTgt = SystemEdge ((src, srcIdx), (newTgt, tgtIdx))
redirectEdge (LessEdge (Th.LessAtom src _ reason)) newTgt = LessEdge (Th.LessAtom src newTgt reason)
redirectEdge (UnsolvedChain ((src, srcIdx), (_, tgtIdx))) newTgt = UnsolvedChain ((src, srcIdx), (newTgt, tgtIdx))

-- | Find connected components using the connectivity predicate.
-- Two nodes are connected if one happens before the other in either direction.
connectedComponentsByPredicate :: (M.NodeId -> M.NodeId -> Bool) -> S.Set M.NodeId -> [S.Set M.NodeId]
connectedComponentsByPredicate isConnected allNodeIds = processNodes (S.toList allNodeIds) S.empty []
  where
    processNodes [] _ acc = acc
    processNodes (n:ns) visited acc
      | n `S.member` visited = processNodes ns visited acc
      | otherwise = 
          let component = findComponent [n] (S.singleton n)
          in processNodes ns (visited `S.union` component) (component : acc)
    
    findComponent [] visited = visited
    findComponent (n:queue) visited =
        let neighbors = filter (\m -> m `S.notMember` visited && isConnected n m) (S.toList allNodeIds)
        in findComponent (queue ++ neighbors) (visited `S.union` S.fromList neighbors)

-- | Extract adversary node IDs from a list of nodes
adversaryNodeIds :: [Node] -> S.Set M.NodeId
adversaryNodeIds nodes = S.fromList [get nNodeId n | n <- nodes, isIntruderNode n]

-- | Check if there is a non-adversary node (outside this cluster) that lies between two cluster nodes
hasIntermediateNonAdversary :: (M.NodeId -> M.NodeId -> Bool) -> S.Set M.NodeId -> [Node] -> Bool
hasIntermediateNonAdversary before cluster allNodes =
    let adversaryNodes = adversaryNodeIds allNodes
        nonClusterAdversary = adversaryNodes `S.difference` cluster
        clusterList = S.toList cluster
    in any (\(i, c1, c2) -> c1 `before` i && i `before` c2)
           [(i, c1, c2) | i <- S.toList nonClusterAdversary, c1 <- clusterList, c2 <- clusterList, c1 /= c2]

-- | Find the largest valid adversary cluster (matching original findAdversaryCluster)
findLargestAdversaryCluster :: (M.NodeId -> M.NodeId -> Bool) -> [Node] -> S.Set M.NodeId
findLargestAdversaryCluster before nodes =
    let validClusters = filter isValidCluster components
    in if null validClusters
       then S.empty
       else maximumBy (comparing S.size) validClusters
  where
    adversaryIds = adversaryNodeIds nodes
    isConnected n m = n `before` m || m `before` n
    components = connectedComponentsByPredicate isConnected adversaryIds
    isValidCluster cluster = not (hasIntermediateNonAdversary before cluster nodes)

-- | Get sink nodes within a cluster (nodes with no outgoing before edges to other cluster members)
getSinkNodes :: (M.NodeId -> M.NodeId -> Bool) -> S.Set M.NodeId -> S.Set M.NodeId
getSinkNodes before cluster =
    S.filter (\n -> not $ any (\m -> n `before` m && n /= m) (S.toList cluster)) cluster

-- | Get incoming edges from outside a cluster to inside it
getIncomingEdges :: S.Set M.NodeId -> [Edge] -> [Edge]
getIncomingEdges cluster edges = 
    filter (\e -> let (src, tgt) = edgeEndpoints e
                  in src `S.notMember` cluster && tgt `S.member` cluster) edges

-- | Update nodes by marking sinks as collapsed and removing internal non-sink nodes
updateNodesForCollapse :: S.Set M.NodeId -> S.Set M.NodeId -> [Node] -> [Node]
updateNodesForCollapse sinks nodesToRemove nodes =
    [if nodeId `S.member` sinks then set nIsCollapsed True n else n
     | n <- nodes, let nodeId = get nNodeId n, nodeId `S.notMember` nodesToRemove]

-- | Update edges by removing those involving removed nodes and adding redirected edges
updateEdgesForCollapse :: S.Set M.NodeId -> S.Set M.NodeId -> [Edge] -> [Edge] -> [Edge]
updateEdgesForCollapse sinks nodesToRemove currentEdges incomingEdges =
    let redirectedEdges = [redirectEdge e sinkId | e <- incomingEdges, sinkId <- S.toList sinks]
        edgeNotRemoved e = let (src, tgt) = edgeEndpoints e
                           in src `S.notMember` nodesToRemove && tgt `S.notMember` nodesToRemove
    in filter edgeNotRemoved currentEdges ++ redirectedEdges

-- | Collapse the largest adversary cluster once.
-- Returns the updated graph representation, or the original if no cluster can be collapsed.
-- When collapsing a subgraph into sink nodes, these are marked as collapsed nodes, which later helps us to render them in the right style.
collapseOneLargestAdversaryCluster :: GraphRepr -> GraphRepr
collapseOneLargestAdversaryCluster repr
    | S.null cluster = repr
    | S.null nodesToRemove = repr  -- No internal nodes to collapse
    | otherwise = set grNodes newNodes $ set grEdges newEdges repr
  where
    currentNodes = get grNodes repr
    currentEdges = get grEdges repr
    -- Build before predicate inline (only used here)
    before n1 n2 = n2 `S.member` Dag.reachableSet [n1] (map edgeEndpoints currentEdges)
    cluster = findLargestAdversaryCluster before currentNodes
    sinks = getSinkNodes before cluster
    nodesToRemove = cluster `S.difference` sinks
    incoming = getIncomingEdges cluster currentEdges
    newNodes = updateNodesForCollapse sinks nodesToRemove currentNodes
    newEdges = updateEdgesForCollapse sinks nodesToRemove currentEdges incoming

-- | Collapse all adversary clusters iteratively (matching original collapseAllAdversarySubgraphs).
-- Uses a greedy approach: Finds largest cluster, collapses it, then repeats until no more clusters can be collapsed.
-- I did not explore if there is a more optimal strategy that first computes all potential clusters, and then finds an optimal set of subgraphs to collapse. In practice, this should be sufficient.
collapseAdversaryClusters :: GraphRepr -> GraphRepr
collapseAdversaryClusters = until (\r -> collapseOneLargestAdversaryCluster r == r) collapseOneLargestAdversaryCluster
