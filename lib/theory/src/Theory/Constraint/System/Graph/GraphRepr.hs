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
    , getNodeAgent
    , getNodeName
    , groupNodesByAgent
    , addSubClustersByAgent
    , addIntelligentClusterWithSubClusters
    , extractBaseName
    , getRuleNameByNode
  ) where

import Debug.Trace
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



----------------------------------------------------
-- Clusturing by agent name 
----------------------------------------------------

extractAgent :: Th.RuleACInst -> String
extractAgent ru = case find isAgentAttribute (Th.ruleAttributes ru) of
  Just (Th.Agent agentName) -> agentName
  _                         -> "Unknown"

isAgentAttribute :: Th.RuleAttribute -> Bool
isAgentAttribute (Th.Agent _) = True
isAgentAttribute _            = False


groupNodesByAgent :: [Node] -> Map.Map String [Node]
groupNodesByAgent nodes = foldr groupByAgent Map.empty nodes
  where
    groupByAgent node acc = case getNodeAgent node of
      Just "Unknown" -> acc
      Just agent     -> Map.insertWith (++) agent [node] acc
      Nothing        -> acc


getNodeName :: Node -> String
getNodeName node = "node" ++ show (get nNodeId node)

getNodeAgent :: Node -> Maybe String
getNodeAgent node = case get nNodeType node of
  SystemNode ru -> Just (extractAgent ru)
  _             -> Nothing


-- Fonction pour créer un cluster à partir des nœuds d'un agent et des arêtes pertinentes
createCluster :: String -> [Node] -> [Edge] -> Cluster
createCluster agent nodes edges = Cluster agent nodes edges

-- Filtre les arêtes pour inclure uniquement celles pertinentes pour les nœuds d'un cluster
filterEdgesForCluster :: [Node] -> [Edge] -> [Edge]
filterEdgesForCluster nodes edges =
    let nodeIds = S.fromList (map (get nNodeId) nodes)
    in filter (\edge -> case edge of
                            SystemEdge ((srcNode, _), (tgtNode, _)) -> srcNode `S.member` nodeIds && tgtNode `S.member` nodeIds
                            UnsolvedChain ((srcNode, _), (tgtNode, _)) -> srcNode `S.member` nodeIds && tgtNode `S.member` nodeIds
                            LessEdge (srcNode, tgtNode, _) -> srcNode `S.member` nodeIds && tgtNode `S.member` nodeIds) edges

-- Fonction pour trouver les composants connectés internes à un cluster
findConnectedComponents :: [Node] -> [Edge] -> [[Node]]
findConnectedComponents nodes edges = go nodes []
  where
    -- Fonction récursive pour trouver tous les nœuds connectés à partir d'un nœud donné
    expandCluster :: Node -> S.Set Th.NodeId -> [Node] -> [Edge] -> S.Set Th.NodeId
    expandCluster node visited nodes edges =
      let nodeId = get nNodeId node
          connectedNodes = [ tgt | SystemEdge ((src, _), (tgt, _)) <- edges, src == nodeId, tgt `S.notMember` visited ] ++
                           [ src | SystemEdge ((src, _), (tgt, _)) <- edges, tgt == nodeId, src `S.notMember` visited ]
          newVisited = S.insert nodeId visited
      in foldr (\nid acc -> if nid `S.member` visited then acc else expandCluster (findNodeById nid nodes) newVisited nodes edges `S.union` acc) (S.singleton nodeId) connectedNodes

    findNodeById :: Th.NodeId -> [Node] -> Node
    findNodeById nodeId nodes = head $ filter (\n -> get nNodeId n == nodeId) nodes

    -- Fonction principale pour trouver tous les composants connectés
    go :: [Node] -> [[Node]] -> [[Node]]
    go [] components = components
    go (n:ns) components =
      let componentIds = S.toList $ expandCluster n S.empty (n:ns) edges
          component = filter (\node -> get nNodeId node `elem` componentIds) (n:ns)
          remainingNodes = filter (`notElem` component) ns
      in go remainingNodes (component : components)


-- Crée les sous-clusters d'un agent et les ajoute à GraphRepr
addSubClustersByAgent :: GraphRepr -> GraphRepr
addSubClustersByAgent repr =
    let nodesByAgent = groupNodesByAgent (get grNodes repr)
        edges = get grEdges repr
        createSubClusters agent nodes =
            let connectedComponents = findConnectedComponents nodes (filterEdgesForCluster nodes edges)
            in zipWith (\i component -> createCluster (agent ++ "_Session_" ++ show i) component (filterEdgesForCluster component edges)) [1..] connectedComponents
        subClusters = concatMap (\(agent, nodes) -> createSubClusters agent nodes) (Map.toList nodesByAgent)
        clusterEdges = concatMap (get cEdges) subClusters
        clusteredNodes = concatMap (get cNodes) subClusters
        remainingEdges = filter (`notElem` clusterEdges) edges
        remainingNodes = filter (`notElem` clusteredNodes) (get grNodes repr)
    in set grClusters subClusters $
       set grEdges remainingEdges $
       set grNodes remainingNodes repr


----------------------------------------------------
-- Clustering based on the name of the rules.
----------------------------------------------------


-- -- Function to get the rule name from a node
-- getRuleNameByNode :: Node -> Maybe String
-- getRuleNameByNode node = case _nNodeType node of
--     SystemNode ru -> Just (Th.showRuleCaseName ru)
--     _             -> Nothing

-- -- Function to extract the base name based on underscores
-- extractBaseName :: String -> Int -> String
-- extractBaseName name underscores = 
--     let parts = splitOn "_" name
--         baseName = intercalate "_" (take (length parts - underscores) parts)
--     in if null baseName then "Unknown" else baseName

-- -- Function to group nodes by similar rule names
-- groupBySimilarName :: [Node] -> Int -> Map.Map String [Node]
-- groupBySimilarName nodes underscores = 
--     foldr (\node acc -> 
--         let ruleName = fromMaybe "Unknown" (getRuleNameByNode node)
--             baseName = extractBaseName ruleName underscores
--         in if baseName == "Unknown"
--             then acc
--             else Map.insertWith (++) baseName [node] acc
--     ) Map.empty nodes

-- Function to add intelligent clusters with similar rule names to GraphRepr
addIntelligentClusterWithSubClusters :: GraphRepr -> GraphRepr
addIntelligentClusterWithSubClusters repr =
    let nodesBySimilarName = groupBySimilarName (get grNodes repr)
        edges = get grEdges repr
        createSubClusters name nodes =
            let connectedComponents = findConnectedComponents nodes (filterEdgesForCluster nodes edges)
            in zipWith (\i component -> createCluster (name ++ "_Session_" ++ show i) component (filterEdgesForCluster component edges)) [1..] connectedComponents
        subClusters = concatMap (\(name, nodes) -> createSubClusters name nodes) (Map.toList nodesBySimilarName)
        clusterEdges = concatMap (get cEdges) subClusters
        clusteredNodes = concatMap (get cNodes) subClusters
        remainingEdges = filter (`notElem` clusterEdges) edges
        remainingNodes = filter (`notElem` clusteredNodes) (get grNodes repr)
    in set grClusters subClusters $
       set grEdges remainingEdges $
       set grNodes remainingNodes repr


-- Function to get the rule name from a node
getRuleNameByNode :: Node -> Maybe String
getRuleNameByNode node = 
    let result = case _nNodeType node of
                    SystemNode ru -> case Th.ruleName ru of
                                       Th.ProtoInfo _ -> Just (Th.showRuleCaseName ru)
                                       _ -> Nothing
                    _ -> Nothing
    in trace ("getRuleNameByNode: " ++ show result) result


-- Function to extract the base name based on underscores
extractBaseName :: String -> String
extractBaseName name = 
    let parts = splitOn "_" name
        lastPart = last parts
        isNumber = all isDigit lastPart
        baseName = if isNumber && length parts > 1 
                   then intercalate "_" (init parts)
                   else "Unknown"
    in trace ("extractBaseName: " ++ show baseName) baseName

-- Function to group nodes by similar rule names
groupBySimilarName :: [Node] -> Map.Map String [Node]
groupBySimilarName nodes = 
    let result = foldr (\node acc -> 
                    let ruleName = fromMaybe "Unknown" (getRuleNameByNode node)
                        baseName = extractBaseName ruleName
                    in if baseName == "Unknown"
                        then acc
                        else Map.insertWith (++) baseName [node] acc
                ) Map.empty nodes
    in trace ("groupBySimilarName: " ++ show result) result