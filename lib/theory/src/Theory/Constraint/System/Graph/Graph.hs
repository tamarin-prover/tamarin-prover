{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE ViewPatterns #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Abstraction over a System to represent certain components as a graph for rendering to a UI.
module Theory.Constraint.System.Graph.Graph (
      systemToGraph
    , SimplificationLevel(..)
    , levelNum
    , GraphOptions
    , goSimplificationLevel
    , goShowAutoSource
    , goClustering
    , goAbbreviate
    , goCompress
    , defaultGraphOptions
    , Graph
    , gRepr
    , gOptions
    , gAbbreviations
    , getGraphSinks
    , module Theory.Constraint.System.Graph.GraphRepr
    , module Theory.Constraint.System.Graph.Abbreviation
    , resolveNodeConcFact
    , resolveNodePremFact
  ) where

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty       as NE
import qualified Data.Map                 as M
import           Data.Maybe
import qualified Data.Set                 as S
import           Extension.Data.Label
import           Extension.Prelude        (collectBy)
import qualified Theory.Constraint.System as Sys
import           Theory.Constraint.System.Graph.GraphRepr
import           Theory.Constraint.System.Graph.Abbreviation
import qualified Theory                   as Th
import Theory.Constraint.System.Graph.Simplification (simplifySystem, compressSystem)

-- | The level of graph simplification.
data SimplificationLevel = SL0 | SL1 | SL2 | SL3
    deriving( Eq, Ord, Read, Show )

-- | Numberical representation of a 'SimplificationLevel'.
levelNum :: SimplificationLevel -> Int
levelNum SL0 = 0
levelNum SL1 = 1
levelNum SL2 = 2
levelNum SL3 = 3

-- | Options for the graph generation.
data GraphOptions = GraphOptions 
  { _goSimplificationLevel :: SimplificationLevel -- ^ The simplification level for simplifying the initial 'System'.
  , _goShowAutoSource      :: Bool                -- ^ Whether to show auto sources like "AUTO_xxx". a.d. TODO this maybe belongs in the DotOptions, not sure if auto source hiding is relevant for JSON.
  , _goClustering          :: Bool                -- ^ Whether to generate clusters of rules with common prefixes.
  , _goAbbreviate          :: Bool                -- ^ Whether to generate abbreviations.
  , _goCompress            :: Bool                -- ^ Whether to compress the initial 'System'.
  }
    deriving( Eq, Ord )

-- | The default options for graph generation.
defaultGraphOptions :: GraphOptions
defaultGraphOptions = GraphOptions 
  { _goSimplificationLevel = SL2
  , _goShowAutoSource = False
  , _goClustering = False
  , _goAbbreviate = True
  , _goCompress = True 
  }

-- | An abstract graph to derive visualiations of a 'System'.
data Graph = Graph 
  { _gSystem        :: Sys.System    -- ^ The backing 'System' instance.
  , _gOptions       :: GraphOptions  -- ^ The options which influence graph generation.
  , _gRepr          :: GraphRepr     -- ^ The actual representation in terms of nodes, edges & clusters.
  , _gAbbreviations :: Abbreviations -- ^ The map of generated abbreviations.
  }
    deriving( Eq, Ord )

$(mkLabels [''Graph, ''GraphOptions])

-- | All facts associated to this node premise.
resolveNodePremFact :: Sys.NodePrem -> Graph -> Maybe Th.LNFact
resolveNodePremFact prem graph = 
  let se = get gSystem graph in
  Sys.resolveNodePremFact prem se

-- | The fact associated with this node conclusion, if there is one.
resolveNodeConcFact :: Sys.NodeConc -> Graph -> Maybe Th.LNFact
resolveNodeConcFact conc graph = 
  let se = get gSystem graph in
  Sys.resolveNodeConcFact conc se

-- | Get all nodes from a 'System' corresponding to rule instances.
systemNodes :: Sys.System -> [Node]
systemNodes se = map systemNode (M.toList $ get Sys.sNodes se)
  where
    systemNode (nid, ru) = Node nid (SystemNode ru)

-- | Get all nodes from a 'System' corresponding to unsolved inputs by the adversary.
systemUnsolvedActionNodes :: Sys.System -> [Node]
systemUnsolvedActionNodes se = map unsolvedActionNode (collectBy $ Sys.unsolvedActionAtoms se)
  where
    unsolvedActionNode (nid, facts) = Node nid (UnsolvedActionNode facts)

-- | Get all nodes from a 'System' corresponding to an induction node.
systemLastActionNode :: Sys.System -> [Node]
systemLastActionNode se = maybe [] (\nid -> [Node nid LastActionAtom]) (get Sys.sLastAtom se)

-- | Get all nodes from a 'System' that are "missing", i.e. they are mentioned by an edge but don't exist elsewhere.
-- a.d. This assumes that there is no edge where both the source and target are missing. But that situation should never happen.
systemMissingNodes :: Sys.System -> [Node]
systemMissingNodes se = mapMaybe missingNode (S.toList $ get Sys.sEdges se)
  where
    missingNode (Sys.Edge (nid, idx) _) | nid `notElem` nodelist = Just $ Node nid (MissingNode (Left idx))
    missingNode (Sys.Edge _ (nid, idx)) | nid `notElem` nodelist = Just $ Node nid (MissingNode (Right idx))
    missingNode _ = Nothing
    nodelist = map fst $ M.toList $ get Sys.sNodes se

-- | Get all edges from a 'System' corresponding to edges between rule instances.
systemEdges :: Sys.System -> [Edge]
systemEdges se = 
  let edges = S.toList $ get Sys.sEdges se in
  map (\(Sys.Edge src tgt) -> SystemEdge (src, tgt)) edges

-- | Transform the graph representation to insert 'CollapseNode's which collect connected attacker derivation nodes.
-- This process is based on the cleandot python script and goes through all nodes in the graph, checks if they are an attacker node
-- and then converts them to a 'CollapseNode'. During this process, connected 'CollapseNode's are unified, so that for each connected
-- groups of attacker derivation nodes a single 'CollapseNode' remains in the final graph.
collapseDerivations :: GraphRepr -> GraphRepr
collapseDerivations repr = 
  let adjMap = toAdjMap repr
      newAdjMap = foldl findCollapseNode adjMap $ M.keys adjMap
      newRepr = fromAdjMap newAdjMap
  in
    newRepr
  where 
    findCollapseNode :: GraphAdjMap -> Th.NodeId -> GraphAdjMap
    findCollapseNode adjMap nodeId =
      let (currentNode, currentEdges) = adjMap M.! nodeId
          predecessors = M.keys $ M.filter (\(_, edges) -> any (\edge -> nodeId == edgeTargetId edge) edges) adjMap
          successors = M.keys $ M.filter (\(node, _) -> any (\edge -> get nNodeId node == edgeTargetId edge) currentEdges) adjMap
      in
        if nodeIsAttackerDerivation currentNode 
        && not (null predecessors)
        && not (null successors)
        then
          -- remove current node
          -- remove those successors that are collapseNodes
          -- remove those predecessors that are collapseNodes
          let removeSuccPredIds = filter (isCollapseNode adjMap) predecessors
                                  ++ filter (isCollapseNode adjMap) successors
              collapseEntries = adjMap M.! nodeId :| map (\k -> adjMap M.! k) removeSuccPredIds
              -- create a new collapseNode out of all removed nodes
              newCollapsedNode = collapseNodes (NE.map fst collapseEntries)
              -- also collect all the edges from the nodes that we collapsed
              unifiedEdges = concat $ NE.toList $ NE.map snd collapseEntries
              -- insert collapseNode
              newAdjMap = foldr (\(node, edges) m -> 
                                  let k = get nNodeId node in
                                  M.insert k (newCollapsedNode, unifiedEdges) m) adjMap collapseEntries
          in
          newAdjMap
        else
          adjMap
    
    isCollapseNode :: GraphAdjMap -> Th.NodeId -> Bool
    isCollapseNode adjMap nodeId =
      case get nNodeType $ fst (adjMap M.! nodeId) of
        CollapseNode _ -> True
        _              -> False

-- | Computes a basic graph representation from a System 
-- where nodes are 
-- 1. the System rule instances
-- 2. unsolved actions by the attacker
-- 3. a possible last action (for induction) 
-- 4. and any nodes that are required by edges but don't exist otherwise.
-- and edges are 
-- 1. edges between rule instances
-- 2. edges implied by less-constraints between temporal variables
-- 3. and any unsolved chains.
computeBasicGraphRepr :: Sys.System -> GraphRepr
computeBasicGraphRepr se = 
  let nodes = systemNodes se
        ++ systemUnsolvedActionNodes se
        ++ systemLastActionNode se
        ++ systemMissingNodes se
      edges =  systemEdges se 
        ++ map LessEdge (S.toList $ get Sys.sLessAtoms se)
        ++ map UnsolvedChain (Sys.unsolvedChains se)
  in 
    GraphRepr [] nodes edges

-- | Compute clusters, nodes & edges from a Graph instance according to the Graph's options.
systemToGraph :: Sys.System -> GraphOptions -> Graph
systemToGraph se options = 
  let -- We first do the existing simplification steps on a System that were defined in the Dot module originally.
      simplfiedSystem = simplifySystem (levelNum $ get goSimplificationLevel options) $
                          if get goCompress options then compressSystem se else se
      basicGraphRepr = computeBasicGraphRepr simplfiedSystem
      -- Iterate on the basicGraphRepr depending on what options are set to get the final repr
      repr1 = if (get goSimplificationLevel options >= SL3) then collapseDerivations basicGraphRepr else basicGraphRepr
      finalRepr = repr1
      abbrevs = computeAbbreviations finalRepr defaultAbbreviationOptions
  in
    Graph se options finalRepr abbrevs

-- | Get all sink nodes of a graph, i.e. those without outgoing edges.
getGraphSinks :: Graph -> [Node]
getGraphSinks graph = 
  let repr = get gRepr graph
      edgeList = toEdgeList repr in
  map (\(node, _, _) -> node) $ filter (\(_, _, outlist) -> null outlist) edgeList