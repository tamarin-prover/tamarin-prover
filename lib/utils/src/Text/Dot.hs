-- |
-- Module: Text.Dot
-- Copyright: Andy Gill, Simon Meier (extension to record syntax)
-- License: BSD3
--
-- Maintainer: Andy Gill <andygill@ku.edu>
-- Stability: unstable
-- Portability: portable
--
-- This module provides a simple interface for building .dot graph files, for input into the dot and graphviz tools.
-- It includes a monadic interface for building graphs.
{-# LANGUAGE TemplateHaskell #-}

module Text.Dot
        (
          -- * Dot
          Dot           -- abstract
        , runDot
        , DotGenState(..)
        , addElements
          -- * Nodes
        , node
        , NodeId        -- abstract
        , userNodeId
        , userNode
          -- * Edges
        , edge
          -- * Showing a graph
        , showDot
          -- * Other combinators
        , scope
        , attribute
        , nodeAttributes
        , edgeAttributes
        , graphAttributes
        , share
        , same
        , createClusterNodeId 
        , cluster
        , createSubGraph
          -- * Record construction
        , rawNode
          -- * Record specification
        , Record       -- abstract
        , field
        , portField
        , hcat
        , hcat'
        , vcat
        , vcat'
          -- * Record node construction
        , record
        , record'
        , record_

        , mrecord
        , mrecord'
        , mrecord_

          -- * Html labels.
        , htmlLabel
        , initializeDotGenState
        , modifyDotGenState
        , getDotGenStateElements
        , setId
        , nextId
        , module Data.GraphViz.Attributes.HTML
        , module Data.GraphViz.Attributes.Colors
        ) where

import Data.Char           (isSpace)
import Data.List           (intersperse)
import qualified Data.Text.Lazy as T
import Control.Monad       (liftM)
import Control.Monad.State (State, runState)
import Extension.Data.Label
import Data.GraphViz.Printing (renderDot, unqtDot)
import Data.GraphViz.Attributes.HTML
import Data.GraphViz.Attributes.Colors
import Data.GraphViz (GraphvizCommand(Dot), DotRepr (setID))

-- | Identifier for a node in a dot file.
data NodeId = NodeId String
            | UserNodeId Int

instance Show NodeId where
  show (NodeId str) = str
  show (UserNodeId i)
        | i < 0     = "u_" ++ show (negate i)
        | otherwise = "u" ++ show i

-- | The types of graph elements present in a dot file.
data GraphElement = GraphAttribute String String              -- ^ Global attributes for nodes/edges.
                  | GraphNode NodeId        [(String,String)] -- ^ A node with attributes.
                  | GraphEdge NodeId NodeId [(String,String)] -- ^ An edge between two nodes with attributes.
                  | Scope           [GraphElement]            -- ^ A subgraph without a name used to logically group elements together.
                  | SubGraph (Maybe NodeId) [GraphElement]    -- ^ A subgraph with an optional name.
  deriving (Show)

-- | The state of the dot generator monad.
data DotGenState = DotGenState {
  _dgsId       :: Int,           -- ^ The current node id which is incremented for every statement that generates a node.
  _dgsElements :: [GraphElement] -- ^ The current list of generated elements.
}

$(mkLabels [''DotGenState])

-- | The monad for generating dot statements.
type Dot = State DotGenState
 
-- | Evaluating a dot generator expression.
runDot :: DotGenState -> Dot a -> (a, DotGenState)
runDot state dot = runState dot state

-- | Retrieving and incrementing the node id in the state.
nextId :: Dot Int
nextId = do
  uq <- getM dgsId
  () <- setM dgsId (succ uq)
  return uq

setId :: Int  -> Dot()
setId i = do 
  setM dgsId i

-- | Initialize DotGenState
initializeDotGenState :: DotGenState
initializeDotGenState = DotGenState { _dgsId = 0, _dgsElements = [] }

-- | Modify DotGenState
modifyDotGenState :: Dot a -> DotGenState -> DotGenState
modifyDotGenState action state = snd (runDot state action)

-- | Get elements from DotGenState
getDotGenStateElements :: Dot [GraphElement]
getDotGenStateElements = getM dgsElements

createClusterNodeId :: String -> NodeId
createClusterNodeId agentName = NodeId ("cluster_" ++ agentName)
  
createSubGraph :: Maybe NodeId -> [GraphElement] -> GraphElement
createSubGraph = SubGraph

-- | Add elements to the dot state.
addElements :: [GraphElement] -> Dot ()
addElements elems = do
  modM dgsElements (++elems)

-- | 'rawNode' takes a list of attributes, generates a new node, and gives a 'NodeId'.
rawNode :: [(String, String)] -> Dot NodeId
rawNode attrs = do 
    uq <- nextId
    let nid = NodeId $ "n" ++ show uq
    addElements [GraphNode nid attrs]
    return nid


-- | 'node' takes a list of attributes, generates a new node, and gives a
-- 'NodeId'. Multi-line labels are fixed such that they use non-breaking
-- spaces and are terminated with a new-line.
node :: [(String,String)] -> Dot NodeId
node = rawNode . map fixLabel
  where
    fixLabel ("label",lbl) = ("label", fixMultiLineLabel lbl)
    fixLabel attr          = attr


-- | 'userNode' takes a NodeId, and adds some attributes to that node.
userNode :: NodeId -> [(String,String)] -> Dot ()
userNode nId attrs = addElements [GraphNode nId attrs ]

-- | 'edge' generates an edge between two 'NodeId's, with attributes.
edge      :: NodeId -> NodeId -> [(String,String)] -> Dot ()
edge  from to attrs = addElements [ GraphEdge from to attrs ]


-- | 'scope' groups a subgraph together; in dot these are the subgraphs inside "{" and "}".
scope     :: Dot a -> Dot a
scope dot = do 
  uq <- getM dgsId
  let subState = DotGenState { _dgsId = uq, _dgsElements = [] }
  let (a, finalState) = runDot subState dot
  setM dgsId (get dgsId finalState)
  addElements [SubGraph Nothing (get dgsElements finalState)]
  return a

-- | 'share' is when a set of nodes share specific attributes. Usually used for layout tweaking.
share :: [(String,String)] -> [NodeId] -> Dot ()
share attrs nodeids =
  let elems = [ Scope ( [ GraphAttribute name val | (name,val) <- attrs]
               ++ [ GraphNode nodeid [] | nodeid <- nodeids ]
               ) ] 
  in addElements elems

-- | 'same' provides a combinator for a common pattern; a set of 'NodeId's with the same rank.
same :: [NodeId] -> Dot ()
same = share [("rank","same")]


-- | 'cluster' builds an explicit, internally named subgraph (called cluster).
cluster :: Dot a -> Dot (NodeId,a)
cluster dot = do
  uq <- getM dgsId  
  let cid = NodeId $ "cluster_" ++ show uq
  let clusterState = DotGenState { _dgsId = succ uq, _dgsElements = [] }
  let (a, finalState) = runDot clusterState dot
  setM dgsId (get dgsId finalState)
  addElements [SubGraph (Just cid) (get dgsElements finalState)]
  return (cid, a)

-- | 'attribute' gives a attribute to the current scope.
attribute :: (String,String) -> Dot ()
attribute (name,val) = addElements [  GraphAttribute name val ]

-- | 'nodeAttributes' sets attributes for all the following nodes in the scope.
nodeAttributes :: [(String,String)] -> Dot ()
nodeAttributes attrs = addElements [ GraphNode (NodeId "node") attrs]

-- | 'edgeAttributes' sets attributes for all the following edges in the scope.
edgeAttributes :: [(String,String)] -> Dot ()
edgeAttributes attrs = addElements [ GraphNode (NodeId "edge") attrs]

-- | 'graphAttributes' sets attributes for current graph.
graphAttributes :: [(String,String)] -> Dot ()
graphAttributes attrs = addElements [ GraphNode (NodeId "graph") attrs]

-- 'showDot' renders a dot graph as a 'String' with the supplied label as the digraph id.
showDot :: String -> Dot a -> String
showDot label dot =
      -- We must escape all double quote characters in the graphviz label by using a backslash. 
      -- In the comparison we just use '"' because it is a single character.
      -- Then for the replacement we must use three \, the first two insert a literal backslash into the string, 
      -- the third one is used to insert a literal double quote into the string. 
  let escapedLabel = concatMap (\c -> if c == '"' then "\\\"" else [c]) label
      initialState = DotGenState { _dgsId = 0, _dgsElements = [] } 
      (_, finalState) = runDot initialState dot
      elems = get dgsElements finalState
  in 
    "digraph " ++ 
    "\"" ++ escapedLabel ++ "\"" ++
    " {\n" ++ unlines (map showGraphElement elems) ++ "\n}\n"

-- | Render a record in the Dot monad. It exploits the internal counter in
-- order to generate unique port-ids. However, they must be combined with the
-- actual node id of the node with the record shape. Thus the returned
-- association list is parametrized over this missing node id.
renderRecord :: Record a -> Dot (String, NodeId -> [(a,NodeId)])
renderRecord = render True
  where
  render _ (Field Nothing l) = return (escape l, const [])
  render _ (Field (Just p) l) = do
    uq <- nextId
    let pid = "n" ++ show uq
    let lbl = "<"++pid++"> "++escape l
    return (lbl, \nId -> [(p,NodeId (show nId++":"++pid))])
  render horiz (HCat rs) = do
    (lbls, ids) <- liftM unzip $ mapM (render True) rs
    let rawLbl = concat (intersperse "|" lbls)
        lbl = if horiz then "{{"++rawLbl++"}}" else "{"++rawLbl++"}"
    return (lbl, \nId -> concatMap (\i -> i nId) ids)
  render horiz (VCat rs) = do
    (lbls, ids) <- liftM unzip $ mapM (render False) rs
    let rawLbl = concat (intersperse "|" lbls)
        lbl = if horiz then "{"++rawLbl++"}" else "{{"++rawLbl++"}}"
    return (lbl, \nId -> concatMap (\i -> i nId) ids)
  -- escape chars used for record label construction
  escape = concatMap esc
  esc '|'  = "\\|"
  esc '{'  = "\\{"
  esc '}'  = "\\}"
  esc '<'  = "\\<"
  esc '>'  = "\\>"
  esc c    = [c]


-- | A generic version of record creation.
genRecord :: String -> Record a -> [(String,String)] -> Dot (NodeId, [(a,NodeId)])
genRecord shape rec attrs = do
  (lbl, ids) <- renderRecord rec
  i <- rawNode ([("shape",shape),("label",lbl)] ++ attrs)
  return (i, ids i)

-- | Create a record node with the given attributes. It returns the node-id of
-- the created node together with an association list mapping the port
-- idenfiers given in the record to their corresponding node-ids. This list is
-- ordered according to a left-to-rigth traversal of the record description.
record :: Record a -> [(String,String)] -> Dot (NodeId, [(a,NodeId)])
record = genRecord "record"

-- | A variant of "record" ignoring the port identifiers.
record' :: Record a -> [(String,String)] -> Dot (NodeId, [NodeId])
record' rec attrs = do (nId, ids) <- record rec attrs
                       return (nId, map snd ids)

-- | A variant of "record" ignoring the port to node-id association list.
record_ :: Record a -> [(String,String)] -> Dot NodeId
record_ rec attrs = liftM fst $ record rec attrs

-- | Like "record", but creates record nodes with rounded corners; i.e. uses
-- the \"Mrecord\" shape instead of the \"record\" shape.
mrecord :: Record a -> [(String,String)] -> Dot (NodeId, [(a,NodeId)])
mrecord = genRecord "Mrecord"

-- | A variant of "mrecord" ignoring the port identifiers.
mrecord' :: Record a -> [(String,String)] -> Dot (NodeId, [NodeId])
mrecord' rec attrs = do (nId, ids) <- mrecord rec attrs
                        return (nId, map snd ids)

-- | A variant of "mrecord" ignoring the port to node-id association list.
mrecord_ :: Record a -> [(String,String)] -> Dot NodeId
mrecord_ rec attrs = liftM fst $ mrecord rec attrs
  

-- | 'userNodeId' allows a user to use their own (Int-based) node id's, without needing to remap them.
userNodeId :: Int -> NodeId
userNodeId i = UserNodeId i


-- | Render a single graph element in dot format.
showGraphElement :: GraphElement -> String
showGraphElement (GraphAttribute name val) = showAttr (name,val) ++ ";"
showGraphElement (GraphNode nid attrs)           = show nid ++ showAttrs attrs ++ ";"
showGraphElement (GraphEdge from to attrs) = show from ++ " -> " ++ show to ++  showAttrs attrs ++ ";"
showGraphElement (Scope elems) = "{\n" ++ unlines (map showGraphElement elems) ++ "\n}"
showGraphElement (SubGraph Nothing elems) = "{\n" ++ unlines (map showGraphElement elems) ++ "\n}"
showGraphElement (SubGraph (Just nid) elems) = "subgraph " ++ show nid ++ " {\n" ++ unlines (map showGraphElement elems) ++ "\n}"

-- | Render attributes in dot format.
showAttrs :: [(String, String)] -> String
showAttrs [] = ""
showAttrs xs = "[" ++ showAttrs' xs ++ "]"
    where
        -- never empty list
        showAttrs' [a]    = showAttr a
        showAttrs' (a:as) = showAttr a ++ "," ++ showAttrs' as
        showAttrs' []     = error "showAttrs: the impossible happened"

-- | Render a single attribute. HTML labels are not escaped as they should contain valid graphviz HTML-like code.
showAttr :: (String, String) -> String
showAttr (name, val) 
  | name == "html_label" = "label=" ++ val
  | otherwise = name ++ "=\"" ++ concatMap escape val ++ "\""
    where
      escape '\n' = "\\l"
      escape '"'  = "\\\""
      escape c    = [c]

-- | Ensure that multi-line labels use non-breaking spaces at the start and
-- are terminated with a newline.
fixMultiLineLabel :: String -> String
fixMultiLineLabel lbl
  | '\n' `elem` lbl = unlines $ map useNonBreakingSpace $ lines lbl
  | otherwise       = lbl
  where
    useNonBreakingSpace line = case span isSpace line of
      (spaces, rest) -> concat (replicate (length spaces) "&nbsp;") ++ rest

------------------------------------------------------------------------------
-- Records
------------------------------------------------------------------------------

-- | Specifies the construction of a record; i.e., mentions all fields possibly
-- together with ports and their horizontal and vertical nesting. (see: record
-- shapes in the DOT documentation.)
data Record a =
    Field (Maybe a) String
  | HCat [Record a]
  | VCat [Record a]
  deriving( Eq, Ord, Show )

-- | Smart constructor for fields that massages the multi-line labels such
-- that dot understands them.
mkField :: Maybe a -> String -> Record a
mkField port = Field port . fixMultiLineLabel

-- | A simple field of a record.
field :: String -> Record a
field = mkField Nothing

-- | A field together with a port which can be used to create direct edges to
-- this field. Note that you can use any type to identify the ports. When
-- creating a record node you will get back an association list between your
-- record identifiers and their concrete node ids.
portField :: a -> String -> Record a
portField port = mkField (Just port)

-- | Concatenate records horizontally.
hcat :: [Record a] -> Record a
hcat = HCat

-- | Concatenate a list strings interpreted as simple fields horizontally.
hcat' :: [String] -> Record a
hcat' = hcat . map field

-- | Concatenate records vertically.
vcat :: [Record a] -> Record a
vcat = VCat

-- | Concatenate a list strings interpreted as simple fields vertically.
vcat' :: [String] -> Record a
vcat' = vcat . map field

---------------------------------------
-- HTML labels
---------------------------------------

-- Generate an html label attribute from a graphviz 'Label'.
htmlLabel :: Label -> (String, String)
htmlLabel label = 
  let rendered = T.unpack $ renderDot $ unqtDot label
      html = "<" ++ rendered ++ ">" in
  ("html_label", html)
