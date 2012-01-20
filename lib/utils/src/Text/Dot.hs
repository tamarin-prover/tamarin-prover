-- |
-- Module: Text.Dot
-- Copyright: Andy Gill
-- License: BSD3
--
-- Maintainer: Andy Gill <andygill@ku.edu>
-- Stability: unstable
-- Portability: portable
--
-- This module provides a simple interface for building .dot graph files, for input into the dot and graphviz tools. 
-- It includes a monadic interface for building graphs.

module Text.Dot 
	( 
	  -- * Dot
	  Dot		-- abstract
	  -- * Nodes
	, node
	, NodeId	-- abstract
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
	, cluster
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
	) where

import Data.List (intersperse)
import Control.Monad (liftM)

data NodeId = NodeId String
	    | UserNodeId Int

instance Show NodeId where
  show (NodeId str) = str
  show (UserNodeId i) 
	| i < 0     = "u_" ++ show (negate i)
	| otherwise = "u" ++ show i

data GraphElement = GraphAttribute String String
		  | GraphNode NodeId        [(String,String)]
		  | GraphEdge NodeId NodeId [(String,String)]
		  | Scope           [GraphElement]
		  | SubGraph NodeId [GraphElement]

data Dot a = Dot { unDot :: Int -> ([GraphElement],Int,a) }

instance Monad Dot where
  return a = Dot $ \ uq -> ([],uq,a)
  m >>= k  = Dot $ \ uq -> case unDot m uq of
			   (g1,uq',r) -> case unDot (k r) uq' of
					   (g2,uq2,r2) -> (g1 ++ g2,uq2,r2)

-- | 'node' takes a list of attributes, generates a new node, and gives a 'NodeId'.
node      :: [(String,String)] -> Dot NodeId
node attrs = Dot $ \ uq -> let nid = NodeId $ "n" ++ show uq 
			  in ( [ GraphNode nid attrs ],succ uq,nid)


-- | 'userNodeId' allows a user to use their own (Int-based) node id's, without needing to remap them.
userNodeId :: Int -> NodeId
userNodeId i = UserNodeId i

-- | 'userNode' takes a NodeId, and adds some attributes to that node. 
userNode :: NodeId -> [(String,String)] -> Dot ()
userNode nId attrs = Dot $ \ uq -> ( [GraphNode nId attrs ],uq,())

-- | 'edge' generates an edge between two 'NodeId's, with attributes.
edge      :: NodeId -> NodeId -> [(String,String)] -> Dot ()
edge  from to attrs = Dot (\ uq -> ( [ GraphEdge from to attrs ],uq,()))

-- | 'scope' groups a subgraph together; in dot these are the subgraphs inside "{" and "}".
scope     :: Dot a -> Dot a
scope (Dot fn) = Dot (\ uq -> case fn uq of
			      ( elems,uq',a) -> ([Scope elems],uq',a))

-- | 'share' is when a set of nodes share specific attributes. Usually used for layout tweaking.
share :: [(String,String)] -> [NodeId] -> Dot ()
share attrs nodeids = Dot $ \ uq -> 
      ( [ Scope ( [ GraphAttribute name val | (name,val) <- attrs]
	       ++ [ GraphNode nodeid [] | nodeid <- nodeids ]
	       ) 
        ], uq, ())

-- | 'same' provides a combinator for a common pattern; a set of 'NodeId's with the same rank.
same :: [NodeId] -> Dot ()
same = share [("rank","same")]


-- | 'cluster' builds an explicit, internally named subgraph (called cluster). 
cluster :: Dot a -> Dot (NodeId,a)
cluster (Dot fn) = Dot (\ uq -> 
		let cid = NodeId $ "cluster_" ++ show uq 
		in case fn (succ uq) of
		    (elems,uq',a) -> ([SubGraph cid elems],uq',(cid,a)))

-- | 'attribute' gives a attribute to the current scope.
attribute :: (String,String) -> Dot ()
attribute (name,val) = Dot (\ uq -> ( [  GraphAttribute name val ],uq,()))

-- | 'nodeAttributes' sets attributes for all the following nodes in the scope.
nodeAttributes :: [(String,String)] -> Dot ()
nodeAttributes attrs = Dot (\uq -> ([ GraphNode (NodeId "node") attrs],uq,()))

-- | 'edgeAttributes' sets attributes for all the following edges in the scope.
edgeAttributes :: [(String,String)] -> Dot ()
edgeAttributes attrs = Dot (\uq -> ([ GraphNode (NodeId "edge") attrs],uq,()))

-- | 'graphAttributes' sets attributes for current graph.
graphAttributes :: [(String,String)] -> Dot ()
graphAttributes attrs = Dot (\uq -> ([ GraphNode (NodeId "graph") attrs],uq,()))


-- 'showDot' renders a dot graph as a 'String'.
showDot :: Dot a -> String
showDot (Dot dm) = case dm 0 of
		    (elems,_,_) -> "digraph G {\n" ++ unlines (map showGraphElement elems) ++ "\n}\n"

showGraphElement :: GraphElement -> String
showGraphElement (GraphAttribute name val) = showAttr (name,val) ++ ";"
showGraphElement (GraphNode nid attrs)           = show nid ++ showAttrs attrs ++ ";"
showGraphElement (GraphEdge from to attrs) = show from ++ " -> " ++ show to ++  showAttrs attrs ++ ";"
showGraphElement (Scope elems) = "{\n" ++ unlines (map showGraphElement elems) ++ "\n}"
showGraphElement (SubGraph nid elems) = "subgraph " ++ show nid ++ " {\n" ++ unlines (map showGraphElement elems) ++ "\n}"

showAttrs :: [(String, String)] -> String
showAttrs [] = ""
showAttrs xs = "[" ++ showAttrs' xs ++ "]"
    where
	-- never empty list
	showAttrs' [a]    = showAttr a
	showAttrs' (a:as) = showAttr a ++ "," ++ showAttrs' as
        showAttrs' []     = error "showAttrs: the impossible happended"

showAttr :: (String, String) -> String
showAttr (name,val) = name ++ "=\"" ++ concatMap escape val ++ "\""
    where escape '\n' = "\\l"
	  escape '"'  = "\\\""
	  escape c    = [c]


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

-- | A simple field of a record.
field :: String -> Record a
field = Field Nothing

-- | A field together with a port which can be used to create direct edges to
-- this field. Note that you can use any type to identify the ports. When
-- creating a record node you will get back an association list between your
-- record identifiers and their concrete node ids.
portField :: a -> String -> Record a
portField port = Field (Just port)

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

-- | Render a record in the Dot monad. It exploits the internal counter in
-- order to generate unique port-ids. However, they must be combined with the
-- actual node id of the node with the record shape. Thus the returned
-- association list is parametrized over this missing node id.
renderRecord :: Record a -> Dot (String, NodeId -> [(a,NodeId)])
renderRecord = render True
  where
  render _ (Field Nothing l) = return (escape l, const [])
  render _ (Field (Just p) l) = 
    Dot $ \uq -> let pid = "n" ++ show uq
                     lbl = "<"++pid++"> "++escape l
		 in  ([], succ uq, (lbl, \nId -> [(p,NodeId (show nId++":"++pid))]))
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
  i <- node ([("shape",shape),("label",lbl)] ++ attrs)
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

