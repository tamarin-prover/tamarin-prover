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

module Text.Dot
        (
          -- * Dot
          Dot           -- abstract
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
        , cluster
          -- * HTML-like labeled nodes specification
        , HTMLLabel       -- abstract
        , cell
        , portHTMLCell
        , hcat
        , hcat'
        , vcat
        , vcat'
        , renderHTMLNode
          -- * HTML-like labeled construction
        , createPlainHTMLNode
        , createPlainHTMLNode'
        , createPlainHTMLNode_
        , createRoundedHTMLNode
        , createRoundedHTMLNode'
        , createRoundedHTMLNode_
        -- Utilities for formatting HTML-like labels

        , escape
        ) where

import Data.Char           (isSpace)
import Control.Monad       (ap)
-- import Control.Applicative (Applicative(..))

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

instance Functor Dot where
  fmap f m = Dot $ \ uq -> case unDot m uq of (a,b,x) -> (a,b,f x)

instance Applicative Dot where
  pure  = return
  (<*>) = ap

instance Monad Dot where
  return a = Dot $ \ uq -> ([],uq,a)
  m >>= k  = Dot $ \ uq -> case unDot m uq of
                           (g1,uq',r) -> case unDot (k r) uq' of
                                           (g2,uq2,r2) -> (g1 ++ g2,uq2,r2)

-- | 'rawNode' takes a list of attributes, generates a new node, and gives a 'NodeId'.
rawNode      :: [(String,String)] -> Dot NodeId
rawNode attrs = Dot $ \ uq ->
    let nid = NodeId $ "n" ++ show uq
    in ( [ GraphNode nid attrs ],succ uq,nid)

-- | 'node' takes a list of attributes, generates a new node, and gives a
-- 'NodeId'. Multi-line labels are fixed such that they use non-breaking
-- spaces and are terminated with a new-line.
node :: [(String,String)] -> Dot NodeId
node = rawNode . map fixLabel
  where
    fixLabel ("label",lbl) = ("label", fixMultiLineLabel lbl)
    fixLabel attr          = attr


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
showGraphElement (GraphAttribute name val) =
   showAttr (name,val) ++ ";"
showGraphElement (GraphNode nid attrs)            = show nid ++ showAttrs attrs ++ ";"
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
showAttr (name, val)
  | name == "label" = name ++ "=" ++ val
  | '<' `elem` val = name ++ "=" ++ concatMap escapeAttrVal val
  | otherwise = name ++ "=\"" ++ concatMap escapeAttrVal val ++ "\""
  where
      escapeAttrVal '\n' = "\\l"
      escapeAttrVal '"' = "\""
      escapeAttrVal c = [c]

-- | Ensure that multi-line labels use non-breaking spaces at the start and
-- are terminated with a newline.
fixMultiLineLabel :: String -> String
fixMultiLineLabel lbl
  | '\n' `elem` lbl = unlines $ map useNonBreakingSpace $ lines lbl
  | otherwise       = lbl
  where
    useNonBreakingSpace line = case span isSpace line of
      (spaces, rest) -> if length spaces > 1 then rest else concat (replicate (length spaces) "&nbsp;") ++ rest
      where
        emptyLine:: String -> Bool
        emptyLine = foldr ((&&) . isSpace) False


------------------------------------------------------------------------------
-- HTML-labels
------------------------------------------------------------------------------
-- | Specifies the construction of the cells of node with HTML-like labels; i.e., 
-- mentions all cells possibly together with ports and their horizontal and vertical nesting. 
--(see: HTML-like lables in the DOT documentation.)
data HTMLLabel a =
    Cell (Maybe a) String
  | HCat Int [HTMLLabel a]
  | VCat Int [HTMLLabel a]
  deriving(Eq, Ord, Show )

-- | Smart constructor for HTML-like labels so that DOT understands them.
makeHTMLLabel :: Maybe a -> String -> HTMLLabel a
makeHTMLLabel port = Cell port . fixMultiLineLabel 

-- | A simple cell content.
cell :: String -> HTMLLabel a
cell = makeHTMLLabel Nothing

-- | A cell together with a port which can be used to create direct edges to
-- this cell. Note that you can use any type to identify the ports. When
-- creating a node you will get back an association list between your
-- identifiers and their concrete node ids.
portHTMLCell :: a -> String -> HTMLLabel a
portHTMLCell port = makeHTMLLabel (Just port)

-- |  Concatenate cell contents horizontally and count how many cells does the structure include.
hcat :: [HTMLLabel a] -> HTMLLabel a
hcat xs = HCat (length xs) xs

-- | Concatenate a list strings interpreted as cell content horizontally.
hcat' :: [String] -> HTMLLabel a
hcat' = hcat . map cell

-- | Concatenate cell contents vertically and count how many cells does the structure include.
vcat :: [HTMLLabel a] -> HTMLLabel a
vcat xs = VCat (length xs) xs

-- | Concatenate a list strings interpreted as cell content vertically.
vcat' :: [String] -> HTMLLabel a
vcat' = vcat . map cell

-- | Render an HTML-like label in the Dot monad. It exploits the internal counter in
-- order to generate unique port-ids. However, they must be combined with the
-- actual node id of the node with. Thus the returned
-- association list is parametrized over this missing node id.
renderHTMLNode  :: String -> HTMLLabel a -> Dot (String, NodeId -> [(a,NodeId)])
renderHTMLNode = render True 1.0
  where
  -- render a node, we handle the "top level" rendering in a special way 
  render::Bool -> Float -> String -> HTMLLabel a -> Dot (String, NodeId -> [(a,NodeId)])
  render toplevel maxspan color (Cell Nothing l) = return (createHTMLTable toplevel ("<TD "++"BGCOLOR='"++color++"' COLSPAN='"++show maxspan++"'>"++escape l++"</TD>"), const [])
  render toplevel maxspan color (Cell (Just p) l)=
    Dot $ \uq -> let pid = "n" ++ show uq
                     lbl = createHTMLTable toplevel ("<TD "++"BGCOLOR='"++color++"' PORT='"++pid++"'"++ " COLSPAN='"++show maxspan++"'>"++escape l++"</TD>")
                 in  ([], succ uq, (lbl, \nId -> [(p,NodeId (show nId++":"++pid))]))
  render toplevel maxspan color (HCat n rs) = do
    (lbls, ids) <- unzip <$> mapM (render False (maxspan/(fromInteger (toInteger n) :: Float)) color) rs
    let rawLbl = concat lbls
        lbl = createHTMLTable toplevel ("<TR>"++rawLbl++"</TR>")
    return (lbl, \nId -> concatMap (\i -> i nId) ids)
  render toplevel _ color (VCat _ rs) =
    do
    let maxspan = getRowsMaxCells rs
    (lbls, ids) <- unzip <$> mapM (render False maxspan color) rs
    let rawLbl = concat lbls
        lbl = createHTMLTable toplevel rawLbl
    return (lbl, \nId -> concatMap (\i -> i nId) ids)

  -- create a formatted HTML table from a string if needed
  createHTMLTable True s = "<<TABLE BORDER='0' CELLBORDER='1' CELLSPACING='0' COLUMNS='*' ALIGN='CENTER'>"++s++"</TABLE>>"
  createHTMLTable False s = s

  -- get the number of cells in a row
  cellsInARow (HCat n _) = n
  cellsInARow (Cell _ _) = 1
  cellsInARow _ = error "Tried to use cellsInARow on a column/some columns!"

  -- get the number of cells in the row/column with the most cells
  getRowsMaxCells xs = fromInteger (toInteger (maximum $ map cellsInARow xs)) :: Float


-- escape chars that interfere with HTML tags
escape::[Char]->[Char]
escape ('<':'s':'u':'b':'>':xs) = '<':'s':'u':'b':'>':escape xs
escape ('<':'/':'s':'u':'b':'>':xs) = '<':'/':'s':'u':'b':'>':escape xs
escape ('<':xs) = "&lt;"++escape xs;
escape ('>':xs) = "&gt;"++escape xs;
escape (x:xs) = x:escape xs;
escape [] = [];


-- | A generic version of a node with an HTML-like label.
genHTMLNode :: String -> HTMLLabel a -> String -> [(String,String)] -> Dot (NodeId, [(a,NodeId)])
genHTMLNode  shape  nodeContent color attrs = do
  (lbl, ids) <- renderHTMLNode color nodeContent
  i <- rawNode ([("shape",shape),("label",lbl)] ++ attrs)
  return (i, ids i)

-- | Create a node with the given attributes. It returns the node-id of
-- the created node together with an association list mapping the port
-- idenfiers given in the node to their corresponding node-ids. This list is
-- ordered according to a left-to-rigth traversal of the node description.
createPlainHTMLNode :: HTMLLabel a -> String -> [(String,String)] -> Dot (NodeId, [(a,NodeId)])
createPlainHTMLNode = genHTMLNode "plaintext"

-- | A variant of a node ignoring the port identifiers.
createPlainHTMLNode' :: HTMLLabel a -> String -> [(String,String)] -> Dot (NodeId, [NodeId])
createPlainHTMLNode' lbls color attrs = do (nId, ids) <- createPlainHTMLNode lbls color attrs
                                           return (nId, map snd ids)

-- | A variant of node creation ignoring the port to node-id association list.
createPlainHTMLNode_:: HTMLLabel a -> String ->[(String,String)] -> Dot NodeId
createPlainHTMLNode_ lbls color attrs = fst <$> createPlainHTMLNode lbls color attrs

-- | Like "createPlainNode", but creates nodes with rounded corners; i.e. uses
-- the "rounded" shape instead of the "plaintext" shape.
createRoundedHTMLNode ::  HTMLLabel a -> String -> [(String,String)] -> Dot (NodeId, [(a,NodeId)])
createRoundedHTMLNode = genHTMLNode "rounded"

-- | A variant of "createRoundedNode" ignoring the port identifiers.
createRoundedHTMLNode' :: HTMLLabel a -> String -> [(String,String)] -> Dot (NodeId, [NodeId])
createRoundedHTMLNode' lbls color attrs = do (nId, ids) <- createRoundedHTMLNode lbls color  attrs
                                             return (nId, map snd ids)

-- | A variant of "createRoundedNode" ignoring the port to node-id association list.
createRoundedHTMLNode_ :: HTMLLabel a -> String -> [(String,String)] -> Dot NodeId
createRoundedHTMLNode_ lbls color attrs = fst <$> createRoundedHTMLNode lbls color attrs