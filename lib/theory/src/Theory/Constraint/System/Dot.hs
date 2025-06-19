{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Conversion of the graph part of a sequent to a Graphviz Dot file.
module Theory.Constraint.System.Dot (
    dotSystemCompact
  , BoringNodeStyle(..)
  , DotOptions
  , doNodeStyle
  , defaultDotOptions
  , SeDot
  ) where


import           Data.Ord
import           Data.Char                (isSpace, ord)
import           Data.Color
import           Data.List                (find, isPrefixOf, intercalate, sortBy, intersperse)
import qualified Data.Map                 as M
import           Data.Maybe
import qualified Data.Set                 as S
import           Data.Ratio
import qualified Data.Text.Lazy           as T
import           Extension.Data.Label
import           Extension.Prelude

import Text.Printf (printf)

import           Control.Basics
import qualified Control.Category         as L
import           Control.Monad.Reader
import           Control.Monad.State      (StateT, evalStateT, runStateT)
import qualified Control.Monad.State as State
import qualified Text.Dot                 as D

import Text.Dot                 (Attribute(..), Label(..), Table(..),
                                 Row(..), Align(..), VAlign(..), Cell(..), TextItem(..))
import Text.PrettyPrint.Class
    ( Document((<->), vcat, fsep, text),
      Doc,
      Style(lineLength, mode),
      Mode(OneLineMode),
      punctuate,
      comma,
      render,
      colon,
      brackets,
      renderStyle,
      defaultStyle )

import           Theory.Constraint.System hiding (Edge, resolveNodeConcFact, resolveNodePremFact)
import qualified Theory as Sys
import           Theory.Constraint.System.Graph.Graph
import           Theory.Model
import           Theory.Text.Pretty       (opAction)

import           Utils.Misc
import qualified Data.Graph               as G
import Theory (laSmaller, laLarger, laReason)


-- | The style for nodes of the intruder.
data BoringNodeStyle = FullBoringNodes | CompactBoringNodes
    deriving( Eq, Ord, Show )

-- | Options for dot generation.
data DotOptions = DotOptions
  { _doNodeStyle :: BoringNodeStyle -- ^ The style for nodes of the intruder.
  , _doAbbrevColor :: D.Color
  }
    deriving ( Eq, Ord, Show )

-- | The default dot options.
defaultDotOptions :: DotOptions
defaultDotOptions = DotOptions CompactBoringNodes black
  where
    black = D.RGB 0 0 0

$(mkLabels [''DotOptions])

type NodeColorMap = M.Map (RuleInfo ProtoRuleACInstInfo IntrRuleACInfo) (RGB Rational)
type SeDot = ReaderT (Graph, NodeColorMap, DotOptions) (StateT DotState D.Dot)

-- | State to track the dot NodeId (different from a System NodeId) of created dot components.
data DotState = DotState {
    _dsNodes   :: M.Map NodeId   D.NodeId
  , _dsPrems   :: M.Map NodePrem D.NodeId
  , _dsConcs   :: M.Map NodeConc D.NodeId
  -- a.d. TODO this is unused. Check if I droppped it somewhere, else delete.
  , _dsSingles :: M.Map (NodeConc, NodePrem) D.NodeId
  }

$(mkLabels [''DotState])

-- | Wrap a computation that generates dot components (SeDot) in order cache that component in the DotState and be able to retrieve its NodeId.
cacheState :: Ord k
           => (DotState :-> M.Map k D.NodeId) -- ^ Accessor to map storing this type of actions.
           -> k                               -- ^ Action index.
           -> SeDot D.NodeId
           -> SeDot ()
cacheState stateAccessor k dot = do
    i <- dot
    modM stateAccessor (M.insert k i)

-- | Retrieve a NodeId from a cached dot component.
getState :: Ord k
         => (DotState :-> M.Map k D.NodeId)
         -> k
         -> String
         -> SeDot D.NodeId
getState stateAccessor k msg = do
    stateMap <- getM stateAccessor
    let mi = stateMap M.!? k
    case mi of
      Nothing -> error msg
      Just i -> return i

-- | Lift a 'D.Dot' action.
liftDot :: D.Dot a -> SeDot a
liftDot = lift . lift

-- | Set default attributes for nodes and edges.
setDefaultAttributes :: D.Dot ()
setDefaultAttributes = do
  D.attribute ("nodesep","0.3")
  D.attribute ("ranksep","0.3")
  D.nodeAttributes [("fontsize","8"),("fontname","Helvetica"),("width","0.3"),("height","0.2")]
  D.edgeAttributes [("fontsize","8"),("fontname","Helvetica")]


-- | Set default attributes for nodes and edges if the graph contains clusters.
-- Some additional options have been added for better rendering
setDefaultAttributesIfCluster :: D.Dot ()
setDefaultAttributesIfCluster = do
  D.attribute ("nodesep", "0.8") -- Slight increase to space out the graph
  D.attribute ("ranksep", "0.8")
  D.attribute ("sep", "4")
  D.attribute ("splines", "true")
  D.attribute ("overlap", "false") -- Prevent nodes from overlapping
  D.attribute ("pack", "true") -- Enable packing of clusters to ensure they are tightly grouped.
  D.attribute ("packmode", "cluster") -- Define packing mode specifically for clusters to organize them more efficiently.
  D.attribute ("concentrate", "true") -- Combine parallel edges .
  D.attribute ("compound", "true")
  D.attribute ("remincross", "true") -- Minimize edge crossings to improve readability.
  D.attribute ("mclimit", "10")
  D.attribute ("nslimit", "20")
  D.attribute ("nslimit1", "20")
  D.attribute ("ordering", "out")
  D.attribute ("rankdir", "TB") -- Set the direction of ranks from top to bottom for a hierarchical layout.
  D.attribute ("showboxes", "false")
  D.attribute ("clusterrank", "local") -- Rank clusters locally to ensure internal cluster organization

  D.nodeAttributes [("fontsize", "8"), ("fontname", "Helvetica"), ("width", "0.3"), ("height", "0.2"), ("margin", "0.05,0.05"), ("shape", "ellipse")] -- Define default attributes for nodes with specific font and size settings.
  D.edgeAttributes [("fontsize", "8"), ("fontname", "Helvetica"), ("penwidth", "1.5"), ("arrowsize", "0.5"), ("color", "black"), ("style", "solid"), ("weight", "8")] -- Define default attributes for edges with specific font, size, and style settings.



-- | This function creates a cluster for a specific role with a list of nodes.
-- It takes an role name and a 'SeDot' action, then executing the given SeDot action within
--a temporary state, updating the current state, and adding the resulting subgraph elements to
--the global state.

-- Note: To be compatible with the 'dotNodeCompact' function which returns a 'SeDot' action,
-- we needed a function that accepts and returns a 'SeDot' action. This is why we didn't use
-- the 'cluster' function from 'Text.Dot'. The only feasible approach was either this or
-- fragmenting the 'dotNodeCompact' function. Thus, we extracted what we needed and removed
-- the unnecessary parts.
roleCluster :: String -> SeDot a -> SeDot ()
roleCluster roleName dot = do
  uq <- liftDot D.nextId
  let cid = D.createClusterNodeId roleName
  env <- ask
  currentState <- State.get
  let clusterState = D.DotGenState { D._dgsId = uq, D._dgsElements = [] }
  ((_, newState), finalDotState) <- lift . lift . lift $ runStateT (runStateT (runReaderT dot env) currentState) clusterState
  State.put newState
  _ <- liftDot $ D.setId $ D._dgsId finalDotState
  liftDot $ D.addElements [D.createSubGraph (Just cid) (D._dgsElements finalDotState)]


-- | Compute a color map for nodes labelled with a proof rule info of one of
-- the given rules.
nodeColorMap :: [RuleACInst] -> NodeColorMap
nodeColorMap rules =
    M.fromList $
      [ (get rInfo ru, getColorForRule (ruleAttributes ru) gIdx mIdx)
      | (gIdx, grp) <- groups, (mIdx, ru) <- zip [0..] grp ]
  where
    groupIdx ru
      | isDestrRule ru                   = 0
      | isConstrRule ru                  = 2
      | isFreshRule ru || isISendRule ru = 3
      | otherwise                        = 1

    -- groups of rules labeled with their index in the group
    groups = [ (gIdx, [ ru | ru <- rules, gIdx == groupIdx ru])
             | gIdx <- [0..3]
             ]

    -- color for each member of a group
    colors = M.fromList $ lightColorGroups intruderHue (map (length . snd) groups)
    getColor idx = fromMaybe (HSV 0 1 1) $ M.lookup idx colors

    -- Function to get color for a given rule
    getColorForRule attrs gIdx mIdx = fromMaybe defaultColor (ruleColor attrs)
        where
            defaultColor =  hsvToRGB $ getColor (gIdx, mIdx)

    -- The hue of the intruder rules
    intruderHue :: Rational
    intruderHue = 18 % 360

------------------------------------------------------------------------------
-- Record based dotting
------------------------------------------------------------------------------

-- | Render an LNFact using the abbreviations given by the graph.
renderLNFact :: Document d => LNFact -> SeDot d
renderLNFact fact = do
  (graph, _, _) <- ask
  let abbreviate = get ((L..) goAbbreviate gOptions) graph
      abbrevs = get gAbbreviations graph
      replacedFact = applyAbbreviationsFact (lookupAbbreviation abbrevs) fact
  if abbreviate
    then return $ prettyLNFact replacedFact
    else return $ prettyLNFact fact

-- | Dot a node in record based (compact) format.
dotNodeCompact :: Node -> Maybe String -> SeDot ()
dotNodeCompact node manualNodeColor = do
  let v = get nNodeId node
  (graph, colorMap, dotOptions) <- ask
  case get nNodeType node of
    SystemNode ru -> cacheState dsNodes v $ do
      let outgoingEdge = hasOutgoingEdge graph v
      let role = fromMaybe "Undefined" (getNodeRole node)

      let rInfoVal = get rInfo ru

      -- TODO this is pretty ugly. Shorten using standard functions
      let ruleColor' = case rInfoVal of
                        ProtoInfo protoRule ->
                          case ruleColor (_praciAttributes protoRule) of
                            Just rgb -> Just (rgbToHex rgb)
                            _ -> Nothing
                        _ -> Nothing

      let color = M.lookup rInfoVal colorMap
          nodeColor = fromMaybe (maybe "white" rgbToHex color) (ruleColor' <|> manualNodeColor)
          attrs = [("fillcolor", nodeColor), ("style", "filled")
                  , ("fontcolor", if colorUsesWhiteFont color then "white" else "black")
                  , ("role", role)]

      ids <- mkNode v ru attrs outgoingEdge dotOptions
      let prems = [ ((v, i), nid) | (Just (Left i),  nid) <- ids ]
          concs = [ ((v, i), nid) | (Just (Right i), nid) <- ids ]
      modM dsPrems $ M.union $ M.fromList prems
      modM dsConcs $ M.union $ M.fromList concs
      return $ fromJust $ lookup Nothing ids
    UnsolvedActionNode facts -> cacheState dsNodes v $ do
      lblPre <- (fsep <$> punctuate comma <$> mapM renderLNFact facts)
      let lbl = lblPre <-> opAction <-> text (show v)
      let attrs | any isKUFact facts = [("color","gray")]
                | otherwise          = [("color","darkblue")]
      mkSimpleNode (render lbl) attrs
    LastActionAtom -> cacheState dsNodes v $ mkSimpleNode (show v) []
    MissingNode (Left conc) -> cacheState dsConcs (v, conc) $ dotConcC (v, conc)
    MissingNode (Right prem) -> cacheState dsPrems (v, prem) $ dotPremC (v, prem)
  where
    hasOutgoingEdge graph v =
      let repr = get gRepr graph
      in or [ v == v' | SystemEdge ((v', _), _) <- get grEdges repr ]
    missingNode shape label = liftDot $ D.node $ [("label", render label),("shape",shape)]
    dotPremC prem = missingNode "invtrapezium" $ prettyNodePrem prem
    dotConcC conc = missingNode "trapezium" $ prettyNodeConc conc

    --True if there's a colour, and it's 'darker' than 0.5 in apparent luminosity
    --This assumes a linear colourspace, which is what graphviz seems to use
    colorUsesWhiteFont (Just (RGB r g b)) = (0.2126*r + 0.7152*g + 0.0722*b) < 0.5
    colorUsesWhiteFont _                  = False

    mkSimpleNode lbl attrs =
        liftDot $ D.node $ [("label", lbl),("shape","ellipse")] ++ attrs

    mkNode  :: NodeId -> RuleACInst -> [(String, String)] -> Bool -> DotOptions
      -> SeDot [(Maybe (Either PremIdx ConcIdx), D.NodeId)]
    mkNode v ru attrs outgoingEdge dotOptions
      -- single node, share node-id for all premises and conclusions
      | get doNodeStyle dotOptions == CompactBoringNodes &&
        (isIntruderRule ru || isFreshRule ru) = do
            ps <- psM
            as <- asM
            cs <- csM
            let lbl | outgoingEdge = show v ++ " : " ++ showDotRuleCaseName ru
                    | otherwise       = concatMap snd as
            nid <- mkSimpleNode lbl []
            return [ (key, nid) | (key, _) <- ps ++ as ++ cs ]
      -- full record syntax
      | otherwise = do
            ps <- psM
            as <- asM
            cs <- csM
            fmap snd $ liftDot $ (`D.record` attrs) $
              D.vcat $ map D.hcat $ map (map (uncurry D.portField)) $
              filter (not . null) [ps, as, cs]
      where
        psM = do
          row <- mapM (\(i, p) -> do
            lbl <- renderLNFact p
            return (Just (Left i), lbl)
            ) $ enumPrems ru
          return $ renderRow row
        asM = do
          ruleLabel <- ruleLabelM
          return $ renderRow [ (Nothing, ruleLabel ) ]
        csM = do
          row <- mapM (\(i, c) -> do
            lbl <- renderLNFact c
            return (Just (Right i), lbl)
            ) $ enumConcs ru
          return $ renderRow row

        ruleLabelM = do
          showAutoSource <- asks (get ((L..) goShowAutoSource gOptions) . fst3)
          lbl <- if showAutoSource
                      then mapM renderLNFact $ filter isAutoSource $ filter isNotDiffAnnotation $ get rActs ru
                      else mapM renderLNFact $ filter isNotDiffAnnotation $ get rActs ru
          return $
            prettyNodeId v <-> colon
            <-> text (showDotRuleCaseName ru)
            <> (if null lbl then mempty else brackets (vcat $ punctuate comma lbl))


        isNotDiffAnnotation fa = (fa /= (Fact (ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0) S.empty []))

        -- check if a fact is from auto-source
        isAutoSource ::  LNFact -> Bool
        isAutoSource (Fact tag _ _) =not $ hasAutoLabel (showFactTag $ tag)

        -- check if a fact has the label of auto-source
        hasAutoLabel :: String -> Bool
        hasAutoLabel f
            | "AUTO_IN_TERM_" `isPrefixOf` f  = True
            | "AUTO_IN_FACT_" `isPrefixOf` f  = True
            | "AUTO_OUT_TERM_" `isPrefixOf` f = True
            | "AUTO_OUT_FACT_" `isPrefixOf` f = True
            | otherwise = False


        renderRow annDocs =
          zipWith (\(ann, _) lbl -> (ann, lbl)) annDocs $
            -- magic factor 1.3 compensates for space gained due to
            -- non-propertional font
            renderBalanced 100 (max 30 . round . (* 1.3)) (map snd annDocs)

        renderBalanced :: Double           -- ^ Total available width
                       -> (Double -> Int)  -- ^ Convert available space to actual line-width.
                       -> [Doc]            -- ^ Initial documents
                       -> [String]         -- ^ Rendered documents
        renderBalanced _          _    []   = []
        renderBalanced totalWidth conv docs =
            zipWith (\w d -> widthRender (conv (ratio * w)) d) usedWidths docs
          where
            oneLineRender  = renderStyle (defaultStyle { mode = OneLineMode })
            widthRender w  = scaleIndent . renderStyle (defaultStyle { lineLength = w })
            usedWidths     = map (fromIntegral . length . oneLineRender) docs
            ratio          = totalWidth / sum usedWidths
            scaleIndent line = case span isSpace line of
              (spaces, rest) ->
                  -- spaces are not wide-enough by default => scale them up
                  let n = (1.5::Double) * fromIntegral (length spaces)
                  in  replicate (round n) ' ' ++ rest


-- | Dot a normal edge.
dotEdge :: Edge -> SeDot ()
dotEdge edge =
  case edge of
    SystemEdge (src, tgt) -> do
      (graph, _, _) <- ask
      let check p = maybe False p (resolveNodePremFact tgt graph) ||
                    maybe False p (resolveNodeConcFact src graph)
          attrs | check isProtoFact =
                    [("style","bold"),("weight","10.0")] ++
                    (guard (check isPersistentFact) >> [("color","gray50")])
                | check isKFact     = [("color","orangered2")]
                | otherwise         = [("color","gray30")]
      dotGenEdge attrs src tgt
    UnsolvedChain (src, tgt) ->
      dotGenEdge [("style","dotted"),("color","green")] src tgt
    LessEdge _ -> error "LessEdges are handled by dotLessEdge"
  where
    dotGenEdge style src tgt = do
      srcId <- getState dsConcs src ("Source node of edge not found: " ++ show src)
      tgtId <- getState dsPrems tgt ("Target node of edge not found: " ++ show tgt)
      liftDot $ D.edge srcId tgtId style

-- | Dot a less edge, which needs to be transformed first to contain the correct color.
dotLessEdge :: (NodeId, NodeId, String) -> SeDot ()
dotLessEdge (src, tgt, color) = do
  srcId <- getState dsNodes src ("Source node of less edge not found: " ++ show src)
  tgtId <- getState dsNodes tgt ("Target node of less edge not found: " ++ show src)
  liftDot $ D.edge srcId tgtId [("color",color),("style","dashed")]

-- | Dot a legend listing all abbreviations by adding a sink node with a suitable HTML table label.
generateLegend :: SeDot ()
generateLegend = do
  (graph, _, dotOptions) <- ask
  let abbrevs = get gAbbreviations graph
  -- Skip generating anything if no abbreviations exist.
  unless (null abbrevs) $ do
    nLegend <- liftDot $ D.scope (do
      D.attribute ("rank", "sink")
      let sortedAbbrevs = topoSortAbbrevs $ zip [0..] $
            sortOn (Data.Ord.Down . render . Sys.prettyLNTerm . fst) $ M.elems abbrevs
          labelColor = get doAbbrevColor dotOptions
          htmlLabel = D.htmlLabel $ abbrevLabel sortedAbbrevs labelColor
      D.node [("shape", "plain"), htmlLabel])
    -- We add invisible edges from all sink nodes of the graph to the legend node to place it somewhere in the middle of the bottom row.
    -- We only add edges from the sink nodes because edges from earlier nodes will be routed avoid later nodes (even if they are invisible) and create constraints that lead to excessive whitespace on the edges of the graph.
    let sinks = getGraphSinks graph
    dotIds <- getM dsNodes
    mapM_ (\nsink ->
      case M.lookup (get nNodeId nsink) dotIds of
      Nothing -> pure ()
      Just nid -> liftDot $ D.edge nid nLegend [("style", "invis")]) sinks
  where
    -- | Render all abbreviations as a table using graphviz' HTML notation.
    abbrevLabel sortedAbbrevs labelColor =
      let tableAttributes = [Border 1, CellBorder 0, CellSpacing 3, CellPadding 1] in
        Table $ HTable Nothing tableAttributes $ map (renderLine labelColor) sortedAbbrevs

    -- | Render an abbreviation to a table row in the legend using graphviz' HTML notation.
    renderLine :: D.Color -> (AbbreviationTerm, AbbreviationExpansion) -> Row
    renderLine labelColor (abbrevName, recursiveExpansion) =
      let cellAttributes = [Align HLeft, VAlign HTop]
          font txt = D.Text [Font [Color labelColor] txt]
          name = LabelCell cellAttributes (font [Str $ T.pack $ render $ Sys.prettyLNTerm abbrevName])
          eq = LabelCell cellAttributes (D.Text [Str $ "="])
          expansion = render $ Sys.prettyLNTerm recursiveExpansion
          -- The expansions can get pretty big, i.e. span multiple lines. To handle linebreaks we replace them with HTML <br> tags.
          expansionBR = LabelCell cellAttributes (D.Text $ expansion `joinLinesWith` Newline [Align HLeft]) in
      Cells [name, eq, expansionBR]

    -- | Replace newlines in `s` with the given separator.
    joinLinesWith :: String -> TextItem -> D.Text
    joinLinesWith s sep = intersperse sep $ map (Str . T.pack) $ lines s

    -- | Do a topological sort of abbreviations to ensure that we print abbreviations in the order in which they are defined.
    -- We define a partial order where for two abbreviations A & B, it holds A < B if A appears in the recursive expansion of B.
    -- To extend the partial order to all abbreviations we do a topological sort on the graph where the nodes are abbreviations and edges are based on the partial order.
    topoSortAbbrevs :: [(Int, (AbbreviationTerm, AbbreviationExpansion))] -> [(AbbreviationTerm, AbbreviationExpansion)]
    topoSortAbbrevs keyedElems =
      let edgeList = map (\(key1, node) ->
                            let outlist = findLegendEdges keyedElems node in
                            (node, key1, outlist)) keyedElems
          (graph, vf, _) = G.graphFromEdges edgeList
          vertices = G.topSort graph in
      map (\v -> fst3 $ vf v) vertices

    -- | We create an edge A -> B between two abbreviations A & B if A appears in the recursive expansion of B.
    findLegendEdges :: [(Int, (AbbreviationTerm, AbbreviationExpansion))] -> (AbbreviationTerm, AbbreviationExpansion) -> [Int]
    findLegendEdges keyedElems (abbrevName1, _) =
      mapMaybe (\(key2, (_, recursiveExpansion2)) ->
                  if isProperSubterm abbrevName1 recursiveExpansion2
                  then Just key2
                  else Nothing) keyedElems




-- | Dot a sequent in compact form (one record per rule), if there is anything
-- to draw.
dotSystemCompact :: GraphOptions -> DotOptions -> System -> D.Dot ()
dotSystemCompact graphOptions dotOptions se =
    let graph = systemToGraph se graphOptions
        -- a.d. TODO make nodeColorMap filter systemnodes from graph instead of accessing System directly.
        colorMap = nodeColorMap (M.elems $ get sNodes se)
        dot = dotGraphCompact dotOptions colorMap graph in
    dot

-- | Dot a graph in compact form (one record per rule).
dotGraphCompact :: DotOptions -> NodeColorMap -> Graph -> D.Dot ()
dotGraphCompact dotOptions colorMap graph =
    (`evalStateT` DotState M.empty M.empty M.empty M.empty) $
        (`runReaderT` (graph, colorMap, dotOptions)) $ do

            -- Get the graph representation details
            let repr = get gRepr graph
                clusters = get grClusters repr
                edges = get grEdges repr
                nodes = get grNodes repr
                (lessEdges, restEdges) = mergeLessEdges edges
                abbreviate = get ((L..) goAbbreviate gOptions) graph

            if null $ get grClusters repr then liftDot setDefaultAttributes else liftDot setDefaultAttributesIfCluster

            -- Process the nodes, clusters, and edges
            mapM_ (\node -> dotNodeCompact node Nothing) nodes
            mapM_ dotCluster clusters
            mapM_ dotEdge restEdges
            mapM_ dotLessEdge lessEdges
            dotClustersEdges clusters

            -- Generate legend if abbreviate is set
            when abbreviate generateLegend


-- Function to dot edges from multiple clusters
dotClustersEdges :: [Cluster] -> SeDot ()
dotClustersEdges clusters = do
    let allEdges = concatMap (get cEdges) clusters
        (lessEdges, restEdges) = mergeLessEdges allEdges
    mapM_ dotEdge restEdges
    mapM_ dotLessEdge lessEdges


-- Simple hash function to amplify differences between names
simpleHash :: String -> Int
simpleHash = foldl (\ acc c -> acc * 31 + ord c) 7

-- Function to generate a value based on the role name
generateValue :: String -> Double
generateValue s = fromIntegral (simpleHash s `mod` 360) / 360.0

-- Function to generate a color based on the role name with more aesthetic colors
roleColor :: String -> String
roleColor name = printf "#%02X%02X%02X%02X" r g b alpha
  where
    v = generateValue name
    -- Adjust saturation and value to get more pleasant colors
    RGB rf gf bf = hsvToRGB (HSV (v * 360) 0.75 0.85) :: RGB Double  -- Higher saturation and brightness
    r = floor (rf * 255) :: Int
    g = floor (gf * 255) :: Int
    b = floor (bf * 255) :: Int
    alpha :: Int
    alpha = floor (255 * (0.3 :: Double))

-- Function to dot clusters
dotCluster :: Cluster -> SeDot ()
dotCluster (Cluster name nodes _) = do
    let baseName = fromMaybe "Undefined" (extractBaseName name)
    let color = roleColor baseName
    roleCluster name $ do
        liftDot $ D.attribute ("nodesep", "0.6")
        liftDot $ D.attribute ("ranksep", "0.6")
        liftDot $ D.attribute ("label", name)
        liftDot $ D.attribute ("style", "filled") -- Set style to filled to apply fillcolor
        liftDot $ D.attribute ("color", color)
        liftDot $ D.attribute ("penwidth", "2")
        liftDot $ D.attribute ("fillcolor", color) -- Use roleColor to set the fillcolor
        liftDot $ D.attribute ("overlap", "false")
        liftDot $ D.attribute ("sep", "4")

        mapM_ (\node -> dotNodeCompact node (Just color)) nodes

-- | Compute proper colors for all less-edges.
-- Computing the colors requires all less-edges of the graph, so we cannot do it per edge.
-- This is why we split up the edges here and use two different functions to convert them to a dot.
mergeLessEdges :: [Edge] -> ([(NodeId, NodeId, String)], [Edge])
mergeLessEdges edges = (merged, rest)
  where
    rest = filter (not . isLessEdge) edges
    merged =
      let lessEdges = mapMaybe extractLessEdge edges in
      map getAllRToC $ eqClasses (\(LessAtom x y _) -> (x, y)) lessEdges

    isLessEdge :: Edge -> Bool
    isLessEdge (LessEdge _) = True
    isLessEdge _ = False

    extractLessEdge :: Edge -> Maybe LessAtom
    extractLessEdge (LessEdge e) = Just e
    extractLessEdge _ = Nothing

    getAllRToC :: [LessAtom] -> (NodeId, NodeId, String)
    -- SAFETY: Output of eqClasses never contains the empty list.
    getAllRToC [] = error "empty list"
    getAllRToC xs@(x:_) =
      (get laSmaller x, get laLarger x,
        -- Sort order is reversed to put the "most important reason" first.
        allRtoColors (sortBy (comparing Data.Ord.Down) $ map (get laReason) xs))

    allRtoColors :: [Reason] -> String
    allRtoColors reasons =
      let len = length reasons
          per = if len >1 then ";" ++ show ((1 :: Double)/fromIntegral len) else ""
          colors = map toColor reasons
          scaledColors = map (++per) colors
      in intercalate ":" scaledColors

    toColor :: Reason -> String
    toColor r = case r of
         Adversary      -> "red"
         Formula        -> "black"
         Fresh          -> "blue3"
         InjectiveFacts -> "purple"
         NormalForm     -> "darkorange3"
