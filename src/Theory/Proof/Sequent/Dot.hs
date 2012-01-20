{-# LANGUAGE TemplateHaskell, TypeOperators #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Conversion of the graph part of a sequent to a Graphviz Dot file.
module Theory.Proof.Sequent.Dot (
    dotSequentLoose
  , dotSequentCompact
  , compressSequent
  ) where

import Safe
import Data.Maybe
import Data.List
import Data.Monoid (Any(..))
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Color

import Extension.Prelude
import Extension.Data.Label

import Control.Basics
import Control.Monad.State (StateT, evalStateT)
import Control.Monad.Reader

import qualified Text.Dot as D
import Text.Isar hiding (style)

import Theory.Rule
import Theory.Proof.Sequent

type NodeColorMap = M.Map (RuleInfo ProtoRuleName IntrRuleACInfo) (HSV Double)
type SeDot = ReaderT (Sequent, NodeColorMap) (StateT DotState D.Dot)

-- | State to avoid multiple drawing of the same entity.
data DotState = DotState {
    _dsNodes   :: M.Map NodeId   D.NodeId
  , _dsPrems   :: M.Map NodePrem D.NodeId
  , _dsConcs   :: M.Map NodeConc D.NodeId
  , _dsSingles :: M.Map (NodeConc, NodePrem) D.NodeId
  }

$(mkLabels [''DotState])

-- | Lift a 'D.Dot' action.
liftDot :: D.Dot a -> SeDot a
liftDot = lift . lift

-- | All edges in a bipartite graph that have neither start point nor endpoint
-- in common with any other edge.
singleEdges :: (Ord a, Ord b) => [(a,b)] -> [(a,b)]
singleEdges es = 
    singles fst es `intersect` singles snd es
  where
    singles proj = concatMap single . groupOn proj . sortOn proj
    single []  = error "impossible"
    single [x] = return x
    single _   = mzero

-- | Get a lighter color.
lighter :: HSV Double -> RGB Double
lighter = hsvToRGB -- fmap (\c -> 1 - 0.3*(1-c)) . hsvToRGB

-- | Ensure that a 'SeDot' action is only executed once by querying and
-- updating the 'DotState' accordingly.
dotOnce :: Ord k 
        => (DotState :-> M.Map k D.NodeId) -- ^ Accessor to map storing this type of actions.
        -> k                               -- ^ Action index.
        -> SeDot D.NodeId                  -- ^ Action to execute only once.
        -> SeDot D.NodeId                          
dotOnce mapL k dot = do
    i <- join $ (maybe dot return . M.lookup k) `liftM` getM mapL
    modM mapL (M.insert k i)
    return i

dotNode :: NodeId -> SeDot D.NodeId
dotNode v = dotOnce dsNodes v $ do
    (se, colorMap) <- ask
    let nodes = get sNodes se
        dot info moreStyle facts = do
            vId <- liftDot $ D.node $ [("label", show v ++ info),("shape","ellipse")] 
                                      ++ moreStyle
            _ <- facts vId
            return vId

    case M.lookup v nodes of
      Nothing -> do
          dot "" [] (const $ return ()) -- \vId -> do
              {-
              premIds <- mapM dotPrem
                           [ NodePremFact v fa 
                           | SeRequires v' fa <- S.toList $ get sRequires se
                           , v == v' ]
              sequence_ [ dotIntraRuleEdge premId vId | premId <- premIds ]
              -}
      Just ru -> do
          let 
              color     = M.lookup (get rInfo ru) colorMap
              nodeColor = maybe "white" (rgbToHex . lighter) color
          dot (label ru) [("fillcolor", nodeColor),("style","filled")] $ \vId -> do
              premIds <- mapM dotPrem
                           [ NodePrem (v,i) | (i,_) <- zip [0..] $ get rPrems ru ]
              concIds <- mapM (dotConc . NodeConc) 
                           [ (v,i) | (i,_) <- zip [0..] $ get rConcs ru ]
              sequence_ [ dotIntraRuleEdge premId vId | premId <- premIds ]
              sequence_ [ dotIntraRuleEdge vId concId | concId <- concIds ]
  where
    label ru = " : " ++ render nameAndActs
      where
        nameAndActs = 
            ruleInfo prettyProtoRuleName prettyIntrRuleACInfo (get rInfo ru) <->
            brackets (vcat $ punctuate comma $ map prettyLNFact $ get rActs ru)

-- | An edge from a rule node to its premises or conclusions.
dotIntraRuleEdge :: D.NodeId -> D.NodeId -> SeDot ()
dotIntraRuleEdge from to = liftDot $ D.edge from to [("color","gray")]

{-
-- | An edge from a rule node to some of its premises or conclusions.
dotNonFixedIntraRuleEdge :: D.NodeId -> D.NodeId -> SeDot ()
dotNonFixedIntraRuleEdge from to = 
    liftDot $ D.edge from to [("color","steelblue")]
-}

-- | The style of a node displaying a fact.
factNodeStyle :: LNFact -> [(String,String)]
factNodeStyle fa
  | isJust (kFactView fa) = []
  | otherwise             = [("fillcolor","gray85"),("style","filled")]

-- | An edge that shares no endpoints with another edge and is therefore
-- contracted.
--
-- FIXME: There may be too many edges being contracted.
dotSingleEdge :: (NodeConc, NodePrem) -> SeDot D.NodeId
dotSingleEdge edge@(_, to) = dotOnce dsSingles edge $ do
    se <- asks fst
    let fa    = nodePremFact to se
        label = render $ prettyLNFact fa
    liftDot $ D.node $ [("label", label),("shape", "hexagon")]
                       ++ factNodeStyle fa

-- | A compressed edge.
dotTrySingleEdge :: Eq c
                 => ((NodeConc, NodePrem) -> c) -> c
                 -> SeDot D.NodeId -> SeDot D.NodeId
dotTrySingleEdge sel x dot = do
    singles <- getM dsSingles
    maybe dot (return . snd) $ find ((x ==) . sel . fst) $ M.toList singles

-- | Premises.
dotPrem :: NodePrem -> SeDot D.NodeId
dotPrem prem@(NodePrem (v,i)) = 
    dotOnce dsPrems prem $ dotTrySingleEdge snd prem $ do
        nodes <- asks (get sNodes . fst)
        let ppPrem = show prem -- FIXME: Use better pretty printing here
            (label, moreStyle) = fromMaybe (ppPrem, []) $ do
                ru <- M.lookup v nodes
                fa <- get rPrems ru `atMay` i
                return ( render $ prettyLNFact fa
                       , factNodeStyle fa
                       )
        liftDot $ D.node $ [("label", label),("shape",shape)] 
                           ++ moreStyle
  where
    shape = "invtrapezium"

-- | Conclusions.
dotConc :: NodeConc -> SeDot D.NodeId
dotConc = 
    dotNodeWithIndex dsConcs fst rConcs getNodeConc "trapezium"    
  where
    dotNodeWithIndex stateSel edgeSel ruleSel unwrap shape x0 = 
        dotOnce stateSel x0 $ dotTrySingleEdge edgeSel x0 $ do
            let x = unwrap x0
            nodes <- asks (get sNodes . fst)
            let (label, moreStyle) = fromMaybe (show x, []) $ do
                    ru <- M.lookup (fst x) nodes
                    fa <- (`atMay` snd x) $ get ruleSel ru
                    return ( render $ prettyLNFact fa
                           , factNodeStyle fa
                           )
            liftDot $ D.node $ [("label", label),("shape",shape)] 
                               ++ moreStyle

-- | Convert the sequent to a 'D.Dot' action representing this sequent as a
-- graph in the GraphViz format. The style is loose in the sense that each
-- premise and conclusion gets its own node.
dotSequentLoose :: Sequent -> D.Dot ()
dotSequentLoose se =
    (`evalStateT` DotState M.empty M.empty M.empty M.empty) $ 
    (`runReaderT` (se, nodeColorMap (M.elems $ get sNodes se))) $ do
        liftDot $ setDefaultAttributes
        -- draw single edges with matching facts.
        mapM_ dotSingleEdge $ singleEdges $ do
            Edge from to <- S.toList $ get sEdges se
            -- FIXME: ensure that conclusion and premise are equal
            guard (nodeConcFact from se == nodePremFact to se)
            return (from, to)
        sequence_ $ do
            (v, ru) <- M.toList $ get sNodes se
            (i, _)  <- zip [0..] $ get rConcs ru
            return (dotConc (NodeConc (v, i)))
        sequence_ $ do
            (v, ru) <- M.toList $ get sNodes se
            (i, _)  <- zip [0..] $ get rPrems ru
            return (dotPrem (NodePrem (v,i)))
        mapM_ dotNode     $ M.keys   $ get sNodes    se
        mapM_ dotEdge     $ S.toList $ get sEdges    se
        mapM_ dotChain    $ S.toList $ get sChains   se
        mapM_ dotMsgEdge  $ S.toList $ get sMsgEdges se
        mapM_ dotLess     $            sLessAtoms    se
  where
    dotEdge  (Edge src tgt)  = do
        mayNid <- M.lookup (src,tgt) `liftM` getM dsSingles
        maybe (dotGenEdge [] src tgt) (const $ return ()) mayNid

    dotChain (Chain src tgt) = 
        dotGenEdge [("style","dashed"),("color","green")] src tgt 

    dotMsgEdge (MsgEdge src tgt) = 
        dotGenEdge [("style","dotted"),("color","orange")] src tgt 

    dotLess (src, tgt) = do
        srcId <- dotNode src
        tgtId <- dotNode tgt
        liftDot $ D.edge srcId tgtId 
            [("color","black"),("style","dotted"),("constraint","false")]
            -- setting constraint to false ignores less-edges when ranking nodes.

    dotGenEdge style src tgt = do
        srcId <- dotConc src
        tgtId <- dotPrem tgt
        liftDot $ D.edge srcId tgtId style

    {-
    dotProvides (SeProvides v fa) = do
        vId <- dotNode v
        faId <- liftDot $ D.node [("label",label),("shape","trapezium")]
        dotNonFixedIntraRuleEdge vId faId
      where
        label = render $ prettyLNFact fa

    dotRequires (SeRequires v _fa) = do
       _vId <- dotNode v
       return ()
       -- FIXME: Reenable
       -- premId <- dotPrem (NodePremFact v fa)
       -- dotNonFixedIntraRuleEdge premId vId
    -}

-- | Set default attributes for nodes and edges.
setDefaultAttributes :: D.Dot ()
setDefaultAttributes = do
  D.attribute ("nodesep","0.3")
  D.attribute ("ranksep","0.3")
  D.nodeAttributes [("fontsize","8"),("fontname","Helvetica"),("width","0.3"),("height","0.2")]
  D.edgeAttributes [("fontsize","8"),("fontname","Helvetica")]


-- | Compute a color map for nodes labelled with a proof rule info of one of
-- the given rules.
nodeColorMap :: [RuleACInst] -> NodeColorMap
nodeColorMap rules = 
    M.fromList $ 
      [ (get rInfo ru, getColor (gIdx, mIdx))
      | (gIdx, grp) <- groups, (mIdx, ru) <- zip [0..] grp ]
  where
    groupIdx ru | isDestrRule ru                   = 0
                | isConstrRule ru                  = 2
                | isFreshRule ru || isKnowsRule ru = 3
                | otherwise                        = 1

    -- groups of rules labeled with their index in the group
    groups = [ (gIdx, [ ru | ru <- rules, gIdx == groupIdx ru])
             | gIdx <- [0..3]
             ]
    
    -- color for each member of a group
    colors = M.fromList $ lightColorGroups intruderHue (map (length . snd) groups)
    getColor idx = fromMaybe (HSV 0 1 1) $ M.lookup idx colors

    -- The hue of the intruder rules
    intruderHue :: Double
    intruderHue = 18 / 360

------------------------------------------------------------------------------
-- Record based dotting
------------------------------------------------------------------------------

-- | Dot a node in record based (compact) format.
dotNodeCompact :: NodeId -> SeDot D.NodeId
dotNodeCompact v = dotOnce dsNodes v $ do
    (se, colorMap) <- ask
    case M.lookup v $ get sNodes se of
      Nothing -> liftDot $ D.node $ [("label", show v),("shape","ellipse")] 
      Just ru -> do
          let color     = M.lookup (get rInfo ru) colorMap
              nodeColor = maybe "white" (rgbToHex . lighter) color
              attrs     = [("fillcolor", nodeColor),("style","filled")]
          (_, ids) <- liftDot $ D.record (mkRecord ru) attrs
          let prems = [ (NodePrem (v, i), nid) | (Just (Left i),  nid) <- ids ]
              concs = [ (NodeConc (v, i), nid) | (Just (Right i), nid) <- ids ]
          modM dsPrems $ M.union $ M.fromList prems
          modM dsConcs $ M.union $ M.fromList concs
          return $ fromJust $ lookup Nothing ids
  where
    mkRecord ru = D.vcat $ map D.hcat $ filter (not . null)
      [ [ D.portField (Just (Left i)) (render (prettyLNFact p))
        | (i, p) <- zip [(0::Int)..] $ get rPrems ru ]
      , [ D.portField Nothing (show v ++ " : " ++ showRuleCaseName ru ++ acts) ]
      , [ D.portField (Just (Right i)) (render (prettyLNFact c))
        | (i, c) <- zip [(0::Int)..] $ get rConcs ru ]
      ]
      where
        acts = (" " ++) $ render $
            brackets $ vcat $ punctuate comma $ map prettyLNFact $ get rActs ru
    

-- | Dot a sequent in compact form (one record per rule)
dotSequentCompact :: Sequent -> D.Dot ()
dotSequentCompact se = 
    (`evalStateT` DotState M.empty M.empty M.empty M.empty) $ 
    (`runReaderT` (se, nodeColorMap (M.elems $ get sNodes se))) $ do
        liftDot $ setDefaultAttributes
        mapM_ dotNodeCompact $ M.keys   $ get sNodes    se
        mapM_ dotEdge        $ S.toList $ get sEdges    se
        mapM_ dotChain       $ S.toList $ get sChains   se
        mapM_ dotMsgEdge     $ S.toList $ get sMsgEdges se
        mapM_ dotLess        $            sLessAtoms    se
  where
    missingNode shape label = liftDot $ D.node $ [("label", render label),("shape",shape)] 
    dotPremC prem = dotOnce dsPrems prem $ missingNode "invtrapezium" $ prettyNodePrem prem
    dotConcC conc = dotOnce dsConcs conc $ missingNode "trapezium" $ prettyNodeConc conc
    dotEdge (Edge src tgt)  = do
        let check p = maybe False p (resolveNodePremFact tgt se) ||
                      maybe False p (resolveNodeConcFact src se)
            attrs | check isProtoFact = [("style","bold"),("weight","10.0")]
                  | check isKFact     = [("color","orangered2")]
                  | otherwise         = [("color","gray30")]
        dotGenEdge attrs src tgt

    dotGenEdge style src tgt = do
        srcId <- dotConcC src
        tgtId <- dotPremC tgt
        liftDot $ D.edge srcId tgtId style
    
    dotChain (Chain src tgt) = 
        dotGenEdge [("style","dashed"),("color","green")] src tgt 

    dotMsgEdge (MsgEdge src tgt) = 
        dotGenEdge [("style","dotted"),("color","orange")] src tgt 

    dotLess (src, tgt) = do
        srcId <- dotNodeCompact src
        tgtId <- dotNodeCompact tgt
        liftDot $ D.edge srcId tgtId 
            [("color","black"),("style","dotted"),("constraint","false")]
            -- setting constraint to false ignores less-edges when ranking nodes.

    {-
    dotProvides (SeProvides v fa) = do
        vId <- dotNodeCompact v
        faId <- liftDot $ D.node [("label",label),("shape","trapezium")]
        dotNonFixedIntraRuleEdge vId faId
      where
        label = render $ prettyLNFact fa
    dotRequires (SeRequires v _fa) = do
       _vId <- dotNodeCompact v
       return ()
       -- FIXME: Reenable
       -- premId <- dotPremC (NodePremFact v fa)
       -- dotNonFixedIntraRuleEdge premId vId
    -}

------------------------------------------------------------------------------
-- Compressed versions of a sequent
------------------------------------------------------------------------------

-- | Unsound compression of the sequent that drops fully connected learns and
-- knows nodes.
compressSequent :: Sequent -> Sequent
compressSequent se = 
    foldl' (flip hideTransferNode) se $ 
    [ x | x@(_, ru) <- M.toList $ get sNodes se
        , isFreshRule ru || isDestrRule ru || isConstrRule ru || isLearnRule ru || isKnowsRule ru ]

-- | @hideTransferNode v se@ hides node @v@ in sequent @se@ if it is a
-- transfer node; i.e., a node annotated with a rule with exactly one premise
-- and one conclusion with exactly one incoming and one outgoing edge.
hideTransferNode :: (NodeId, RuleACInst) -> Sequent -> Sequent
hideTransferNode (v, ru) se = fromMaybe se $ do
    guard $    
         all (\l -> length (get l ru) <= 1) [rPrems, rConcs]
      && (null $ get rActs ru)
      && (length eIns  == length (get rPrems ru))
      && (length eOuts == length (get rConcs ru))
      && all (\(Edge cIn pOut) -> nodeConcNode cIn /= nodePremNode pOut) eNews
      && notOccursIn sMsgEdges
      && notOccursIn sChains 
      && notOccursIn sAtoms
      && notOccursIn sFormulas

    return $ modify sEdges (  (`S.union` S.fromList eNews)
                            . (`S.difference` S.fromList eIns)
                            . (`S.difference` S.fromList eOuts)
                           )
           $ modify sNodes (M.delete v)
           $ se
  where
    selectPart :: (Sequent :-> S.Set a) -> (a -> Bool) -> [a]
    selectPart l p = filter p $ S.toList $ get l se

    notOccursIn :: HasFrees a => (Sequent :-> a) -> Bool
    notOccursIn l = not $ getAny $ foldFrees (Any . (v ==)) $ get l se

    eIns  = selectPart sEdges ((v ==) . nodePremNode . eTgt)
    eOuts = selectPart sEdges ((v ==) . nodeConcNode . eSrc)

    eNews = [ Edge cIn pOut | Edge cIn _ <- eIns, Edge _ pOut <- eOuts ]
