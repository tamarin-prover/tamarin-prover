{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Conversion of the graph part of a sequent to a Graphviz Dot file.
module Theory.Constraint.System.Dot (
    nonEmptyGraph
  , nonEmptyGraphDiff
  , dotSystemLoose
  , dotSystemCompact
  , compressSystem
  , BoringNodeStyle(..)
  ) where

import           Data.Char                (isSpace)
import           Data.Color
import qualified Data.DAG.Simple          as D
import qualified Data.Foldable            as F
import           Data.List                (find,foldl',intersect)
import qualified Data.Map                 as M
import           Data.Maybe
import           Data.Monoid              (Any(..))
import qualified Data.Set                 as S
import           Data.Ratio
import           Safe

import           Extension.Data.Label
import           Extension.Prelude

import           Control.Basics
import           Control.Monad.Reader
import           Control.Monad.State      (StateT, evalStateT)

import qualified Text.Dot                 as D
import           Text.PrettyPrint.Class

import           Theory.Constraint.System
import           Theory.Model
import           Theory.Text.Pretty       (opAction)

-- | 'True' iff the dotted system will be a non-empty graph.
nonEmptyGraph :: System -> Bool
nonEmptyGraph sys = not $
    M.null (get sNodes sys) && null (unsolvedActionAtoms sys) &&
    null (unsolvedChains sys) &&
    S.null (get sEdges sys) && S.null (get sLessAtoms sys)

-- | 'True' iff the dotted system will be a non-empty graph.
nonEmptyGraphDiff :: DiffSystem -> Bool
nonEmptyGraphDiff diffSys = not $
     case (get dsSystem diffSys) of
          Nothing    -> True
          (Just sys) -> M.null (get sNodes sys) && null (unsolvedActionAtoms sys) &&
                        null (unsolvedChains sys) &&
                        S.null (get sEdges sys) && S.null (get sLessAtoms sys)

type NodeColorMap = M.Map (RuleInfo ProtoRuleACInstInfo IntrRuleACInfo) (RGB Rational)
type SeDot = ReaderT (System, NodeColorMap) (StateT DotState D.Dot)

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
              nodeColor = maybe "white" rgbToHex color
          dot (label ru) [("fillcolor", nodeColor),("style","filled")] $ \vId -> do
              premIds <- mapM dotPrem
                           [ (v,i) | (i,_) <- enumPrems ru ]
              concIds <- mapM dotConc
                           [ (v,i) | (i,_) <- enumConcs ru ]
              sequence_ [ dotIntraRuleEdge premId vId | premId <- premIds ]
              sequence_ [ dotIntraRuleEdge vId concId | concId <- concIds ]
  where
    label ru = " : " ++ render nameAndActs
      where
        nameAndActs =
            ruleInfo (prettyProtoRuleName . get praciName) prettyIntrRuleACInfo (get rInfo ru) <->
            brackets (vcat $ punctuate comma $ map prettyLNFact $ filter isNotDiffAnnotation $ get rActs ru)
        isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0, factTerms = []})

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
dotPrem prem@(v, i) =
    dotOnce dsPrems prem $ dotTrySingleEdge snd prem $ do
        nodes <- asks (get sNodes . fst)
        let ppPrem = show prem -- FIXME: Use better pretty printing here
            (label, moreStyle) = fromMaybe (ppPrem, []) $ do
                ru <- M.lookup v nodes
                fa <- lookupPrem i ru
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
    dotNodeWithIndex dsConcs fst rConcs (id *** getConcIdx) "trapezium"
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
dotSystemLoose :: System -> D.Dot ()
dotSystemLoose se =
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
            (i, _)  <- enumConcs ru
            return (dotConc (v, i))
        sequence_ $ do
            (v, ru) <- M.toList $ get sNodes se
            (i, _)  <- enumPrems ru
            return (dotPrem (v,i))
        -- FIXME: Also dot unsolved actions.
        mapM_ dotNode     $ M.keys   $ get sNodes     se
        mapM_ dotEdge     $ S.toList $ get sEdges     se
        mapM_ dotChain    $            unsolvedChains se
        mapM_ dotLess     $ S.toList $ get sLessAtoms se
  where
    dotEdge  (Edge src tgt)  = do
        mayNid <- M.lookup (src,tgt) `liftM` getM dsSingles
        maybe (dotGenEdge [] src tgt) (const $ return ()) mayNid

    dotChain (src, tgt) =
        dotGenEdge [("style","dashed"),("color","green")] src tgt

    dotLess (src, tgt) = do
        srcId <- dotNode src
        tgtId <- dotNode tgt
        liftDot $ D.edge srcId tgtId
            [("color","black"),("style","dotted")] -- FIXME: Reactivate,("constraint","false")]
            -- setting constraint to false ignores less-edges when ranking nodes.

    dotGenEdge style src tgt = do
        srcId <- dotConc src
        tgtId <- dotPrem tgt
        liftDot $ D.edge srcId tgtId style


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
      [ (get rInfo ru, case find colorAttr $ ruleAttributes ru of
            Just (RuleColor c)  -> c
            Nothing             -> hsvToRGB $ getColor (gIdx, mIdx))
      | (gIdx, grp) <- groups, (mIdx, ru) <- zip [0..] grp ]
  where
    groupIdx ru | isDestrRule ru                   = 0
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

-- Note: Currently RuleColors are the only Rule Attributes, so the second line is
-- commented out to remove the redundant pattern compiler warning. If more are added,
-- the second line can be uncommented.
    colorAttr (RuleColor _) = True
--    colorAttr _             = False

    -- The hue of the intruder rules
    intruderHue :: Rational
    intruderHue = 18 % 360

------------------------------------------------------------------------------
-- Record based dotting
------------------------------------------------------------------------------

-- | The style for nodes of the intruder.
data BoringNodeStyle = FullBoringNodes | CompactBoringNodes
    deriving( Eq, Ord, Show )


-- | Dot a node in record based (compact) format.
dotNodeCompact :: BoringNodeStyle -> NodeId -> SeDot D.NodeId
dotNodeCompact boringStyle v = dotOnce dsNodes v $ do
    (se, colorMap) <- ask
    let hasOutgoingEdge =
            or [ v == v' | Edge (v', _) _ <- S.toList $ get sEdges se ]
    case M.lookup v $ get sNodes se of
      Nothing -> case filter ((v ==) . fst) (unsolvedActionAtoms se) of
        [] -> mkSimpleNode (show v) []
        as -> let lbl = (fsep $ punctuate comma $ map (prettyLNFact . snd) as)
                        <-> opAction <-> text (show v)
                  attrs | any (isKUFact . snd) as = [("color","gray")]
                        | otherwise               = [("color","darkblue")]
              in mkSimpleNode (render lbl) attrs
      Just ru -> do
          let color     = M.lookup (get rInfo ru) colorMap
              nodeColor = maybe "white" rgbToHex color
              attrs     = [("fillcolor", nodeColor),("style","filled")
                            , ("fontcolor", if colorUsesWhiteFont color then "white" else "black")]
          ids <- mkNode ru attrs hasOutgoingEdge
          let prems = [ ((v, i), nid) | (Just (Left i),  nid) <- ids ]
              concs = [ ((v, i), nid) | (Just (Right i), nid) <- ids ]
          modM dsPrems $ M.union $ M.fromList prems
          modM dsConcs $ M.union $ M.fromList concs
          return $ fromJust $ lookup Nothing ids
  where
    --True if there's a colour, and it's 'darker' than 0.5 in apparent luminosity
    --This assumes a linear colourspace, which is what graphviz seems to use
    colorUsesWhiteFont (Just (RGB r g b)) = (0.2126*r + 0.7152*g + 0.0722*b) < 0.5
    colorUsesWhiteFont _                  = False

    mkSimpleNode lbl attrs =
        liftDot $ D.node $ [("label", lbl),("shape","ellipse")] ++ attrs

    mkNode  :: RuleACInst -> [(String, String)] -> Bool 
      -> ReaderT (System, NodeColorMap) (StateT DotState D.Dot)
         [(Maybe (Either PremIdx ConcIdx), D.NodeId)]
    mkNode ru attrs hasOutgoingEdge
      -- single node, share node-id for all premises and conclusions
      | boringStyle == CompactBoringNodes &&
        (isIntruderRule ru || isFreshRule ru) = do
            let lbl | hasOutgoingEdge = show v ++ " : " ++ showRuleCaseName ru
                    | otherwise       = concatMap snd as
            nid <- mkSimpleNode lbl []
            return [ (key, nid) | (key, _) <- ps ++ as ++ cs ]
      -- full record syntax
      | otherwise =
            fmap snd $ liftDot $ (`D.record` attrs) $
            D.vcat $ map D.hcat $ map (map (uncurry D.portField)) $
            filter (not . null) [ps, as, cs]
      where
        ps = renderRow [ (Just (Left i),  prettyLNFact p) | (i, p) <- enumPrems ru ]
        as = renderRow [ (Nothing,        ruleLabel ) ]
        cs = renderRow [ (Just (Right i), prettyLNFact c) | (i, c) <- enumConcs ru ]

        ruleLabel =
            prettyNodeId v <-> colon <-> text (showRuleCaseName ru) <>
            (brackets $ vcat $ punctuate comma $
                map prettyLNFact $ filter isNotDiffAnnotation $ get rActs ru)

        isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0, factTerms = []})

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



-- | Dot a sequent in compact form (one record per rule), if there is anything
-- to draw.
dotSystemCompact :: BoringNodeStyle -> System -> D.Dot ()
dotSystemCompact boringStyle se =
    (`evalStateT` DotState M.empty M.empty M.empty M.empty) $
    (`runReaderT` (se, nodeColorMap (M.elems $ get sNodes se))) $ do
        liftDot $ setDefaultAttributes
        mapM_ (dotNodeCompact boringStyle) $ M.keys $ get sNodes       se
        mapM_ (dotNodeCompact boringStyle . fst) $ unsolvedActionAtoms se
        F.mapM_ dotEdge                            $ get sEdges        se
        F.mapM_ dotChain                           $ unsolvedChains    se
        F.mapM_ dotLess                            $ get sLessAtoms    se
  where
    missingNode shape label = liftDot $ D.node $ [("label", render label),("shape",shape)]
    dotPremC prem = dotOnce dsPrems prem $ missingNode "invtrapezium" $ prettyNodePrem prem
    dotConcC conc = dotOnce dsConcs conc $ missingNode "trapezium" $ prettyNodeConc conc
    dotEdge (Edge src tgt)  = do
        let check p = maybe False p (resolveNodePremFact tgt se) ||
                      maybe False p (resolveNodeConcFact src se)
            attrs | check isProtoFact =
                      [("style","bold"),("weight","10.0")] ++
                      (guard (check isPersistentFact) >> [("color","gray50")])
                  | check isKFact     = [("color","orangered2")]
                  | otherwise         = [("color","gray30")]
        dotGenEdge attrs src tgt

    dotGenEdge style src tgt = do
        srcId <- dotConcC src
        tgtId <- dotPremC tgt
        liftDot $ D.edge srcId tgtId style

    dotChain (src, tgt) =
        dotGenEdge [("style","dashed"),("color","green")] src tgt

    dotLess (src, tgt) = do
        srcId <- dotNodeCompact boringStyle src
        tgtId <- dotNodeCompact boringStyle tgt
        liftDot $ D.edge srcId tgtId
            [("color","black"),("style","dotted")] -- FIXME: reactivate ,("constraint","false")]
            -- setting constraint to false ignores less-edges when ranking nodes.


------------------------------------------------------------------------------
-- Compressed versions of a sequent
------------------------------------------------------------------------------

-- | Drop 'Less' atoms entailed by the edges of the 'System'.
dropEntailedOrdConstraints :: System -> System
dropEntailedOrdConstraints se =
    modify sLessAtoms (S.filter (not . entailed)) se
  where
    edges               = rawEdgeRel se
    entailed (from, to) = to `S.member` D.reachableSet [from] edges

-- | Unsound compression of the sequent that drops fully connected learns and
-- knows nodes.
compressSystem :: System -> System
compressSystem se0 =
    foldl' (flip tryHideNodeId) se (frees (get sLessAtoms se, get sNodes se))
  where
    se = dropEntailedOrdConstraints se0

-- | @hideTransferNode v se@ hides node @v@ in sequent @se@ if it is a
-- transfer node; i.e., a node annotated with a rule that is one of the
-- special intruder rules or a rule with with at most one premise and
-- at most one conclusion and both premises and conclusions have incoming
-- respectively outgoing edges.
--
-- The compression is chosen such that unly uninteresting nodes are that have
-- no open goal are suppressed.
tryHideNodeId :: NodeId -> System -> System
tryHideNodeId v se = fromMaybe se $ do
    guard $  (lvarSort v == LSortNode)
          && notOccursIn unsolvedChains
          && notOccursIn (get sFormulas)
    maybe hideAction hideRule (M.lookup v $ get sNodes se)
  where
    selectPart :: (System :-> S.Set a) -> (a -> Bool) -> [a]
    selectPart l p = filter p $ S.toList $ get l se

    notOccursIn :: HasFrees a => (System -> a) -> Bool
    notOccursIn proj = not $ getAny $ foldFrees (Any . (v ==)) $ proj se

    -- hide KU-actions deducing pairs, inverses, and simple terms
    hideAction = do
        guard $  not (null kuActions)
              && all eligibleTerm kuActions
              && all (\(i, j) -> not (i == j)) lNews
              && notOccursIn (standardActionAtoms)
              && notOccursIn (get sLastAtom)
              && notOccursIn (get sEdges)

        return $ modify sLessAtoms ( (`S.union` S.fromList lNews)
                                   . (`S.difference` S.fromList lIns)
                                   . (`S.difference` S.fromList lOuts)
                                   )
               $ modify sGoals (\m -> foldl' removeAction m kuActions)
               $ se
      where
        kuActions            = [ x | x@(i,_,_) <- kuActionAtoms se, i == v ]
        eligibleTerm (_,_,m) =
            isPair m || isInverse m || sortOfLNTerm m == LSortPub

        removeAction m (i, fa, _) = M.delete (ActionG i fa) m

        lIns  = selectPart sLessAtoms ((v ==) . snd)
        lOuts = selectPart sLessAtoms ((v ==) . fst)
        lNews = [ (i, j) | (i, _) <- lIns, (_, j) <- lOuts ]

    -- hide a rule, if it is not "too complicated"
    hideRule :: RuleACInst -> Maybe System
    hideRule ru = do
        guard $  eligibleRule
              && ( length eIns  == length (get rPrems ru) )
              && ( length eOuts == length (get rConcs ru) )
              && ( all (not . selfEdge) eNews             )
              && notOccursIn (get sLastAtom)
              && notOccursIn (get sLessAtoms)
              && notOccursIn (unsolvedActionAtoms)

        return $ modify sEdges ( (`S.union` S.fromList eNews)
                               . (`S.difference` S.fromList eIns)
                               . (`S.difference` S.fromList eOuts)
                               )
               $ modify sNodes (M.delete v)
               $ se
      where
        eIns  = selectPart sEdges ((v ==) . nodePremNode . eTgt)
        eOuts = selectPart sEdges ((v ==) . nodeConcNode . eSrc)
        eNews = [ Edge cIn pOut | Edge cIn _ <- eIns, Edge _ pOut <- eOuts ]

        selfEdge (Edge cIn pOut) = nodeConcNode cIn == nodePremNode pOut

        eligibleRule =
             any ($ ru) [isISendRule, isIRecvRule, isCoerceRule, isFreshRule]
          || ( null (get rActs ru) &&
               all (\l -> length (get l ru) <= 1) [rPrems, rConcs]
             )

{-
-- | Try to hide a 'NodeId'. This only works if it has only action and either
-- edge or less constraints associated.
tryHideNodeId :: NodeId -> System -> System
-}

