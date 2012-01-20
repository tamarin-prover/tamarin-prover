{-# LANGUAGE TypeSynonymInstances,PatternGuards,FlexibleInstances,DeriveDataTypeable,OverloadedStrings #-}
module ProofVisualization where

import ProofTree
import SymbolicDerivationGraph

import qualified Data.Set as S
import qualified Data.GraphViz.Commands as GC
import qualified Data.GraphViz as G
import qualified Data.Graph.Inductive.Tree as FGLT
import qualified Data.Graph.Inductive as FGL
import Data.Maybe

import qualified Text.Blaze.Html4.Transitional as H
import Text.Blaze.Html4.Transitional ( (!) )
import Text.Blaze.Html4.Transitional.Attributes hiding ( char, label )
import Text.Blaze.Renderer.String

-- ***************************************************************************
-- * Visualization
-- ***************************************************************************

zProofTreeToHtmlFile :: ZProofTree -> FilePath -> IO ()
zProofTreeToHtmlFile zpt outfile = do
  let currentSvg = "/tmp/proofs/current.svg"
  _ <- sdgToSvg (getRootSDG.getFocused $ zpt) currentSvg
  _ <- zProofTreeToSvg zpt "/tmp/proofs/overview.svg"
  let goals = filter (\(sdg,_) -> sdg /= getRootSDG (getFocused zpt)) $
                zip (getUnexplored (zipperToProofTree zpt)) [(0::Int)..]
  goalInfo <- mapM getInfo goals
  writeFile outfile (renderHtml (zProofTreeToHtml zpt currentSvg goalInfo))
 where
  getInfo (sdg,i) = do
    _ <- sdgToSvg sdg svg
    return ("Goal "++show i,svg)
   where svg = "/tmp/proofs/goal_"++show i++".svg"

zProofTreeToHtml :: ZProofTree -> String -> [(String,String)] -> H.Html
zProofTreeToHtml zpt currentSvg goals =
  H.docTypeHtml $ H.body $ H.span $ do
    mapM_ (H.p . H.string) (lines $ showProofTreeStats (zipperToProofTree zpt))
    focused
    zProofTreeToIndentedList zpt
    mapM_ infoToHtml goals
    overview
 where
  infoToHtml (state,svg) = do
    H.p $ H.string  (state++":")
    H.img ! src (H.stringValue svg)
  focused = do
    H.p $ H.string  ("Focused ("++ (showStatus .getFocused $ zpt)++"):")
    H.img ! src (H.stringValue currentSvg)
  overview = do
    H.p $ H.string  ("Overview:")
    H.img ! src (H.stringValue "/tmp/proofs/overview.svg")



-- ** Visualization of SGDs

sdgToGraphviz :: SDG -> G.DotGraph FGL.Node
sdgToGraphviz sdg = G.graphToDot params (sdgToFgl sdg)
 where
  params =
    G.nonClusteredParams
      {G.fmtNode=(\x -> [G.Label (G.HtmlLabel (G.HtmlTable (snd x))),
                         G.Shape G.BoxShape]),
       G.fmtEdge=(\(_,_,(i,j,mchain)) -> attribsEdge (i,j,mchain))}
  attribsEdge (i,j,Left chainIndex) =
    [G.Label (G.HtmlLabel (G.HtmlTable (G.HTable Nothing [G.HtmlBorder 0, G.HtmlCellBorder 0]
                                                 [G.HtmlRow [label]]))),
     G.Color [G.X11Color G.Gray]
    ]
   where label = G.HtmlLabelCell [G.HtmlBGColor (G.X11Color G.Cyan)]
                                 (G.HtmlText [G.HtmlStr  (show i++"~~"++show j++"@"++show chainIndex)])
  attribsEdge (i,j,Right weight) =
    [G.Label (G.StrLabel (show i++"->"++show j)), G.Weight weight]

sdgToFgl :: SDG -> FGLT.Gr G.HtmlTable (Int,Int,Either Int Double)
sdgToFgl sdg@(SDG nodes edges chains) = FGL.mkGraph nodesInd edgesInd
 where
  nodesInd = zip [1..] (map (showRuleGraphviz sdg) $ S.toList nodes)
  indNodes = zip (S.toList nodes) [1..]
  chainInds = zip (S.toList $ sChains sdg) [length (nonTrivialAssms sdg) ..]
  edgesInd = map (g False) (S.toList edges) ++ map (g True) (S.toList chains)
  g isChain e@(Edge (r1,i) (r2,j)) =
    (fromMaybe (errMissing "source") $ lookup r1 indNodes,
     fromMaybe (errMissing "target") $ lookup r2 indNodes,
     (i,j,
      if isChain then maybe (errMissing "chain") Left $ lookup e chainInds
      else case getConc r1 i of
             P {} -> Right 10.0
             _ -> Right 2.0))
   where
    errMissing missing =
        error $ "sdgToFgl: edge\n" ++ show e++ "\nin sdg, but "++missing++" not. nodes: \n"
                ++unlines (map show (S.toList nodes))

showRuleGraphviz :: SDG -> Rule -> G.HtmlTable
showRuleGraphviz sdg r@(Rule rn assms _ex concs) =
  (G.HTable Nothing [G.HtmlBorder 0, G.HtmlCellBorder 0] (sassms'++sconcs'))
 where
   sconcs = map showConc concsInfo
     -- if all get1o3 concsInfo then [] else map showConc concsInfo
    where concsInfo = zipWith (\i c -> ((r,i) `elem` sourcesSDG sdg,i,c)) [0..] concs
   sassms = map showAssm (zip [0..] assms)
   showAssm (i,a) =
     case lookup (r,i) oassmInds of
       Just ind -> labelCell [G.HtmlBGColor (G.X11Color G.Cyan)] (show a++"@"++show ind)
       Nothing -> labelCell [] (show a)
   showConc (isSource,i,a) = labelCell [] (if isSource then "#"++show i else show a)
   oassms = nonTrivialAssms sdg
   oassmInds = zip oassms [(0::Int)..]
   len    = max (length sconcs) (length sassms)
   labelCell attrs s = G.HtmlLabelCell attrs (G.HtmlText [G.HtmlStr  s])
   nameCell = labelCell [G.HtmlBGColor (G.X11Color G.Gray)] rn
   sassms' = [G.HtmlRow (sassms++(replicate (len - length sassms) emptyCell)++[nameCell])]
   sconcs' = if null sconcs then [] else [G.HtmlRow (sconcs++(replicate (len - length sconcs + 1) emptyCell))]
   emptyCell = G.HtmlLabelCell [] (G.HtmlText [])

zProofTreeToGraphviz :: ZProofTree -> G.DotGraph FGL.Node
zProofTreeToGraphviz zpt = G.graphToDot params (zProofTreeToFGL zpt)
 where
  params =
    G.nonClusteredParams
      {G.fmtNode=(\x -> [G.Label (G.StrLabel (snd x)),
                         G.Shape G.BoxShape]),
       G.fmtEdge=(\(_,_,()) -> [])}

zProofTreeToFGL :: ZProofTree -> FGLT.Gr String ()
zProofTreeToFGL zpt = FGL.mkGraph node2Ind edgesInd
 where focused = getFocused zpt
       (nodes,edges) = traverse [] (zipperToProofTree zpt)
       backEdge [] = S.empty
       backEdge is@(_:ys) = S.singleton (ys,is) -- edge to parent
       mkNode pos pt =
         S.singleton ((if pt == focused then "==>" else "")++showStatus pt,pos)
       traverse pos st@(Unexplored _) =
         (mkNode pos st, backEdge pos)
       traverse pos st@(Explored _ _ sts) =
         (S.unions (mkNode pos st:ns),
          S.unions (backEdge pos:es))
        where
         res = zipWith (\cst i -> traverse (i:pos) cst) sts [(1::Int)..]
         ns = map fst res
         es = map snd res
       node2Ind = zip  [1..] (map (\(s,pos) -> s++" "++concatMap show (reverse pos)) $ S.toList nodes)
       ind2Node = zip (map snd (S.toList nodes)) [1..]
       edgesInd = map g (S.toList edges)
       g (psrc,ptgt) = (fromJust $ lookup psrc ind2Node,
                        fromJust $ lookup ptgt ind2Node, ())

zProofTreeToIndentedList :: ZProofTree -> H.Html
zProofTreeToIndentedList zpt = H.pre $ H.string $ toText [] (zipperToProofTree zpt)
 where focused = getFocused zpt
       toText pos pt@(Explored _ _ pts) =
         ppStatus pos pt ++ (concat $ zipWith (\apt i -> toText (i:pos) apt) pts [(1::Int)..])
       toText pos pt@(Unexplored _) = ppStatus pos pt
       ppStatus pos pt =
         replicate (3*length pos) ' ' ++showStatus pt++" "++show (reverse pos)++(if pt == focused then " <=========" else "")++"\n"

-- ***************************************************************************
-- * Interaction with graphviz
-- ***************************************************************************

outputPath :: FilePath
outputPath = "/tmp/proofs/"

sdgToSvg :: SDG -> FilePath -> IO (Either String FilePath)
sdgToSvg sdg fname = 
  GC.runGraphviz (sdgToGraphviz sdg) GC.Svg fname

zProofTreeToSvg :: ZProofTree -> FilePath -> IO (Either String FilePath)
zProofTreeToSvg zpt fname = 
  GC.runGraphviz (zProofTreeToGraphviz zpt) GC.Svg fname

sdgToDot :: SDG -> FilePath -> IO (Either String FilePath)
sdgToDot sdg fname = 
  GC.runGraphviz (sdgToGraphviz sdg) GC.DotOutput fname

{-
sdgStateToColor :: SDGState -> G.X11Color
sdgStateToColor UnExplored = G.Cyan
sdgStateToColor (Dead _) = G.Red
sdgStateToColor Explored = G.Gray
sdgStateToColor Realized = G.Green
-}