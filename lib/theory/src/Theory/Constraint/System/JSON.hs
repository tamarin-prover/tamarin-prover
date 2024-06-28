{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{-|
   Copyright   : (c) 2016 Dominik Schoop
   License     : GPL v3 (see LICENSE)

   Maintainer  : Dominik Schoop dominik.schoop@hs-esslingen.de
   Portability : GHC only

   Conversion of the graph part of a sequent (constraint system) to a JSON graph format

   ADVISE:
   - DO NOT USE sequentToJSONPretty IN OPERATIONAL MODE.
     Remember to replace sequentToJSONPretty with sequentToJSON in getTheoryGraphR in Handler.hs.
   - The time consuming pretty printing of facts and terms can be disabeled by a parameter of
     sequentToJSONPretty and sequentToJSON. Currently, everything is pretty with sequentToJSONPretty
     and nothing is pretty with sequentToJSON.

   TO DO:
   - generate JSON in non-interactive mode
   - make it work for observational equivalence
   - encode historic information in the graph: sequence of nodes added

   OPEN PROBLEMS:
   - JSON encodePretty converts < and > to "\u003c" and "\u003e"
     ghastly postprocessing has been applied to sequentToJSONPretty
-}

module Theory.Constraint.System.JSON (
    sequentsToJSON,                     
    writeSequentAsJSONToFile,
    sequentsToJSONPretty,
    writeSequentAsJSONPrettyToFile
  ) where
import           Extension.Data.Label       as L (get)
import           Data.Aeson
import           Data.Aeson.TH
import           Data.Aeson.Encode.Pretty   -- to do pretty printing of JSON
import           Data.Foldable
import qualified Data.Map                   as M
import           Data.Maybe
import qualified Data.ByteString.Lazy.Char8 as BC (unpack)
import           Control.Monad.Reader
import           Text.PrettyPrint.Class     -- for Doc and the pretty printing functions 
import           Theory.Constraint.System hiding (Edge, resolveNodeConcFact, resolveNodePremFact)
import qualified Theory.Constraint.System.Graph.Graph as G
import           Theory.Constraint.System.Graph.Graph hiding (defaultOptions)
import           Theory.Model

-------------------------------------------------------------------------------------------------
-- Data structure for JSON graphs                                                              --
-- adapted from https://github.com/jsongraph/json-graph-specification                          --
-------------------------------------------------------------------------------------------------

-- | Representation of a term in a JSON graph node.
data JSONGraphNodeTerm = 
  Const String
  | Funct String [JSONGraphNodeTerm] String
  deriving (Show)

-- | Automatically derived instances have unnecessarily many tag-value pairs. 
-- Hence, we have our own here.
instance FromJSON JSONGraphNodeTerm where
  parseJSON = withObject "JSONGraphNodeTerm" $ \o -> asum [
    Const <$> o .: "jgnConst",
    Funct <$> o .: "jgnFunct" <*> o .: "jgnParams" <*> o .: "jgnShow" ]

instance ToJSON JSONGraphNodeTerm where
  toJSON (Const s) = object [ "jgnConst" .= s ]
  toJSON (Funct f p s) = object 
    [ "jgnFunct"  .= f
    , "jgnParams" .= toJSON p
    , "jgnShow"   .= s
    ] 

-- | Representation of a fact in a JSON graph node.
data JSONGraphNodeFact = JSONGraphNodeFact 
  { jgnFactId    :: String
  , jgnFactTag   :: String  -- ^ ProtoFact, FreshFact, OutFact, InFact, KUFact, KDFact, DedFact
  , jgnFactName  :: String  -- ^ Fr, Out, In, !KU, ...
  , jgnFactMult  :: String  -- ^ "!" = persistent, "" = linear
  , jgnFactTerms :: [JSONGraphNodeTerm]
  , jgnFactShow  :: String
  } deriving (Show)

-- | Representation of meta data of a JSON graph node.
data JSONGraphNodeMetadata = JSONGraphNodeMetadata 
  { jgnPrems :: [JSONGraphNodeFact]
  , jgnActs  :: [JSONGraphNodeFact]
  , jgnConcs :: [JSONGraphNodeFact]
  } deriving (Show)

-- | Representation of a node of a JSON graph.
data JSONGraphNode = JSONGraphNode 
  { jgnId :: String
  , jgnType :: String
  , jgnLabel :: String
  , jgnMetadata :: Maybe JSONGraphNodeMetadata
  } deriving (Show)

-- | Representation of an edge of a JSON graph.
data JSONGraphEdge = JSONGraphEdge 
  { jgeSource :: String
  , jgeRelation :: String
  , jgeTarget :: String
  } deriving (Show)

-- | Representation of a cluster of a JSON graph.
data JSONGraphCluster = JSONGraphCluster 
  { jgcName :: String
  , jgcNodes :: [JSONGraphNode]
  , jgcEdges :: [JSONGraphEdge]
  } deriving (Show)

-- | Representation of an abbreviation of a JSON graph.
data JSONGraphAbbrev = JSONGraphAbbrev
  { jgaTerm :: JSONGraphNodeTerm
  , jgaAbbrev :: JSONGraphNodeTerm
  , jgaExpansion :: JSONGraphNodeTerm
  } deriving (Show)

-- | Representation of a JSON graph.
data JSONGraph = JSONGraph 
  { jgDirected :: Bool
  , jgType :: String
  , jgLabel :: String
  , jgNodes :: [JSONGraphNode]
  , jgEdges :: [JSONGraphEdge]
  , jgClusters :: [JSONGraphCluster]
  , jgAbbrevs :: [JSONGraphAbbrev]
  } deriving (Show)

-- | Representation of a collection of JSON graphs.
data JSONGraphs = JSONGraphs 
    {
      graphs :: [JSONGraph]
    } deriving (Show)

-- | Derive ToJSON and FromJSON. 
concat <$> mapM (deriveJSON defaultOptions) [''JSONGraphNodeFact, ''JSONGraphNodeMetadata, ''JSONGraphEdge, ''JSONGraphCluster, ''JSONGraphAbbrev, ''JSONGraph, ''JSONGraphs]

-- | Optional fields are not handled correctly with automatically derived instances
-- hence, we have our own here.
instance FromJSON JSONGraphNode where
  parseJSON = withObject "JSONGraphNode" $ \o -> JSONGraphNode
      <$> o .: "jgnId"
      <*> o .: "jgnType"
      <*> o .: "jgnLabel"
      <*> o .:? "jgnMetadata"

instance ToJSON JSONGraphNode where
  toJSON (JSONGraphNode jgnId' jgnType' jgnLabel' jgnMetadata') = object $ catMaybes
      [ ("jgnId" .=) <$> pure jgnId'
      , ("jgnType" .=) <$> pure jgnType'
      , ("jgnLabel" .=) <$> pure jgnLabel'
      , ("jgnMetadata" .=) <$> jgnMetadata' ]

-- | Generation of JSON text from JSON graphs.

-- | Flatten out pretty printed facts from prettyLNFact etc.
cleanString :: [Char] -> [Char]
cleanString [] = []
cleanString (' ':'\n':' ':xs) = cleanString (' ':xs)
cleanString ('\n':xs) = cleanString xs
cleanString (' ':' ':xs) = cleanString (' ':xs)
cleanString (c:xs) = (c:cleanString xs)

-- | Convert output of pretty print functions to string.
pps :: Doc -> String
pps d = cleanString $ render d

-- | EncodePretty encodes '<' as "\u003c" and '>' as "\u003e".
-- This function replaces these characters. 
removePseudoUnicode :: [Char] -> [Char]
removePseudoUnicode [] = []
removePseudoUnicode ('\\':'u':'0':'0':'3':'c':xs) = ('<':removePseudoUnicode xs)
removePseudoUnicode ('\\':'u':'0':'0':'3':'e':xs) = ('>':removePseudoUnicode xs)
removePseudoUnicode (x:xs) = (x:removePseudoUnicode xs)

-- | Remove " from start and end of string.
plainstring :: String -> String
plainstring ('\"':s) = reverse $ plainstring $ reverse s
plainstring s = s

-- | Determine the type of rule for a JSON node.
getRuleType :: HasRuleName r => r -> String
getRuleType r
    | isIntruderRule r  = "isIntruderRule"
    | isDestrRule r     = "isDestrRule"
    | isIEqualityRule r = "isIEqualityRule"
    | isConstrRule r    = "isConstrRule"
    | isPubConstrRule r = "isPubConstrRule"
    | isNatConstrRule r = "isNatConstrRule"
    | isFreshRule r     = "isFreshRule"
    | isIRecvRule r     = "isIRecvRule"
    | isISendRule r     = "isISendRule"
    | isCoerceRule r    = "isCoerceRule"
    | isProtocolRule r  = "isProtocolRule"
    | otherwise         = "unknown rule type"

-- | 
-- Bool: determines whether facts etc are also pretty printed
-- Graph: Graph to be dumped to JSON
type RJSON a = Reader (Bool, Graph) a

getPretty :: RJSON Bool
getPretty = do
  (pretty, _) <- ask
  return pretty

getGraph :: RJSON Graph
getGraph = do
  (_, graph) <- ask
  return graph

-- | Generate the JSON data structure from a term.
-- | "instance Show a" in Raw.hs served as example.
lntermToJSONGraphNodeTerm :: Bool -> LNTerm -> JSONGraphNodeTerm
lntermToJSONGraphNodeTerm pretty t =
    case viewTerm t of
      Lit l -> Const (show l)
      FApp (NoEq (s,_)) [] 
            -> Funct (plainstring $ show s) [] res
      FApp (NoEq (s,_)) as 
            -> Funct (plainstring $ show s) (map (lntermToJSONGraphNodeTerm pretty) as) res
      FApp (AC o) as       
            -> Funct (show o) (map (lntermToJSONGraphNodeTerm pretty) as) res
      _     -> Const ("unknown term type: " ++ show t)
    where 
      res = case pretty of 
              True -> show t
              False -> "" 

-- | Generate the JSON data structure for items such as facts and actions. 
itemToJSONGraphNodeFact :: Bool -> String -> LNFact -> JSONGraphNodeFact
itemToJSONGraphNodeFact pretty id' f =
     JSONGraphNodeFact { jgnFactId    = id'
                       , jgnFactTag   = case isProtoFact f of
                                          True  -> "ProtoFact"
                                          False -> show (factTag f)
                       , jgnFactName  = showFactTag $ factTag f
                       , jgnFactMult  = case factTagMultiplicity $ factTag f of
                                          Linear     -> ""
                                          Persistent -> "!"
                       , jgnFactTerms = map (lntermToJSONGraphNodeTerm pretty) (factTerms f)
                       , jgnFactShow  = case pretty of
                                          True  -> pps $ prettyLNFact f
                                          False -> ""
                       }
{-|
   Generate JSON data structure for facts in premises and conclusion of rules.
   Since facts are ordered in the premises and conclusions, the ordering number as well as a prefix
   ("p" (premise) and "c" (conclusion)) are given to the function.
-}
factToJSONGraphNodeFact :: Bool -> String -> NodeId -> (Int,LNFact) -> JSONGraphNodeFact
factToJSONGraphNodeFact pretty prefix n (idx, f) =
     itemToJSONGraphNodeFact pretty (show n ++ ":" ++ prefix ++ show idx) f

-- | Generate JSONGraphNode from a node of an abstract graph. (metadata part)
-- Facts and actions as are represented as metadata to keep close to the original JSON graph schema.
nodeToJSONGraphNodeMetadata :: Bool -> (NodeId, RuleACInst) -> JSONGraphNodeMetadata
nodeToJSONGraphNodeMetadata pretty (n, ru) = 
    JSONGraphNodeMetadata { jgnPrems = map (factToJSONGraphNodeFact pretty "p" n) 
                                       $ zip [0..] $ L.get rPrems ru
                          , jgnActs  = map (itemToJSONGraphNodeFact pretty "action") $ L.get rActs ru 
                          , jgnConcs = map (factToJSONGraphNodeFact pretty "c" n) 
                                       $ zip [0..] $ L.get rConcs ru
                          }

-- | Generate JSONGraphNode from a node of an abstract graph.
graphNodeToJSONGraphNode :: Node -> RJSON JSONGraphNode
graphNodeToJSONGraphNode node = do
  pretty <- getPretty
  let nid = get nNodeId node
      nodeType = get nNodeType node
  case nodeType of
    SystemNode ru -> 
      return $ JSONGraphNode 
                { jgnId = show nid
                , jgnType = getRuleType ru
                , jgnLabel = getRuleName ru
                , jgnMetadata = Just (nodeToJSONGraphNodeMetadata pretty (nid, ru))
                }
    UnsolvedActionNode facts -> 
      return $ JSONGraphNode 
                { jgnId = show nid
                , jgnType     = "unsolvedActionAtom"
                , jgnLabel    = if pretty 
                                then pps $ fsep $ punctuate comma $ map prettyLNFact facts
                                else ""
                , jgnMetadata = 
                    Just JSONGraphNodeMetadata 
                      { jgnPrems = []
                      , jgnActs  = map (itemToJSONGraphNodeFact pretty "action") facts 
                      , jgnConcs = [] 
                      }
               }    
    LastActionAtom -> 
      return $ JSONGraphNode 
                { jgnId = show nid
                , jgnType = "lastAtom"
                , jgnLabel = show nid
                , jgnMetadata = Nothing 
                }
    {-|
      Generate a JSONGraphNode for those nodes in sEdges that are not present in sNodes. 
      This might occur in the case distinctions shown in the GUI.
      Since a fact is missing, the id is encoded as jgnFactId, could also be done directly in jgnId.
    -}
    MissingNode (Left conc) -> 
      -- a.d. TODO JSON ignores conc and always sets conclusion id to c0. Is that intended behavior?
      return $ JSONGraphNode 
        { jgnId = show nid
        , jgnType = "missingNodeConc"
        , jgnLabel = ""
        , jgnMetadata = 
            Just JSONGraphNodeMetadata 
              { jgnPrems = []
              , jgnActs  = []
              , jgnConcs = 
                  [ JSONGraphNodeFact 
                      { jgnFactId    = show nid ++":c0"
                      , jgnFactTag   = ""
                      , jgnFactName  = ""
                      , jgnFactMult  = ""
                      , jgnFactTerms = []   
                      , jgnFactShow  = ""
                      }
                  ]
              }
        }
    MissingNode (Right prem) -> 
      return $ JSONGraphNode 
        { jgnId = show nid
        , jgnType = "missingNodePrem"
        , jgnLabel = ""
        , jgnMetadata = 
            Just JSONGraphNodeMetadata 
              { jgnPrems = 
                  [ JSONGraphNodeFact 
                      { jgnFactId    = show nid ++":p0"
                      , jgnFactTag   = ""
                      , jgnFactName  = ""
                      , jgnFactMult  = ""
                      , jgnFactTerms = []
                      , jgnFactShow = ""
                      }
                  ] 
              , jgnActs  = []
              , jgnConcs = []
              }
        }


-- | Determine the type of an edge.
getRelationType :: NodeConc -> NodePrem -> Graph -> String
getRelationType src tgt graph =
  let check p = maybe False p (resolveNodePremFact tgt graph) ||
                maybe False p (resolveNodeConcFact src graph)
      relationType | check isKFact          = "KFact"
                   | check isPersistentFact = "PersistentFact"
                   | check isProtoFact      = "ProtoFact"
                   | otherwise              = "default"
  in
    relationType

-- | Generate JSONGraphEdge from an edge of a abstract graph.
graphEdgeToJSONGraphEdge :: Edge -> RJSON JSONGraphEdge
graphEdgeToJSONGraphEdge (SystemEdge (src, tgt)) = do
  graph <- getGraph
  return $ JSONGraphEdge { jgeSource = show sid ++ ":c" ++ show concIdx
                , jgeTarget = show tid ++ ":p" ++ show premIdx
                , jgeRelation = getRelationType src tgt graph
                }
                where 
                  (sid, ConcIdx concIdx) = src
                  (tid, PremIdx premIdx) = tgt
graphEdgeToJSONGraphEdge (LessEdge (src, tgt, reason)) =
  return $ JSONGraphEdge { jgeSource = show src
                , jgeRelation = "LessAtoms"
                , jgeTarget = show tgt
                }
graphEdgeToJSONGraphEdge (UnsolvedChain (src, tgt)) = 
  return $ JSONGraphEdge { jgeSource = show sid ++ ":c" ++ show concIdx
                , jgeTarget = show tid ++ ":p" ++ show premIdx
                , jgeRelation = "unsolvedChain"
                }
                where 
                  (sid, ConcIdx concIdx) = src
                  (tid, PremIdx premIdx) = tgt

-- | Generate JSONGraphCluster from a cluster of an abstract graph.
graphClusterToJSONGraphCluster :: Cluster -> RJSON JSONGraphCluster 
graphClusterToJSONGraphCluster cluster = do
  jnodes <- mapM graphNodeToJSONGraphNode $ get cNodes cluster
  jedges <- mapM graphEdgeToJSONGraphEdge $ get cEdges cluster
  return $ JSONGraphCluster 
    { jgcName = get cName cluster
    , jgcNodes = jnodes
    , jgcEdges = jedges
    }

-- | Generate JSONGraphAbbrev from an abbreviation of an abstract graph.
graphAbbrevtoJSONGraphAbbrev :: (LNTerm, (LNTerm, LNTerm)) -> RJSON JSONGraphAbbrev
graphAbbrevtoJSONGraphAbbrev (term, (abbrev, recursiveExpansion)) = do
  pretty <- getPretty
  return JSONGraphAbbrev
    { jgaTerm = lntermToJSONGraphNodeTerm pretty term
    , jgaAbbrev = lntermToJSONGraphNodeTerm pretty abbrev
    , jgaExpansion = lntermToJSONGraphNodeTerm pretty recursiveExpansion
    }


-- | Generate JSON graph(s) data structure from an abstract graph.
sequentToJSONGraph :: String     -- ^ label of graph
                   -> RJSON JSONGraph
sequentToJSONGraph label = do
  graph <- getGraph
  let repr = get gRepr graph 
      abbrevs = get gAbbreviations graph
  jnodes <- mapM graphNodeToJSONGraphNode (L.get grNodes repr)
  jedges <- mapM graphEdgeToJSONGraphEdge (L.get grEdges repr)
  jclusters <- mapM graphClusterToJSONGraphCluster (L.get grClusters repr)
  jabbrevs <- mapM graphAbbrevtoJSONGraphAbbrev $ M.toList abbrevs
  return $ JSONGraph 
            { jgDirected = True
            , jgType  = "Tamarin prover constraint system"
            , jgLabel = label
            , jgNodes = jnodes
            , jgEdges = jedges
            , jgClusters = jclusters
            , jgAbbrevs = jabbrevs
            } 

sequentsToJSONGraphs :: Bool 
                     -> [(String, Graph)] 
                     -> JSONGraphs
sequentsToJSONGraphs pretty systems = 
    let jsonGraphs = map (\(label, graph) -> (`runReader` (pretty, graph)) $ sequentToJSONGraph label) systems in
    JSONGraphs {
      graphs = jsonGraphs
    }

-- | Generate JSON bytestring from an abstract graph.
sequentsToJSON :: GraphOptions -> [(String, System)] -> String
sequentsToJSON graphOptions systems =
  let graphs = map (\(label, system) -> (label, systemToGraph system graphOptions)) systems
      graphJSON = sequentsToJSONGraphs False graphs
  in
    BC.unpack $ encode graphJSON

-- | NOTE (dschoop): encodePretty encodes < and > as "\u003c" and "\u003e" respectively.
-- The encoding is removed with function removePseudoUnicode since Data.Strings.Util is non-standard.
-- The function encodePretty returns Data.ByteString.Lazy.Internal.ByteString containing
-- 8-bit bytes. However, eventually some other ByteString or String is expected by writeFile 
-- in /src/Web/Theory.hs.
sequentsToJSONPretty :: GraphOptions -> [(String, System)] -> String
sequentsToJSONPretty graphOptions systems =
  let graphs = map (\(label, system) -> (label, systemToGraph system graphOptions)) systems
      graphJSON = sequentsToJSONGraphs True graphs
  in
    removePseudoUnicode $ BC.unpack $ encodePretty graphJSON

-- | Generate JSON bytestring from an abstract graph and write to a file.
writeSequentAsJSONToFile :: FilePath -> GraphOptions -> String -> System -> IO ()
writeSequentAsJSONToFile fp graphOptions l se =
  do writeFile fp $ sequentsToJSON graphOptions [(l, se)]

-- | Generate JSON bytestring with pretty formatting from an abstract graph and write to a file.
writeSequentAsJSONPrettyToFile :: FilePath -> GraphOptions -> String -> System -> IO ()
writeSequentAsJSONPrettyToFile fp graphOptions l se =
  do writeFile fp $ sequentsToJSONPretty graphOptions [(l, se)]
