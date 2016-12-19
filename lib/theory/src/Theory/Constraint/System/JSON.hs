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
    sequentToJSON,                     
    writeSequentAsJSONToFile,
    sequentToJSONPretty,
    writeSequentAsJSONPrettyToFile
  ) where
import           Extension.Data.Label       as L (get)
import           Data.Aeson
import           Data.Aeson.TH
import           Data.Aeson.Encode.Pretty   -- to do pretty printing of JSON
import           Data.Foldable
import qualified Data.Map                   as M
import           Data.Maybe
import qualified Data.Set                   as S
import qualified Data.ByteString.Lazy.Char8 as BC (unpack)

import           Text.PrettyPrint.Class     -- for Doc and the pretty printing functions 
import           Theory.Constraint.System   
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
    {
      jgnFactId    :: String
    , jgnFactTag   :: String  -- ^ ProtoFact, FreshFact, OutFact, InFact, KUFact, KDFact, DedFact
    , jgnFactName  :: String  -- ^ Fr, Out, In, !KU, ...
    , jgnFactMult  :: String  -- ^ "!" = persistent, "" = linear
    , jgnFactTerms :: [JSONGraphNodeTerm]
    , jgnFactShow  :: String
    } deriving (Show)

-- | Representation of meta data of a JSON graph node.
data JSONGraphNodeMetadata = JSONGraphNodeMetadata 
    {
      jgnPrems :: [JSONGraphNodeFact]
    , jgnActs  :: [JSONGraphNodeFact]
    , jgnConcs :: [JSONGraphNodeFact]
    } deriving (Show)

-- | Representation of a node of a JSON graph.
data JSONGraphNode = JSONGraphNode 
    {
      jgnId :: String
    , jgnType :: String
    , jgnLabel :: String
    , jgnMetadata :: Maybe JSONGraphNodeMetadata
    } deriving (Show)

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

-- | Representation of an edge of a JSON graph.
data JSONGraphEdge = JSONGraphEdge 
    {
      jgeSource :: String
    , jgeRelation :: String
    , jgeTarget :: String
--  , jgeDirected :: Maybe Bool
--  , jgeLabel :: Maybe String
    } deriving (Show)

-- | Representation of a JSON graph.
data JSONGraph = JSONGraph 
   {
      jgDirected :: Bool
    , jgType :: String
    , jgLabel :: String
    , jgNodes :: [JSONGraphNode]
    , jgEdges :: [JSONGraphEdge]
--  , jgmetadata :: JSONGraphMetadata 
    } deriving (Show)

-- | Representation of a collection of JSON graphs.
data JSONGraphs = JSONGraphs 
    {
      graphs :: [JSONGraph]
    } deriving (Show)

-- | Derive ToJSON and FromJSON. 
concat <$> mapM (deriveJSON defaultOptions) [''JSONGraphNodeFact, ''JSONGraphNodeMetadata, ''JSONGraphEdge, ''JSONGraph, ''JSONGraphs]

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
    | isFreshRule r     = "isFreshRule"
    | isIRecvRule r     = "isIRecvRule"
    | isISendRule r     = "isISendRule"
    | isCoerceRule r    = "isCoerceRule"
    | isProtocolRule r  = "isProtocolRule"
    | otherwise         = "unknown rule type"

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

-- | Generate JSONGraphNode from node of sequent (metadata part).
-- Facts and actions as are represented as metadata to keep close to the original JSON graph schema.
nodeToJSONGraphNodeMetadata :: Bool -> (NodeId, RuleACInst) -> JSONGraphNodeMetadata
nodeToJSONGraphNodeMetadata pretty (n, ru) = 
    JSONGraphNodeMetadata { jgnPrems = map (factToJSONGraphNodeFact pretty "p" n) 
                                       $ zip [0..] $ L.get rPrems ru
                          , jgnActs  = map (itemToJSONGraphNodeFact pretty "action") $ L.get rActs ru 
                          , jgnConcs = map (factToJSONGraphNodeFact pretty "c" n) 
                                       $ zip [0..] $ L.get rConcs ru
                          }

-- | Generate JSONGraphNode from node of sequent.
nodeToJSONGraphNode :: Bool -> (NodeId, RuleACInst) -> JSONGraphNode
nodeToJSONGraphNode pretty (n, ru) = 
    JSONGraphNode { jgnId = show n
                  , jgnType = getRuleType ru
                  , jgnLabel = getRuleName ru
                  , jgnMetadata = Just (nodeToJSONGraphNodeMetadata pretty (n, ru))
                  }

-- | Determine the type of an edge.
getRelationType :: NodeConc -> NodePrem -> System -> String
getRelationType src tgt se =
    let check p = maybe False p (resolveNodePremFact tgt se) ||
                  maybe False p (resolveNodeConcFact src se)
        relationType | check isKFact          = "KFact"
                     | check isPersistentFact = "PersistentFact"
                     | check isProtoFact      = "ProtoFact"
                     | otherwise              = "default"
    in
    relationType

-- | Generate JSON data structure for lastAtom.
lastAtomToJSONGraphNode :: Maybe NodeId -> [JSONGraphNode]
lastAtomToJSONGraphNode n = case n of
    Nothing -> [] 
    Just n' -> [JSONGraphNode { jgnId = show n'
                              , jgnType = "lastAtom"
                              , jgnLabel = show n'
                              , jgnMetadata = Nothing 
                              }] 

-- | Generate JSON data structure for unsolvedActionAtom.
unsolvedActionAtomsToJSONGraphNode :: Bool -> (NodeId, LNFact) -> JSONGraphNode
unsolvedActionAtomsToJSONGraphNode pretty (n, f) =
    JSONGraphNode 
      { jgnId = show n
      , jgnType     = "unsolvedActionAtom"
      , jgnLabel    = case pretty of
                        True  -> pps $ prettyLNFact f
                        False -> ""
      , jgnMetadata = 
          Just JSONGraphNodeMetadata 
            { jgnPrems = []
            , jgnActs  = [itemToJSONGraphNodeFact pretty "action" f] 
            , jgnConcs = [] 
            }
     }    

{-|
  Generate a JSONGraphNode for those nodes in sEdges that are not present in sNodes. 
  This might occur in the case distinctions shown in the GUI.
  Since a fact is missing, the id is encoded as jgnFactId, could also be done directly in jgnId.
-}
missingNodesToJSONGraphNodes :: System -> [Edge] -> [JSONGraphNode]
missingNodesToJSONGraphNodes _ [] = []
missingNodesToJSONGraphNodes se ((Edge (sid, _) (tid, _)):el) 
    | notElem sid nodelist = 
         (JSONGraphNode 
            { jgnId = show sid
            , jgnType = "missingNodeConc"
            , jgnLabel = ""
            , jgnMetadata = 
                Just JSONGraphNodeMetadata 
                  { jgnPrems = []
                  , jgnActs  = []
                  , jgnConcs = 
                      [ JSONGraphNodeFact 
                          { jgnFactId    = show sid ++":c0"
                          , jgnFactTag   = ""
                          , jgnFactName  = ""
                          , jgnFactMult  = ""
                          , jgnFactTerms = []   
                          , jgnFactShow  = ""
                          }
                      ]
                  }
            }: missingNodesToJSONGraphNodes se el)
    | notElem tid nodelist = 
         (JSONGraphNode 
            { jgnId = show tid
            , jgnType = "missingNodePrem"
            , jgnLabel = ""
            , jgnMetadata = 
                Just JSONGraphNodeMetadata 
                  { jgnPrems = 
                      [ JSONGraphNodeFact 
                          { jgnFactId    = show tid ++":p0"
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
            }: missingNodesToJSONGraphNodes se el)
    | otherwise = (missingNodesToJSONGraphNodes se el)
    where 
      nodelist = map fst $ M.toList $ L.get sNodes se

-- | Generate JSON data structure for edges.
edgeToJSONGraphEdge :: System -> Edge -> JSONGraphEdge
edgeToJSONGraphEdge se (Edge src tgt)  =
    JSONGraphEdge { jgeSource = show sid ++ ":c" ++ show concidx
                  , jgeTarget = show tid ++ ":p" ++ show premidx
                  , jgeRelation = getRelationType src tgt se
                  }
                  where 
                    (sid, ConcIdx concidx) = src
                    (tid, PremIdx premidx) = tgt

-- | Generate JSON data structure for lessAtoms edge.
lessAtomsToJSONGraphEdge :: (NodeId, NodeId) -> JSONGraphEdge
lessAtomsToJSONGraphEdge (src, tgt) =
    JSONGraphEdge { jgeSource = show src
                  , jgeRelation = "LessAtoms"
                  , jgeTarget = show tgt
                  }

-- | Generate JSON data structure for unsolvedChain edge.
unsolvedchainToJSONGraphEdge :: (NodeConc, NodePrem) -> JSONGraphEdge
unsolvedchainToJSONGraphEdge (src, tgt)  =
    JSONGraphEdge { jgeSource = show sid ++ ":c" ++ show concidx
                  , jgeTarget = show tid ++ ":p" ++ show premidx
                  , jgeRelation = "unsolvedChain"
                  }
                  where 
                    (sid, ConcIdx concidx) = src
                    (tid, PremIdx premidx) = tgt

-- | Generate JSON graph(s) data structure from sequent.
sequentToJSONGraphs :: Bool       -- ^ determines whether facts etc are also pretty printed
                    -> String     -- ^ label of graph
                    -> System     -- ^ sequent to dump to JSON
                    -> JSONGraphs
sequentToJSONGraphs pretty label se = 
    JSONGraphs 
      { graphs = 
          [ JSONGraph 
              { jgDirected = True
              , jgType  = "Tamarin prover constraint system"
              , jgLabel = label
              , jgNodes = (map (nodeToJSONGraphNode pretty) $ M.toList $ L.get sNodes se)
                          ++ (lastAtomToJSONGraphNode $ L.get sLastAtom se)
                          ++ (map (unsolvedActionAtomsToJSONGraphNode pretty) $ unsolvedActionAtoms se)
                          ++ (missingNodesToJSONGraphNodes se $ S.toList $ L.get sEdges se)
              , jgEdges = (map (edgeToJSONGraphEdge se) $ S.toList $ L.get sEdges se)
                          ++ (map lessAtomsToJSONGraphEdge $ S.toList $ L.get sLessAtoms se)
                          ++ (map unsolvedchainToJSONGraphEdge $ unsolvedChains se)
              } 
          ] 
      }

-- | Generate JSON bytestring from sequent.
sequentToJSON :: String -> System -> String
sequentToJSON l se =
    BC.unpack $ encode (sequentToJSONGraphs False l se)

-- | NOTE (dschoop): encodePretty encodes < and > as "\u003c" and "\u003e" respectively.
-- The encoding is removed with function removePseudoUnicode since Data.Strings.Util is non-standard.
-- The function encodePretty returns Data.ByteString.Lazy.Internal.ByteString containing
-- 8-bit bytes. However, eventually some other ByteString or String is expected by writeFile 
-- in /src/Web/Theory.hs.
sequentToJSONPretty :: String -> System -> String
sequentToJSONPretty l se =
    removePseudoUnicode $ BC.unpack $ encodePretty $ sequentToJSONGraphs True l se

writeSequentAsJSONToFile :: FilePath -> String -> System -> IO ()
writeSequentAsJSONToFile fp l se =
    do writeFile fp $ sequentToJSON l se

writeSequentAsJSONPrettyToFile :: FilePath -> String -> System -> IO ()
writeSequentAsJSONPrettyToFile fp l se =
    do writeFile fp $ sequentToJSONPretty l se
