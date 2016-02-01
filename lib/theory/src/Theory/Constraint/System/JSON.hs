{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- Copyright   : (c) 2016 Dominik Schoop
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Dominik Schoop dominik.schoop@hs-esslingen.de
-- Portability : GHC only
--
-- Conversion of the graph part of a sequent (constraint system) to a JSON graph format

{-
   TO DO:
   - generate JSON in non-interactive mode
   - encode historic information in the graph: sequence of nodes added
   - ??? give more information on type of node: e.g. isDestrRule, isConstrRule, ... 
   - ??? make it work for observational equivalence

   OPEN PROBLEMS:
   - JSON encodePretty converts < and > to "\u003c" and "\u003e"
     ghastly postprocessing has been applied to sequentToJSONPretty
-}

module Theory.Constraint.System.JSON (
    sequentToJSON,                     
    writeSequentAsJSONToFile,
    sequentToJSONPretty,               -- used as reference in imgThyPath (Theory.hs)
                                       -- change to sequentToJSON when tested
                                       -- via getTheoryGraphR (Handler.hs)
    writeSequentAsJSONPrettyToFile
  ) where
import           Extension.Data.Label       as L (get)
import           Data.Aeson
import           Data.Aeson.TH
import           Data.Aeson.Encode.Pretty   -- to do pretty printing of JSON
import qualified Data.Map                   as M
import           Data.Maybe
import qualified Data.Set                   as S
import qualified Data.ByteString.Lazy.Char8 as BC (unpack)

import           Text.PrettyPrint.Class     -- for Doc and the pretty printing functions 
import           Theory.Constraint.System   
import           Theory.Model

------------------------------------------------------------------------------
-- Data structure for JSON graphs                                           --
-- adapted from https://github.com/jsongraph/json-graph-specification       --
------------------------------------------------------------------------------

-- term in a JSON graph node, either in a fact, an action or an unsolvedActionAtom
data JSONGraphNodeTerm
  = Const { jgnConst :: String }
  | Funct { jgnFunct :: String, jgnParams :: [JSONGraphNodeTerm], jgnShow :: String }
  deriving (Show)

-- fact in a JSON graph node
data JSONGraphNodeFact = JSONGraphNodeFact {
    jgnFactId    :: String
  , jgnFactTag   :: String
  , jgnFactTerms :: [JSONGraphNodeTerm]
  , jgnFactShow  :: String
} deriving (Show)

-- meta data of JSON graph node
data JSONGraphNodeMetadata = JSONGraphNodeMetadata {
    jgnPrems :: [JSONGraphNodeFact] -- all could be done as optional
  , jgnActs  :: [JSONGraphNodeFact]
  , jgnConcs :: [JSONGraphNodeFact]
} deriving (Show)

-- node of a JSON graph
data JSONGraphNode = JSONGraphNode {
    jgnId :: String
  , jgnType :: String
  , jgnLabel :: String
  , jgnMetadata :: Maybe JSONGraphNodeMetadata
} deriving (Show)

-- optional fields are not handled correctly with automatically derived instances
-- hence, we have our own here
instance FromJSON JSONGraphNode where
    parseJSON = withObject "JSONGraphNode" $ \o -> JSONGraphNode
        <$> o .: "jgnId"
        <*> o .: "jgnType"
        <*> o .: "jgnLabel"
        <*> o .:? "jgnMetadata"

instance ToJSON JSONGraphNode where
    toJSON (JSONGraphNode jgnId jgnType jgnLabel jgnMetadata) = object $ catMaybes
        [ ("jgnId" .=) <$> pure jgnId      
        , ("jgnType" .=) <$> pure jgnType
        , ("jgnLabel" .=) <$> pure jgnLabel
        , ("jgnMetadata" .=) <$> jgnMetadata ]

-- edge of a JSON graph
data JSONGraphEdge = JSONGraphEdge {
    jgeSource :: String
  , jgeRelation :: String
  , jgeTarget :: String
--  , jgeDirected :: Maybe Bool
--  , jgeLabel :: Maybe String
} deriving (Show)

-- JSON graph
data JSONGraph = JSONGraph {
    jgDirected :: Bool
  , jgType :: String
  , jgLabel :: String
  , jgNodes :: [JSONGraphNode]
  , jgEdges :: [JSONGraphEdge]
--  , jgmetadata :: JSONGraphMetadata 
} deriving (Show)

-- collection of JSON graphs
data JSONGraphs = JSONGraphs {
    graphs :: [JSONGraph]
} deriving (Show)

-- 
concat <$> mapM (deriveJSON defaultOptions) [''JSONGraphNodeTerm, ''JSONGraphNodeFact, ''JSONGraphNodeMetadata, ''JSONGraphEdge, ''JSONGraph, ''JSONGraphs]

------------------------------------------------------------------------------
-- Generation of JSON text from JSON graphs                                 --
------------------------------------------------------------------------------

-- flatten out pretty printed facts from prettyLNFact etc.
cleanString :: [Char] -> [Char]
cleanString [] = []
cleanString (' ':'\n':' ':xs) = cleanString (' ':xs)
cleanString ('\n':xs) = cleanString xs
cleanString (' ':' ':xs) = cleanString (' ':xs)
cleanString (c:xs) = (c:cleanString xs)

-- convert output of pretty print functions to string
pps :: Doc -> String
pps d = cleanString $ render d

-- encodePretty encodes '<' as "\u003c" and '>' as "\u003e"
-- this function replaces these strings 
removePseudoUnicode :: [Char] -> [Char]
removePseudoUnicode [] = []
removePseudoUnicode ('\\':'u':'0':'0':'3':'c':xs) = ('<':removePseudoUnicode xs)
removePseudoUnicode ('\\':'u':'0':'0':'3':'e':xs) = ('>':removePseudoUnicode xs)
removePseudoUnicode (x:xs) = (x:removePseudoUnicode xs)

-- remove " from start and end of string
plainstring :: String -> String
plainstring ('\"':s) = reverse $ plainstring $ reverse s
plainstring s = s

-- generate JSON data structure from terms
-- "instance Show a" in Raw.hs served as example
lntermToJSONGraphNodeTerm :: LNTerm -> JSONGraphNodeTerm
lntermToJSONGraphNodeTerm t =
    case viewTerm t of
      Lit l                  -> Const { jgnConst  = show l }
      FApp   (NoEq (s,_)) [] -> Funct { jgnFunct  = plainstring $ show s, 
                                        jgnParams = [], 
                                        jgnShow   = show t }
      FApp   (NoEq (s,_)) as -> Funct { jgnFunct  = plainstring $ show s, 
                                        jgnParams = map lntermToJSONGraphNodeTerm as,
                                        jgnShow   = show t }
      FApp   (AC o) as       -> Funct { jgnFunct  = show o, 
                                        jgnParams = map lntermToJSONGraphNodeTerm as,
                                        jgnShow   = show t }
      _                      -> Const { jgnConst = "unknown term type: " ++ show t }

-- generate JSON data structure from facts in premises and conclusion of rules
-- since facts are ordered in the premises and conclusions, the ordering number as well as a prefix
-- ("p:" (premise) and "c:" (conclusion)) are given to the function 
factToJSONGraphNodeFact :: String -> NodeId -> (Int,LNFact) -> JSONGraphNodeFact
factToJSONGraphNodeFact prefix n (idx, f) =
     JSONGraphNodeFact { jgnFactId    = prefix ++ show n ++ ":" ++ show idx
                       , jgnFactTag   = show (factTag f)
                       , jgnFactTerms = map lntermToJSONGraphNodeTerm (factTerms f)
                       , jgnFactShow  = pps $ prettyLNFact f
                       }

-- generate JSON data structure from facts in actions
actToJSONGraphNodeFact :: LNFact -> JSONGraphNodeFact
actToJSONGraphNodeFact f =
     JSONGraphNodeFact { jgnFactId    = "action"
                       , jgnFactTag   = show (factTag f)
                       , jgnFactTerms = map lntermToJSONGraphNodeTerm (factTerms f)
                       , jgnFactShow  = pps $ prettyLNFact f
                       }

-- generate JSONGraphNode from node of sequent (metadata part)
-- facts and actions as metadata to keep close to the original JSON graph schema
nodeToJSONGraphNodeMetadata :: (NodeId, RuleACInst) -> JSONGraphNodeMetadata
nodeToJSONGraphNodeMetadata (n, ru) = 
    JSONGraphNodeMetadata { jgnPrems = map (factToJSONGraphNodeFact "p:" n) 
                                       $ zip [0..] $ L.get rPrems ru
                          , jgnActs  = map actToJSONGraphNodeFact $ L.get rActs ru 
                          , jgnConcs = map (factToJSONGraphNodeFact "c:" n) 
                                       $ zip [0..] $ L.get rConcs ru
                          }

-- generate JSONGraphNode from node of sequent
nodeToJSONGraphNode :: (NodeId, RuleACInst) -> JSONGraphNode
nodeToJSONGraphNode (n, ru) = 
    JSONGraphNode { jgnId = show n
                  , jgnType = "rule"
                  , jgnLabel = getRuleName ru
                  , jgnMetadata = Just (nodeToJSONGraphNodeMetadata (n, ru))
                  }

-- determine the type of an edge
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

-- generate JSON data structure for lastAtom
lastAtomToJSONGraphNode :: Maybe NodeId -> [JSONGraphNode]
lastAtomToJSONGraphNode n = case n of
    Nothing -> [] 
    Just n -> [JSONGraphNode { jgnId = show n
                             , jgnType = "lastAtom"
                             , jgnLabel = show n
                             , jgnMetadata = Nothing 
                             }] 

-- generate JSON data structure for unsolvedActionAtom
unsolvedActionAtomsToJSONGraphNode :: (NodeId, LNFact) -> JSONGraphNode
unsolvedActionAtomsToJSONGraphNode (n, f) =
    JSONGraphNode { jgnId = show n
                  , jgnType = "unsolvedActionAtom"
                  , jgnLabel = pps $ prettyLNFact f
                  , jgnMetadata = 
                      Just JSONGraphNodeMetadata { jgnPrems = []
                                                 , jgnActs  = [actToJSONGraphNodeFact f] 
                                                 , jgnConcs = [] 
                                                 }
                  }    

-- generate a JSONGraphNode for those nodes in sEdges that are not present in sNodes 
-- might occur in the case distinctions shown in the GUI
-- since a fact is missing, the id is encoded as jgnFactId, could also be done directly in jgnId
missingNodesToJSONGraphNodes :: System -> [Edge] -> [JSONGraphNode]
missingNodesToJSONGraphNodes _ [] = []
missingNodesToJSONGraphNodes se ((Edge src tgt):el) 
    | notElem sid nodelist = 
         (JSONGraphNode { jgnId = show sid
                        , jgnType = "missingNodeConc"
                        , jgnLabel = ""
                        , jgnMetadata = Just JSONGraphNodeMetadata 
                              { jgnPrems = []
                              , jgnActs  = []
                              , jgnConcs = [JSONGraphNodeFact 
                                                { jgnFactId    = "c:"++ show sid ++":0"
                                                , jgnFactTag   = ""
                                                , jgnFactTerms = []   
                                                , jgnFactShow  = ""
                                                }]
                              }
                          }: missingNodesToJSONGraphNodes se el)
    | notElem tid nodelist = 
         (JSONGraphNode { jgnId = show tid
                        , jgnType = "missingNodePrem"
                        , jgnLabel = ""
                        , jgnMetadata = Just JSONGraphNodeMetadata 
                             { jgnPrems = [JSONGraphNodeFact 
                                               { jgnFactId    = "p:"++ show tid ++":0"
                                               , jgnFactTag   = ""
                                               , jgnFactTerms = []
                                               , jgnFactShow = ""
                                               }] 
                             , jgnActs  = []
                             , jgnConcs = []
                             }
                          }: missingNodesToJSONGraphNodes se el)
    | otherwise = (missingNodesToJSONGraphNodes se el)
    where 
     (sid, ConcIdx concidx) = src
     (tid, PremIdx premidx) = tgt
     nodelist = map fst $ M.toList $ L.get sNodes se

-- generate JSON data structure for edges
edgeToJSONGraphEdge :: System -> Edge -> JSONGraphEdge
edgeToJSONGraphEdge se (Edge src tgt)  =
    JSONGraphEdge { jgeSource = "c:" ++ show sid ++ ":" ++ show concidx
                  , jgeTarget = "p:" ++ show tid ++ ":" ++ show premidx
                  , jgeRelation = getRelationType src tgt se
                  }
                  where 
                    (sid, ConcIdx concidx) = src
                    (tid, PremIdx premidx) = tgt

-- generate JSON data structure for lessAtoms edge
lessAtomsToJSONGraphEdge :: (NodeId, NodeId) -> JSONGraphEdge
lessAtomsToJSONGraphEdge (src, tgt) =
    JSONGraphEdge { jgeSource = show src
                  , jgeRelation = "LessAtoms"
                  , jgeTarget = show tgt
                  }

-- generate JSON data structure for unsolvedChain edge
unsolvedchainToJSONGraphEdge :: (NodeConc, NodePrem) -> JSONGraphEdge
unsolvedchainToJSONGraphEdge (src, tgt)  =
    JSONGraphEdge { jgeSource = "c:" ++ show sid ++ ":" ++ show concidx
                  , jgeTarget = "p:" ++ show tid ++ ":" ++ show premidx
                  , jgeRelation = "unsolvedChain"
                  }
                  where 
                    (sid, ConcIdx concidx) = src
                    (tid, PremIdx premidx) = tgt

-- generate JSON graph(s) data structure from sequent
sequentToJSONGraphs :: String -> System -> JSONGraphs
sequentToJSONGraphs label se = 
    JSONGraphs 
    { graphs = [ JSONGraph 
                 { jgDirected = True
                 , jgType  = "Tamarin prover constraint system"
                 , jgLabel = label
                 , jgNodes = (map nodeToJSONGraphNode $ M.toList $ L.get sNodes se)
                             ++ (lastAtomToJSONGraphNode $ L.get sLastAtom se)
                             ++ (map unsolvedActionAtomsToJSONGraphNode $ unsolvedActionAtoms se)
                             ++ (missingNodesToJSONGraphNodes se $ S.toList $ L.get sEdges se)
                 , jgEdges = (map (edgeToJSONGraphEdge se) $ S.toList $ L.get sEdges se)
                             ++ (map lessAtomsToJSONGraphEdge $ S.toList $ L.get sLessAtoms se)
                             ++ (map unsolvedchainToJSONGraphEdge $ unsolvedChains se)
                 } 
               ] 
    }

-- generate JSON bytestring from sequent  
sequentToJSON :: String -> System -> String
sequentToJSON l se =
    BC.unpack $ encode (sequentToJSONGraphs l se)

-- NOTE: encodePretty encodes < and > as "\u003c" and "\u003e" respectively
-- removal with own function removePseudoUnicode since Data.Strings.Util non-standard
sequentToJSONPretty :: String -> System -> String
sequentToJSONPretty l se =
    removePseudoUnicode $ BC.unpack $ encodePretty $ sequentToJSONGraphs l se

writeSequentAsJSONToFile :: FilePath -> String -> System -> IO ()
writeSequentAsJSONToFile fp l se =
    do writeFile fp $ sequentToJSON l se

writeSequentAsJSONPrettyToFile :: FilePath -> String -> System -> IO ()
writeSequentAsJSONPrettyToFile fp l se =
    do writeFile fp $ sequentToJSONPretty l se

