{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings   #-}

-- |
-- Build the readable analysis artifacts for an eviction store. Both
-- store.jsonl and the per-lemma trees come from one immutable store.bin
-- snapshot, so they always refer to the same complete-record prefix.
module Theory.Constraint.Solver.TreeExport
  ( writeStoreExports
  ) where

import           Theory.Constraint.Solver.ProofMethod (ProofMethod (..), Result (..))
import           Theory.Constraint.Solver.Store       (Kind (..), LemmaRoot (..),
                                                        MethodEdge (..),
                                                        Ref, StoredRecord (..),
                                                        decodeStoredRecord, readStoreRecords,
                                                        refText, valueRef, writeStoreJSON)
import           Theory.Constraint.System             (SystemTraceQuantifier (..),
                                                        prettyGoal)
import           Theory.Text.Pretty                    (render)

import           Data.Aeson                           (Value, object, (.=))
import qualified Data.Aeson                           as JSON
import qualified Data.Binary                          as Binary
import           Data.List                            (sortOn)
import qualified Data.Map                             as Map
import qualified Data.Set                             as Set
import           System.FilePath                      ((</>))

-- | Write store.jsonl and every available lemma tree next to store.bin.
writeStoreExports :: FilePath -> IO [FilePath]
writeStoreExports storeDirectory = do
    storedRecords <- readStoreRecords storeDirectory
    lemmaTreePaths <- writeLemmaTrees storeDirectory storedRecords
    storeJSONPath <- writeStoreJSON storeDirectory storedRecords
    pure (storeJSONPath : lemmaTreePaths)

-- | Reconstruct and write all lemma trees contained in a store snapshot.
writeLemmaTrees :: FilePath -> [StoredRecord] -> IO [FilePath]
writeLemmaTrees storeDirectory storedRecords = mapM writeLemmaTree lemmaRoots
  where
    lemmaRoots :: [LemmaRoot]
    lemmaRoots = sortOn (\root -> root.lrLemma) $ Map.elems $ Map.fromList
      [ (lemmaRoot.lrLemma, lemmaRoot)
      | lemmaRoot <- decodeRecords KLemmaRoot storedRecords
      ]

    methodEdgesBySystem :: Map.Map Ref MethodEdge
    methodEdgesBySystem = Map.fromList
      [ (methodEdge.meSubject, methodEdge)
      | methodEdge <- decodeRecords KMethodEdge storedRecords
      ]

    storedSystemRefs :: Set.Set Ref
    storedSystemRefs = Set.fromList
      [ record.storedKey
      | record <- storedRecords
      , record.storedKind == KShell
      ]

    writeLemmaTree :: LemmaRoot -> IO FilePath
    writeLemmaTree lemmaRoot = do
        let (rootJSON, proofStatus) =
              buildTreeNode storedSystemRefs methodEdgesBySystem
                            Set.empty lemmaRoot.lrRoot
            treePath = storeDirectory
                       </> (sanitizeFileName lemmaRoot.lrLemma ++ ".tree.json")
        JSON.encodeFile treePath $ object
          [ "lemma"      .= lemmaRoot.lrLemma
          , "quantifier" .= quantifierText lemmaRoot.lrTraceQuantifier
          , "status"     .= exportStatusText proofStatus
          , "root"       .= rootJSON
          ]
        pure treePath

-- | Build one nested proof tree and its aggregate status.
buildTreeNode :: Set.Set Ref
              -> Map.Map Ref MethodEdge
              -> Set.Set Ref
              -> Ref
              -> (Value, ExportStatus)
buildTreeNode storedSystemRefs methodEdgesBySystem ancestorRefs systemRef
  | systemRef `Set.member` ancestorRefs =
      error ("cycle in stored method edges at " ++ show systemRef)
  | systemRef `Set.notMember` storedSystemRefs =
      error ("lemma tree references missing system " ++ show systemRef)
  | otherwise =
      case Map.lookup systemRef methodEdgesBySystem of
        Nothing         -> unexpandedNode
        Just methodEdge -> expandedNode methodEdge
  where
    unexpandedNode :: (Value, ExportStatus)
    unexpandedNode =
      ( object [ "method"   .= ("unexpanded" :: String)
               , "system"   .= refText systemRef
               , "children" .= object []
               ]
      , ExportIncomplete
      )

    expandedNode :: MethodEdge -> (Value, ExportStatus)
    expandedNode methodEdge =
        let nextAncestorRefs = Set.insert systemRef ancestorRefs
            childResults = Map.map
              (buildTreeNode storedSystemRefs methodEdgesBySystem
                             nextAncestorRefs)
              methodEdge.meChildren
            childNodes = Map.map fst childResults
            childStatuses = map snd (Map.elems childResults)
            proofStatus = maximum
              (exportStatusForMethod methodEdge.meMethod : childStatuses)
        in ( object [ "method"   .= methodToJSON methodEdge.meMethod
                    , "system"   .= refText systemRef
                    , "children" .= childNodes
                    ]
           , proofStatus
           )

-- | Export a proof method in the existing tree-file schema.
methodToJSON :: ProofMethod -> Value
methodToJSON (SolveGoal goal) = object
    [ "solveGoal" .= object
        [ "ref"    .= refText (valueRef KGoal goal)
        , "pretty" .= render (prettyGoal goal)
        ]
    ]
methodToJSON Simplify          = JSON.toJSON ("simplify" :: String)
methodToJSON Induction         = JSON.toJSON ("induction" :: String)
methodToJSON (Sorry reason)    = object ["sorry" .= reason]
methodToJSON Invalidated       = JSON.toJSON ("invalidated" :: String)
methodToJSON (Finished result) = object ["finished" .= resultText result]

resultText :: Result -> String
resultText Solved            = "solved"
resultText Unfinishable      = "unfinishable"
resultText (Contradictory _) = "contradiction"

-- | Constructors are ordered from the least to the most important status.
data ExportStatus
  = ExportComplete
  | ExportUnfinishable
  | ExportIncomplete
  | ExportTrace
  | ExportInvalidated
  deriving (Eq, Ord)

exportStatusForMethod :: ProofMethod -> ExportStatus
exportStatusForMethod Invalidated                  = ExportInvalidated
exportStatusForMethod (Finished Solved)            = ExportTrace
exportStatusForMethod (Finished Unfinishable)      = ExportUnfinishable
exportStatusForMethod (Sorry _)                    = ExportIncomplete
exportStatusForMethod _                            = ExportComplete

exportStatusText :: ExportStatus -> String
exportStatusText ExportComplete       = "completeProof"
exportStatusText ExportUnfinishable   = "unfinishableProof"
exportStatusText ExportIncomplete     = "incompleteProof"
exportStatusText ExportTrace          = "traceFound"
exportStatusText ExportInvalidated    = "invalidatedProof"

quantifierText :: SystemTraceQuantifier -> String
quantifierText ExistsNoTrace   = "AllTraces"
quantifierText ExistsSomeTrace = "ExistsTrace"

-- | Decode every record of one kind or fail with record identity.
decodeRecords :: Binary.Binary a => Kind -> [StoredRecord] -> [a]
decodeRecords requestedKind storedRecords = map decodeRecord matchingRecords
  where
    matchingRecords :: [StoredRecord]
    matchingRecords = filter hasRequestedKind storedRecords

    hasRequestedKind :: StoredRecord -> Bool
    hasRequestedKind record = record.storedKind == requestedKind

    decodeRecord record =
        case decodeStoredRecord record of
          Right value       -> value
          Left decodeError  -> error
            ("binary decode of " ++ show record.storedKey ++ " ("
             ++ show record.storedKind ++ "): " ++ decodeError)

sanitizeFileName :: String -> String
sanitizeFileName name = map replaceCharacter name
  where
    replaceCharacter character
      | character == '/' || character == ' ' = '_'
      | otherwise                            = character
