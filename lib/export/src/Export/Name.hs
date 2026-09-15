-- |
-- Deterministic target-name allocation shared by exporter components.
module Export.Name
  ( TargetNamespace (..),
    TargetEvent (..),
    TargetVariable (..),
    NameAllocator,
    emptyNameAllocator,
    reserveNames,
    allocateEvent,
    allocateVariable,
    freshNameAvoiding,
    sanitizeSymbol,
  )
where

import Data.Char (isDigit)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

data TargetNamespace
  = GlobalNamespace
  | VariableNamespace
  deriving (Eq, Ord, Show)

newtype TargetEvent = TargetEvent {targetEventText :: String}
  deriving (Eq, Ord, Show)

newtype TargetVariable = TargetVariable String
  deriving (Eq, Ord, Show)

newtype NameAllocator = NameAllocator (Map.Map TargetNamespace (Set.Set String))
  deriving (Eq, Show)

emptyNameAllocator :: NameAllocator
emptyNameAllocator = NameAllocator Map.empty

reserveNames :: TargetNamespace -> Set.Set String -> NameAllocator -> NameAllocator
reserveNames namespace names (NameAllocator allocated) =
  NameAllocator (Map.insertWith Set.union namespace names allocated)

allocateEvent :: String -> NameAllocator -> (TargetEvent, NameAllocator)
allocateEvent preferred allocator =
  let (name, allocator') = allocate GlobalNamespace preferred allocator
   in (TargetEvent name, allocator')

allocateVariable :: String -> NameAllocator -> (TargetVariable, NameAllocator)
allocateVariable preferred allocator =
  let (name, allocator') = allocate VariableNamespace preferred allocator
   in (TargetVariable name, allocator')

allocate :: TargetNamespace -> String -> NameAllocator -> (String, NameAllocator)
allocate namespace preferred allocator =
  (chosen, reserveNames namespace (Set.singleton chosen) allocator)
  where
    used = namesIn namespace allocator
    chosen = freshNameAvoiding "_" used preferred

namesIn :: TargetNamespace -> NameAllocator -> Set.Set String
namesIn namespace (NameAllocator allocated) =
  Map.findWithDefault Set.empty namespace allocated

-- | Choose a deterministic fresh spelling while preserving the preferred
-- name when it is available. The separator lets callers retain established
-- target spellings such as @t1@ and @rid_foo_1@.
freshNameAvoiding :: String -> Set.Set String -> String -> String
freshNameAvoiding separator used preferred
  | preferred `Set.notMember` used = preferred
  | otherwise =
      head
        [ candidate
        | suffix <- [(1 :: Integer) ..],
          let candidate = preferred ++ separator ++ show suffix,
          candidate `Set.notMember` used
        ]

sanitizeSymbol :: Char -> String -> String
sanitizeSymbol prefix name
  | name `elem` reservedWords || startsWithDigit name = prefix : name
  | otherwise = name
  where
    startsWithDigit (firstCharacter : _) = isDigit firstCharacter
    startsWithDigit [] = False

reservedWords :: [String]
reservedWords =
  [ "among",
    "axiom",
    "channel",
    "choice",
    "clauses",
    "const",
    "def",
    "diff",
    "do",
    "elimtrue",
    "else",
    "equation",
    "equivalence",
    "event",
    "expand",
    "fail",
    "for",
    "forall",
    "foreach",
    "free",
    "fun",
    "get",
    "if",
    "implementation",
    "in",
    "inj-event",
    "insert",
    "lemma",
    "let",
    "letfun",
    "letproba",
    "new",
    "noninterf",
    "noselect",
    "not",
    "nounif",
    "or",
    "otherwise",
    "out",
    "param",
    "phase",
    "pred",
    "proba",
    "process",
    "proof",
    "public_vars",
    "putbegin",
    "query",
    "reduc",
    "restriction",
    "secret",
    "select",
    "set",
    "sid",
    "suchthat",
    "sync",
    "table",
    "then",
    "type",
    "weaksecret",
    "yield"
  ]
