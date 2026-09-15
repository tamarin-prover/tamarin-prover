module Export.ProVerif.Header
  ( ProVerifHeader (..),
    BuiltinTranslation (..),
    builtins,
    stateHeaders,
    attribHeaders,
    filterHeaders,
    getProVerifHeaderIdentifier,
    checkDuplicates',
    finalizeHeaders,
  )
where

import Control.Monad (unless)
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Export.Types (Translation (..), TranslationContext (..), translationFail)
import Text.PrettyPrint.Class

-- ProVerif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProVerifHeader
  = Type String -- type declaration
  | Sym String String String [String] -- symbol declaration, (symkind,name,type,attr)
  | Fun String String Int String [String] -- symbol declaration, (symkind,name,arity,types,attr)
  | HEvent String String
  | Table String String
  | Eq String String String String -- eqtype, quantif, equation pub/priv
  deriving (Ord, Show, Eq)

stateHeaders :: Set.Set ProVerifHeader
stateHeaders =
  Set.fromList
    [ Table "tbl_states_handle" "(bitstring,channel)",
      Table "tbl_locks_handle" "(bitstring,channel)"
    ]

data BuiltinTranslation
  = NotSupportedBuiltin String
  | AccurateBuiltin [ProVerifHeader]
  | BestEffortBuiltin [ProVerifHeader]

builtins :: String -> BuiltinTranslation
builtins "diffie-hellman" =
  BestEffortBuiltin
    [ Sym "const" "g" ":bitstring" [],
      Fun "fun" "exp" 2 "(bitstring,bitstring):bitstring" [],
      Eq "equation" "forall a:bitstring,b:bitstring;" "exp( exp(g,a),b) = exp(exp(g,b),a)" ""
    ]
builtins "locations-report" =
  AccurateBuiltin [Fun "fun" "rep" 2 "(bitstring,bitstring):bitstring" ["private"]]
builtins "xor" =
  BestEffortBuiltin
    [ Fun "fun" "xor" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "zero" 0 "():bitstring" []
    ]
builtins "hashing" =
  AccurateBuiltin [Fun "fun" "h" 1 "(bitstring):bitstring" []]
builtins "asymmetric-encryption" =
  AccurateBuiltin
    [ Fun "fun" "aenc" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "pk" 1 "(bitstring):bitstring" []
    ]
builtins "signing" =
  AccurateBuiltin
    [ Fun "fun" "sign" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "pk" 1 "(bitstring):bitstring" [],
      Fun "fun" "okay" 0 "():bitstring" []
    ]
builtins "revealing-signing" =
  AccurateBuiltin
    [ Fun "fun" "revealSign" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "revealVerify" 3 "(bitstring,bitstring,bitstring):bitstring" [],
      Fun "fun" "getMessage" 1 "(bitstring):bitstring" [],
      Fun "fun" "pk" 1 "(bitstring):bitstring" [],
      Fun "fun" "okay" 0 "():bitstring" []
    ]
builtins "symmetric-encryption" =
  AccurateBuiltin [Fun "fun" "senc" 2 "(bitstring,bitstring):bitstring" []]
builtins "multiset" =
  NotSupportedBuiltin
    "Multiset is not supported in ProVerif. If you want to model natural numbers, you can use the dedicated Tamarin builtin."
builtins "bilinear-pairing" =
  NotSupportedBuiltin "Bilinear pairings are not supported in ProVerif."
builtins name
  | name
      `elem` [ "dest-pairing",
               "dest-asymmetric-encryption",
               "dest-signing",
               "dest-symmetric-encryption",
               "natural-numbers",
               "reliable-channel"
             ] = AccurateBuiltin []
builtins name =
  NotSupportedBuiltin
    ("Builtin `" ++ name ++ "` is not supported by this export backend.")

filterHeaders :: Set.Set ProVerifHeader -> Set.Set ProVerifHeader
filterHeaders = Set.filter (not . isForbidden)
  where
    isForbidden (Fun "fun" "true" _ _ _) = True
    isForbidden (Type "bitstring") = True
    isForbidden (Type "channel") = True
    isForbidden (Type "nat") = True
    isForbidden _ = False

getProVerifHeaderIdentifier :: ProVerifHeader -> Maybe String
getProVerifHeaderIdentifier (Fun _ name _ _ _) = Just name
getProVerifHeaderIdentifier (Sym _ name _ _) = Just name
getProVerifHeaderIdentifier (HEvent name _) = Just name
getProVerifHeaderIdentifier (Table name _) = Just name
getProVerifHeaderIdentifier _ = Nothing

checkDuplicates' :: Set.Set ProVerifHeader -> IO [ProVerifHeader]
checkDuplicates' headers = do
  unless (null conflicts) $
    translationFail $
      unlines
        ( "ProVerif constructs (functions, constants, events, tables) must be distinct. Please rename these duplicates:"
            : [intercalate ", " (map show definitions) | (_, definitions) <- conflicts]
        )
  pure (Set.toList headers)
  where
    identifiers =
      Map.fromListWith (<>)
        [ (name, [header])
        | header <- Set.toList headers,
          Just name <- [getProVerifHeaderIdentifier header]
        ]
    conflicts = Map.toList (Map.filter ((> 1) . length) identifiers)

prettyProVerifHeader :: ProVerifHeader -> Doc
prettyProVerifHeader = \case
  Type name -> text "type " <> text name <> text "."
  HEvent name headerType -> text "event " <> text name <> text headerType <> text "."
  Table name headerType -> text "table " <> text name <> text headerType <> text "."
  Eq equationType quantifier equation visibility ->
    text equationType <> text " " <> text quantifier <> text " " <> text equation <> text visibility <> text "."
  Sym symbolKind name symbolType [] -> text symbolKind <> text " " <> text name <> text symbolType <> text "."
  Sym symbolKind name symbolType attributes ->
    text symbolKind <> text " " <> text name <> text symbolType <> renderAttributes attributes <> text "."
  Fun functionKind name _ symbolType [] -> text functionKind <> text " " <> text name <> text symbolType <> text "."
  Fun functionKind name _ symbolType attributes ->
    text functionKind <> text " " <> text name <> text symbolType <> renderAttributes attributes <> text "."

prettyDeepSecHeader :: ProVerifHeader -> Doc
prettyDeepSecHeader = \case
  Type _ -> emptyDoc
  Eq "reduc" _ equation _ -> text "reduc" <> text " " <> text equation <> text "."
  Eq equationType _ equation _ ->
    translationFail $ "DeepSec does not support equations: " ++ equationType ++ " " ++ equation
  HEvent _ _ -> emptyDoc
  Table _ _ -> emptyDoc
  Sym symbolKind name _ attributes ->
    text symbolKind <> text " " <> text name <> privateAttribute attributes <> text "."
  Fun functionKind name arity _ attributes ->
    text functionKind
      <> text " "
      <> text name
      <> text "/"
      <> text (show arity)
      <> privateAttribute attributes
      <> text "."

renderAttributes :: [String] -> Doc
renderAttributes attributes =
  text "[" <> fsep (punctuate comma (map text attributes)) <> text "]"

privateAttribute :: [String] -> Doc
privateAttribute attributes
  | "private" `elem` attributes = text "[private]"
  | otherwise = emptyDoc

attribHeaders :: TranslationContext -> [ProVerifHeader] -> [Doc]
attribHeaders context headers = case context.trans of
  ProVerif ->
    intercalate
      [text ""]
      ( filter
          (not . null)
          [ titledBlock "Types" [prettyProVerifHeader h | h@(Type {}) <- headers],
            titledBlock "Free names" [prettyProVerifHeader h | h@(Sym {}) <- headers],
            titledBlock "Functions" [prettyProVerifHeader h | h@(Fun {}) <- headers],
            titledBlock "Equations" [prettyProVerifHeader h | h@(Eq {}) <- headers],
            titledBlock "Events" [prettyProVerifHeader h | h@(HEvent {}) <- headers],
            titledBlock "Tables" [prettyProVerifHeader h | h@(Table {}) <- headers]
          ]
      )
  DeepSec -> symbols ++ functions ++ equations
  where
    titledBlock title docs
      | null docs = []
      | otherwise = text ("(* " ++ title ++ " *)") : docs
    (equations, functions, symbols) = splitHeaders headers
    splitHeaders [] = ([], [], [])
    splitHeaders (header : rest)
      | Sym {} <- header = (equationDocs, functionDocs, prettyDeepSecHeader header : symbolDocs)
      | Fun {} <- header = (equationDocs, prettyDeepSecHeader header : functionDocs, symbolDocs)
      | Eq {} <- header = (prettyDeepSecHeader header : equationDocs, functionDocs, symbolDocs)
      | HEvent {} <- header = (prettyDeepSecHeader header : equationDocs, functionDocs, symbolDocs)
      | Table {} <- header = (prettyDeepSecHeader header : equationDocs, functionDocs, symbolDocs)
      | Type {} <- header = (equationDocs, functionDocs, prettyDeepSecHeader header : symbolDocs)
      where
        (equationDocs, functionDocs, symbolDocs) = splitHeaders rest

-- | Deduplicate, filter, and validate the collected headers.
finalizeHeaders :: Set.Set ProVerifHeader -> [Set.Set ProVerifHeader] -> IO [ProVerifHeader]
finalizeHeaders theoryHeaders translationHeaders =
  checkDuplicates' (filterHeaders (Set.unions (theoryHeaders : translationHeaders)))
