{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Pretty printing and parsing of Maude terms and replies.
module Term.Maude.Parser (
  -- * pretty printing of terms for Maude
    ppMaude
  , ppTheory

  -- * parsing of Maude replies
  , parseUnifyReply
  , parseMatchReply
  , parseVariantsReply
  , parseReduceReply
  ) where

import Term.LTerm
import Term.Maude.Types
import Term.Maude.Signature
import Term.Rewriting.Definitions

import Control.Monad.Bind

import Control.Basics

import Data.Maybe
import qualified Data.Set as S

import qualified Data.ByteString as B
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC

import Data.Attoparsec.ByteString.Char8

-- import Extension.Data.Monoid

------------------------------------------------------------------------------
-- Pretty printing of Maude terms.
------------------------------------------------------------------------

-- | Pretty print an 'LSort'.
ppLSort :: LSort -> ByteString
ppLSort s = case s of
    LSortPub       -> "Pub"
    LSortFresh     -> "Fresh"
    LSortMsg       -> "Msg"
    LSortNat       -> "TamNat"
    LSortNode      -> "Node"
    (LSortUser st) -> B.concat [funUserSymPrefix, BC.pack st]

ppLSortSym :: LSort -> ByteString
ppLSortSym lsort = case lsort of
    LSortFresh     -> "f"
    LSortPub       -> "p"
    LSortMsg       -> "c"
    LSortNode      -> "n"
    LSortNat       -> "t"
    (LSortUser st) -> B.concat ["tu", BC.pack st]

parseLSortSym :: ByteString -> Maybe LSort
parseLSortSym s = case s of
    "f"  -> Just LSortFresh
    "p"  -> Just LSortPub
    "c"  -> Just LSortMsg
    "n"  -> Just LSortNode
    "t"  -> Just LSortNat
    _    ->
      if BC.head s == 'u'
        then Just (LSortUser $ BC.unpack $ BC.tail s)
        else Nothing

-- | Used to prevent clashes with predefined Maude function symbols
--   like @true@
funSymPrefix :: ByteString
funSymPrefix = "tamX"

-- | Used to prevent clashes of user-defined symbols with built-in ones.
funUserSymPrefix :: ByteString
funUserSymPrefix = "tamU"

-- | Prefix for private function symbols.
funSymPrefixPriv :: ByteString
funSymPrefixPriv = "tamP"

-- | Replace underscores "_" with minus "-" for Maude.
replaceUnderscore :: ByteString -> ByteString
replaceUnderscore s = BC.map f s
    where
       f x | x == '_'  = '-'
       f x | otherwise = x

-- | Replace underscores "_" with minus "-" for Maude.
replaceUnderscoreFun :: NoEqSym -> NoEqSym
replaceUnderscoreFun (NoEqSym s arity priv sig) = NoEqSym (replaceUnderscore s) arity priv sig

-- | Replace minus "-" with underscores "_" when parsing back from Maude.
replaceMinus :: ByteString -> ByteString
replaceMinus s = BC.map f s
    where
       f x | x == '-'  = '_'
       f x | otherwise = x

-- | Replace minus "-" with underscores "_" when parsing back from Maude.
replaceMinusFun :: NoEqSym -> NoEqSym
replaceMinusFun (NoEqSym s arity priv sig) = NoEqSym (replaceMinus s) arity priv sig

-- | Pretty print an AC symbol for Maude.
ppMaudeACSym :: ACSym -> ByteString
ppMaudeACSym o =
    funSymPrefix <> case o of
                      Mult       -> "mult"
                      Union      -> "mun"
                      Xor        -> "xor"
                      NatPlus    -> "tplus"
                      UserAC f _ -> BC.pack f

-- | Pretty print a non-AC symbol for Maude.
ppMaudeNoEqSym :: NoEqSym -> ByteString
ppMaudeNoEqSym (NoEqSym o _ Private _) = funSymPrefixPriv <> o
ppMaudeNoEqSym (NoEqSym o _ Public  _) = funSymPrefix     <> o

-- | Pretty print a C symbol for Maude.
ppMaudeCSym :: CSym -> ByteString
ppMaudeCSym EMap = funSymPrefix <> emapSymString


-- | @ppMaude t@ pretty prints the term @t@ for Maude.
ppMaude :: Term MaudeLit -> ByteString
ppMaude t = case viewTerm t of
    Lit (MaudeVar i lsort)   -> "x" <> ppInt i <> ":" <> ppLSort lsort
    Lit (MaudeConst i lsort) -> ppLSortSym lsort <> "(" <> ppInt i <> ")"
    Lit (FreshVar _ _)       -> error "Term.Maude.Types.ppMaude: FreshVar not allowed"
    FApp (NoEq fsym) []      -> ppMaudeNoEqSym fsym
    FApp (NoEq fsym) as      -> ppMaudeNoEqSym fsym <> ppArgs as
    FApp (C fsym) as         -> ppMaudeCSym fsym    <> ppArgs as
    FApp (AC op) as          -> ppMaudeACSym op     <> ppArgs as
    FApp List as             -> "list(" <> ppList as <> ")"
  where
    ppArgs as     = "(" <> (B.intercalate "," (map ppMaude as)) <> ")"
    ppInt         = BC.pack . show
    ppList []     = "nil"
    ppList (x:xs) = "cons(" <> ppMaude x <> "," <> ppList xs <> ")"

------------------------------------------------------------------------------
-- Pretty printing a 'MaudeSig' as a Maude functional module.
------------------------------------------------------------------------------

-- | The term algebra and rewriting rules as a functional module in Maude.
ppTheory :: MaudeSig -> ByteString  --TODO-MY add the sorts and subsorts in maude
ppTheory msig = BC.unlines $
    [ "fmod MSG is"
    , "  protecting NAT ."
    , "  sort Pub Fresh Msg Node TamNat " <> theoryUserSortIds userSorts <> " TOP ."
    , "  subsort Pub < Msg ."
    , "  subsort Fresh < Msg ."
    , "  subsort TamNat < Msg ."
    , "  subsort Msg < TOP ."
    , "  subsort Node < TOP ."
    -- constants
    , "  op f : Nat -> Fresh ."
    , "  op p : Nat -> Pub ."
    , "  op c : Nat -> Msg ."
    , "  op n : Nat -> Node ."
    
    , "  op t : Nat -> TamNat ." ]
    ++
    -- user-defined sorts
    concatMap theoryUserSorts userSorts
    ++
    -- used for encoding FApp List [t1,..,tk]
    -- list(cons(t1,cons(t2,..,cons(tk,nil)..)))
    [ "  op list : TOP -> TOP ."
    , "  op cons : TOP TOP -> TOP ."
    , "  op nil  : -> TOP ." ]
    ++
    (if enableMSet msig
       then
       [ theoryOp "mun : Msg Msg -> Msg [comm assoc]" ]
       else [])
    ++
    (if enableDH msig
       then
       [ theoryOp "one : -> Msg"
       , theoryOp "exp : Msg Msg -> Msg"
       , theoryOp "mult : Msg Msg -> Msg [comm assoc]"
       , theoryOp "inv : Msg -> Msg" ]
       else [])
    ++
    (if enableBP msig
       then
       [ theoryOp "pmult : Msg Msg -> Msg"
       , theoryOp "em : Msg Msg -> Msg [comm]" ]
       else [])
    ++
    (if enableXor msig
       then
       [ theoryOp "zero : -> Msg"
       , theoryOp "xor : Msg Msg -> Msg [comm assoc]" ]
       else [])
    ++
    (if enableNat msig
       then
       [ theoryOp "tone : -> TamNat"
       , theoryOp $ "tplus : TamNat TamNat -> TamNat [comm assoc]" ]  --TODO-UNCERTAIN removed zero
       else [])
    ++
    (catMaybes $ map theoryUserACSyms (S.toList $ userACSyms msig))
    ++
    map theoryFunSym (S.toList $ stFunSyms msig)
    ++
    map theoryRule (S.toList $ rrulesForMaudeSig msig)
    ++
    [ "endfm" ]
  where
    userSorts = S.toList $ userSortsForMaudeSig msig

    theoryUserSortIds = BC.unwords . map ppLSort
    theoryUserSorts sort =
      [ "  subsort " <> ppLSort sort <> " < Msg ."
      , "  op " <> ppLSortSym sort <> " : Nat -> " <> ppLSort sort <> " ." ]
    theoryOpNoEq priv fsort =
        "  op " <> (if (priv==Private) then funSymPrefixPriv else funSymPrefix) <> fsort <>" ."
    theoryOp = theoryOpNoEq Public
    theoryFunSym (NoEqSym s ar priv sorts) =
        theoryOpNoEq priv (s <> " : " <> maybeCustomSorts ar sorts)
    maybeCustomSorts ar sorts = 
      maybe (theorySorts ar) (B.concat . theoryCustomSorts) sorts
    theorySorts ar = (B.concat $ replicate ar "Msg ") <> "-> Msg"
    theoryCustomSorts []     = []
    theoryCustomSorts [x]    = [BC.pack "-> ", sortMaudeName x]
    theoryCustomSorts (x:xs) = [sortMaudeName x, BC.pack " "] ++ theoryCustomSorts xs 

    theoryUserACSyms (UserAC f s) =
      let sort = sortMaudeName s 
      in  Just $ BC.concat
            [ "  op ", funSymPrefix, BC.pack f, " : ", sort, " ", sort
            , " -> ", sort, " [comm assoc] ."]
    theoryUserACSyms _            = Nothing

    -- Prefix non-builtin sorts with "tamU" prefix to avoid clashes
    sortMaudeName :: String -> ByteString
    sortMaudeName "Msg"   = BC.pack "Msg"
    sortMaudeName "Fresh" = BC.pack "Fresh"
    sortMaudeName "Pub"   = BC.pack "Pub"
    sortMaudeName "Nat"   = BC.pack "TamNat"
    sortMaudeName st      = B.concat [funUserSymPrefix, BC.pack st]
    theoryRule (l `RRule` r) =
        "  eq " <> ppMaude lm <> " = " <> ppMaude rm <> " [variant] ."
      where (lm,rm) = evalBindT ((,) <$> lTermToMTerm' l <*> lTermToMTerm' r) noBindings
                        `evalFresh` nothingUsed

-- Parser for Maude output
------------------------------------------------------------------------

-- | @parseUnifyReply reply@ takes a @reply@ to a unification query
--   returned by Maude and extracts the unifiers.
parseUnifyReply :: MaudeSig -> ByteString -> Either String [MSubst]
parseUnifyReply msig reply = flip parseOnly reply $
    choice [ string "No unifier." *> endOfLine *> pure []
           , many1 (parseSubstitution msig) ]
        <* endOfInput

-- | @parseMatchReply reply@ takes a @reply@ to a match query
--   returned by Maude and extracts the unifiers.
parseMatchReply :: MaudeSig -> ByteString -> Either String [MSubst]
parseMatchReply msig reply = flip parseOnly reply $
    choice [ string "No match." *> endOfLine *> pure []
           , many1 (parseSubstitution msig) ]
        <* endOfInput

-- | @parseVariantsReply reply@ takes a @reply@ to a variants query
--   returned by Maude and extracts the unifiers.
parseVariantsReply :: MaudeSig -> ByteString -> Either String [MSubst]
parseVariantsReply msig reply = flip parseOnly reply $ do
    endOfLine *> many1 parseVariant <* (string "No more variants.")
    <* endOfLine <* string "rewrites: "
    <* takeWhile1 isDigit <* endOfLine <* endOfInput
  where
    parseVariant = string "Variant #" *> takeWhile1 isDigit *> endOfLine *>
                   string "rewrites: " *> takeWhile1 isDigit *> endOfLine *>
                   parseReprintedTerm *> manyTill parseEntry endOfLine
    parseReprintedTerm = choice [ string "TOP" *> pure LSortMsg, parseSort ]
                         *> string ": " *> parseTerm msig <* endOfLine
    parseEntry = (,) <$> (flip (,) <$> (string "x" *> decimal <* string ":") <*> parseSort)
                     <*> (string " --> " *> parseTerm msig <* endOfLine)

-- | @parseSubstitution l@ parses a single substitution returned by Maude.
parseSubstitution :: MaudeSig -> Parser MSubst
parseSubstitution msig = do
    endOfLine *> string "Solution " *> takeWhile1 isDigit *> endOfLine
    choice [ string "empty substitution" *> endOfLine *> pure []
           , many1 parseEntry]
  where 
    parseEntry = (,) <$> (flip (,) <$> (string "x" *> decimal <* string ":") <*> parseSort)
                     <*> (string " --> " *> parseTerm msig <* endOfLine)

-- | @parseReduceReply l@ parses a single solution returned by Maude.
parseReduceReply :: MaudeSig -> ByteString -> Either String MTerm
parseReduceReply msig reply = flip parseOnly reply $ do
    string "result " *> choice [ string "TOP" *> pure LSortMsg, parseSort ] -- we ignore the sort
        *> string ": " *> parseTerm msig <* endOfLine <* endOfInput

-- | Parse an 'MSort'.
parseSort :: Parser LSort
parseSort =  string "Pub"      *> return LSortPub
         <|> string "Fresh"    *> return LSortFresh
         <|> string "Node"     *> return LSortNode
         <|> string "TamNat"   *> return LSortNat
         <|> userprefix        *> -- Sorts with tamU* are user-defined
               ( sortIdent    >>= return . LSortUser . BC.unpack )
         <|> string "M"        *> -- FIXME: why?
               ( string "sg"   *> return LSortMsg )
  where
    sortIdent = takeWhile1 (`BC.notElem` (":(,)\n " :: B.ByteString))
    userprefix = string funUserSymPrefix

-- | @parseTerm@ is a parser for Maude terms.
parseTerm :: MaudeSig -> Parser MTerm
parseTerm msig = choice
   [ string "#" *> (lit <$> (FreshVar <$> (decimal <* string ":") <*> parseSort))
   , string "%" *> (lit <$> (FreshVar <$> (decimal <* string ":") <*> parseSort))
   , do ident <- takeWhile1 (`BC.notElem` (":(,)\n " :: B.ByteString))
        choice [ do _ <- string "("
                    case parseLSortSym ident of
                      Just s  -> parseConst s
                      Nothing -> parseFApp ident
               , string ":" *> parseMaudeVariable ident
               , parseFAppConst ident
               ]
   ]
  where
    consSym = NoEqSym "cons" 2 Public Nothing
    nilSym  = NoEqSym "nil" 0 Public Nothing

    parseFunSym ident args
      | op `elem` allowedFunSyms = replaceMinusFun op
      | otherwise                =
          error $ "Maude.Parser.parseTerm: unknown function "
                  ++ "symbol `" ++ show op ++ "', not in "
                  ++ show allowedFunSyms
      where prefixLen      = BC.length funSymPrefix
            special        = ident `elem` ["list", "cons", "nil"]
            priv           = if (not special) && BC.isPrefixOf funSymPrefixPriv ident 
                               then Private else Public
            op_ident       = if special then ident else BC.drop prefixLen ident
            op             = 
              case lookup op_ident [ (noEqOp o, o) | o <- allowedFunSyms] of
                Just (NoEqSym _ _ _ sts) ->
                  NoEqSym op_ident (length args) priv sts
                Nothing ->
                  NoEqSym op_ident (length args) priv Nothing

            noEqOp (NoEqSym fs _ _ _) = fs
            allowedFunSyms =
              [consSym, nilSym, natOneSym]
              ++ (S.toList $ noEqFunSyms msig)

    parseConst s = lit <$> (flip MaudeConst s <$> decimal) <* string ")"

    parseFApp ident =
        appIdent <$> sepBy1 (parseTerm msig) (string ", ") <* string ")"
      where
        appIdent args  | ident == ppMaudeACSym Mult       = fAppAC Mult    args
                       | ident == ppMaudeACSym Union      = fAppAC Union   args
                       | ident == ppMaudeACSym NatPlus    = fAppAC NatPlus args
                       | ident == ppMaudeACSym Xor        = fAppAC Xor   args
                       | ident == ppMaudeCSym  EMap       = fAppC  EMap    args
                       | ident `elem` maudeUserACSymbols  = lookupUserAC ident userSyms args
          where
            userSyms = S.toList $ userACSyms msig
            maudeUserACSymbols = map ppMaudeACSym (S.toList $ userACSyms msig)
 
            lookupUserAC idn (sym:syms) as
              | idn == ppMaudeACSym sym  = fAppAC sym as
              | otherwise                = lookupUserAC idn syms as
            lookupUserAC idn [] _ = error $
              "Maude.Parser.parseTerm: error parsing user AC symbol: " ++ (BC.unpack idn)
       

        appIdent [arg] | ident == "list"                  = fAppList (flattenCons arg)
        appIdent args                                     = fAppNoEq op args
          where op = parseFunSym ident args

        flattenCons (viewTerm -> FApp (NoEq s) [x,xs]) | s == consSym = x:flattenCons xs
        flattenCons (viewTerm -> FApp (NoEq s)  [])    | s == nilSym  = []
        flattenCons t                                                 = [t]

    parseFAppConst ident = return $ fAppNoEq (parseFunSym ident []) []

    parseMaudeVariable ident =
        case BC.uncons ident of
            Just ('x', num) -> lit <$> (MaudeVar (read (BC.unpack num)) <$> parseSort)
            _               -> fail "invalid variable"
