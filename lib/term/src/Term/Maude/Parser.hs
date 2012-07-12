{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections #-}
{-# LANGUAGE ViewPatterns, NamedFieldPuns #-}
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
  , parseReduceReply
  ) where

import Term.LTerm
import Term.Maude.Types
import Term.Maude.Signature
import Term.Rewriting.Definitions

import Control.Monad.Bind

import Control.Basics

import qualified Data.Set as S

import qualified Data.ByteString as B
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC

import Data.Attoparsec.ByteString.Char8

import Extension.Data.Monoid

------------------------------------------------------------------------------
-- Pretty printing of Maude terms.
------------------------------------------------------------------------

-- | Pretty print an 'LSort'.
ppLSort :: LSort -> ByteString
ppLSort s = case s of
    LSortPub   -> "Pub"
    LSortFresh -> "Fresh"
    LSortMsg   -> "Msg"
    LSortNode  -> "Node"

ppLSortSym :: LSort -> ByteString
ppLSortSym lsort = case lsort of
    LSortFresh -> "f"
    LSortPub   -> "p"
    LSortMsg   -> "c"
    LSortNode  -> "n"

parseLSortSym :: ByteString -> Maybe LSort
parseLSortSym s = case s of
    "f"  -> Just LSortFresh
    "p"  -> Just LSortPub
    "c"  -> Just LSortMsg
    "n"  -> Just LSortNode
    _    -> Nothing

-- | Used to prevent clashes with predefined Maude function symbols
--   like @true@
funSymPrefix :: ByteString
funSymPrefix = "tamX"

-- | Pretty print an AC symbol for Maude.
ppMaudeACSym :: ACSym -> ByteString
ppMaudeACSym o =
    funSymPrefix <> obs
  where obs = case o of
                  Mult  -> "mult"
                  Union -> "mun"
                  Xor   -> "xor"

-- | Pretty print an AC symbol for Maude.
ppMaudeNonACSym :: NonACSym -> ByteString
ppMaudeNonACSym (o,_) = funSymPrefix <> o


-- | @ppMaude t@ pretty prints the term @t@ for Maude.
ppMaude :: Term MaudeLit -> ByteString
ppMaude t = case viewTerm t of
    Lit (MaudeVar i lsort)   -> "x" <> ppInt i <> ":" <> ppLSort lsort
    Lit (MaudeConst i lsort) -> ppLSortSym lsort <> "(" <> ppInt i <> ")"
    Lit (FreshVar _ _)       -> error "Term.Maude.Types.ppMaude: FreshVar not allowed"
    FApp (NonAC fsym) [] -> ppMaudeNonACSym fsym
    FApp (NonAC fsym) as ->
        ppMaudeNonACSym fsym <> "(" <> (B.intercalate "," (map ppMaude as)) <> ")"
    FApp (AC op) as          ->
        ppMaudeACSym op <> "(" <> (B.intercalate "," (map ppMaude as)) <> ")"
    FApp List as             ->
        funSymPrefix <> "list(" <> ppList as <> ")"
  where
    ppInt         = BC.pack . show
    ppList []     = funSymPrefix <> "nil"
    ppList (x:xs) = funSymPrefix <> "cons(" <> ppMaude x <> "," <> ppList xs <> ")"

------------------------------------------------------------------------------
-- Pretty printing a 'MaudeSig' as a Maude functional module.
------------------------------------------------------------------------------

-- | The term algebra and rewriting rules as a functional module in Maude.
ppTheory :: MaudeSig -> ByteString
ppTheory msig = BC.unlines $
    [ "fmod MSG is"
    , "  protecting NAT ." ]
    ++
    (if enableMSet msig
     then [ "  sort Pub Fresh Msg Node TOP ."
          , "  op " <> funSymPrefix <> "mun : Msg Msg -> Msg [comm assoc] ."
          , "  op " <> funSymPrefix <> "empty : -> Msg ."
          ]
     else [ "  sort Pub Fresh Msg Node TOP ."])
    ++
    [ "  subsort Pub < Msg ."
    , "  subsort Fresh < Msg ."
    , "  subsort Msg < TOP ."
    , "  subsort Node < TOP ."
    -- constants
    , "  op f : Nat -> Fresh ."
    , "  op p : Nat -> Pub ."
    , "  op c : Nat -> Msg ."
    , "  op n : Nat -> Node ."
    -- used for encoding FApp List [t1,..,tk]
    -- list(cons(t1,cons(t2,..,cons(tk,nil)..)))
    , "  op " <> funSymPrefix <> "list : TOP -> TOP ."
    , "  op " <> funSymPrefix <> "cons : TOP TOP -> TOP ."
    , "  op " <> funSymPrefix <> "nil  : -> TOP ." ]
    ++
    (if enableDH msig
       then
       [ "  op " <> funSymPrefix <> "one : -> Msg ."
       , "  op " <> funSymPrefix <> "exp : Msg Msg -> Msg ."
       , "  op " <> funSymPrefix <> "mult : Msg Msg -> Msg [comm assoc] ."
       , "  op " <> funSymPrefix <> "inv : Msg -> Msg ." ]
       else [])
    ++
    (if enableXor msig
       then
       [ "  op " <> funSymPrefix <> "zero : -> Msg ."
       , "  op " <> funSymPrefix <> "xor : Msg Msg -> Msg [comm assoc] ."]
       else [])
    ++
    map theoryFunSym (S.toList $ functionSymbols msig)
    ++
    map theoryRule (S.toList $ rrulesForMaudeSig msig)
    ++
    [ "endfm" ]
  where
    theoryFunSym (s,ar) =
        "  op " <> funSymPrefix <> s <> " : " <> (B.concat $ replicate ar "Msg ") <> " -> Msg ."
    theoryRule (l `RRule` r) =
        "  eq " <> ppMaude lm <> " = " <> ppMaude rm <> " ."
      where (lm,rm) = evalBindT ((,) <$>  lTermToMTerm' l <*> lTermToMTerm' r) noBindings
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
         <|> string "M"        *>
               (    string "sg"  *> return LSortMsg )


-- | @parseTerm@ is a parser for Maude terms.
parseTerm :: MaudeSig -> Parser MTerm
parseTerm msig = choice
   [ string "#" *> (lit <$> (FreshVar <$> (decimal <* string ":") <*> parseSort))
   , do ident <- takeWhile1 (`BC.notElem` (":(,)\n " :: B.ByteString))
        choice [ do string "("
                    case parseLSortSym ident of
                      Just s  -> parseConst s
                      Nothing -> parseFApp ident
               , string ":" *> parseMaudeVariable ident
               , parseFAppConst ident
               ]
   ]
  where
    parseConst s = lit <$> (flip MaudeConst s <$> decimal) <* string ")"

    parseFApp ident =
        appIdent <$> sepBy1 (parseTerm msig) (string ", ") <* string ")"
      where
        appIdent args  | ident == ppMaudeACSym Mult      = fAppAC Mult  args
                       | ident == ppMaudeACSym Xor       = fAppAC Xor   args
                       | ident == ppMaudeACSym Union     = fAppAC Union args
        appIdent [arg] | ident == funSymPrefix <> "list" = fAppList (flattenCons arg)
        appIdent args                                    =
            ensureValidOp op (fAppNonAC op args)
          where op = (BC.drop prefixLen ident, length args)

        flattenCons (viewTerm -> FApp (NonAC ("cons",2)) [x,xs]) = x:flattenCons xs
        flattenCons (viewTerm -> FApp (NonAC ("nil",0))  [])     = []
        flattenCons t                                            = [t]

    parseFAppConst ident = return $ ensureValidOp op (fAppNonAC op [])
      where op = (BC.drop prefixLen ident,0)

    parseMaudeVariable ident =
        case BC.uncons ident of
            Just ('x', num) -> lit <$> (MaudeVar (read (BC.unpack num)) <$> parseSort)
            _               -> fail "invalid variable"

    prefixLen = BC.length funSymPrefix
    ensureValidOp op x | op `elem` [("cons",2), ("nil",0)]      = x
                       | op `S.member` allFunctionSymbols msig  = x
                       | otherwise = error $ "Maude.Parser.parseTerm: unknown function"
                                             ++ "symbol `"++ show op ++"'"
