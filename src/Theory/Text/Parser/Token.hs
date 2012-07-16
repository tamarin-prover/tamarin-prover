{-# LANGUAGE TupleSections #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Tokenizing infrastructure
module Theory.Text.Parser.Token (
  -- * Tokens
    integer
  , string
  , strings

  -- ** Text passages
  , TextType(..)
  , text

  -- * Identifiers and Variables
  , identifier
  , indexedIdentifier

  , freshName
  , pubName

  , sortedLVar
  , lvar
  , msgvar
  , nodevar

  -- * Operators
  , opExp
  , opMult

  , opEqual
  , opLess
  , opAt
  , opForall
  , opExists
  , opImplies
  , opLEquiv
  , opLAnd
  , opLOr
  , opLNot

  -- ** Pseudo operators
  , equalSign
  , opDot
  , opComma
  , opSharp
  , opBang
  , opSlash
  , opColon
  , opMinus
  , opLeftarrow
  , opRightarrow
  , opLongleftarrow
  , opLongrightarrow

  -- * Parentheses/quoting
  , braced
  , parens
  , angled
  , singleQuoted
  , doubleQuoted

  -- * List parsing
  , commaSep
  , commaSep1
  , list

    -- * Basic Parsing
  , Parser
  , parseFile
  , parseFromString
  ) where

import           Prelude                hiding (id, (.))

import           Data.Char              (isDigit)
import           Data.Foldable          (asum)

import           Control.Applicative    hiding (empty, many, optional)
import           Control.Category
import           Control.Monad

import           Text.Parsec            hiding (token, (<|>), string )
import qualified Text.Parsec            as P
import           Text.Parsec.Pos

import           Theory
import           Theory.Text.Lexer
                   ( Keyword(..), TextType(..), runAlex, AlexPosn(..)
                   , alexGetPos, alexMonadScan
                   )



------------------------------------------------------------------------------
-- Parser
------------------------------------------------------------------------------

-- | A parser for a stream of tokens.
type Parser a = Parsec [Token] MaudeSig a

-- | Parser a file.
parseFile :: Parser a -> FilePath -> IO a
parseFile parser f = do
  s <- readFile f
  case runParser parser minimalMaudeSig f (scanString f s) of
    Right p -> return p
    Left err -> error $ show err

-- | Run a given parser on a given string.
parseFromString :: Parser a -> String -> Either ParseError a
parseFromString parser =
    runParser parser minimalMaudeSig dummySource . scanString dummySource
  where
    dummySource = "<interactive>"


------------------------------------------------------------------------------
-- Lexing (based on Alex)
------------------------------------------------------------------------------

-- | The tokens delivered by our Alex based scanner
type Token = (SourcePos, Keyword)

-- | Scan a string using the given filename in the error messages.
--
-- NOTE: Lexical errors are thrown using 'error'.
scanString :: FilePath -> String -> [Token]
scanString filename s =
  case runAlex s gatherUntilEOF of
    Left err  -> error err
    Right kws -> kws
  where
  gatherUntilEOF = do
    AlexPn _ line col <- alexGetPos
    let pos = newPos filename line col
    k <- alexMonadScan
    case k of
      EOF -> return [(pos,EOF)]
      _   -> do kws <- gatherUntilEOF
                return $ (pos,k) : kws


-- Token parsers
----------------

-- | Parse a token based on the acceptance condition
token :: (Keyword -> Maybe a) -> Parser a
token p = P.token (show . snd) fst (p . snd)

-- | Parse a keyword.
kw :: Keyword -> Parser ()
kw t = token check
  where
  check t' | t == t' = Just () | otherwise = Nothing

-- | Parse content between keywords.
betweenKWs :: Keyword -> Keyword -> Parser a -> Parser a
betweenKWs l r = between (kw l) (kw r)

-- | Between braces.
braced :: Parser a -> Parser a
braced = betweenKWs LBRACE RBRACE

-- | Between parentheses.
parens :: Parser a -> Parser a
parens = betweenKWs LPAREN RPAREN

-- | Between angular brackets.
angled :: Parser a -> Parser a
angled = betweenKWs LESS GREATER

-- | Between single quotes.
singleQuoted :: Parser a -> Parser a
singleQuoted = betweenKWs SQUOTE SQUOTE

-- | Between double quotes.
doubleQuoted :: Parser a -> Parser a
doubleQuoted = betweenKWs DQUOTE DQUOTE

-- | Parse an identifier as a string
string :: String -> Parser ()
string cs = token extract
  where extract (IDENT name) | cs == name = Just ()
        extract _                         = Nothing

-- | Parse a sequence of fixed strings.
strings :: [String] -> Parser ()
strings = mapM_ string

-- | Parse a text passage.
text :: (TextType -> Maybe a) -> Parser a
text f = token (\t -> case t of TEXT ty -> f ty; _ -> mzero)

-- | Parse an integer.
integer :: Parser Int
integer = do i <- identifier
             guard (all isDigit i)
             return (read i)

-- | A comma separated list of elements.
commaSep :: Parser a -> Parser [a]
commaSep = (`sepBy` kw COMMA)

-- | A comma separated non-empty list of elements.
commaSep1 :: Parser a -> Parser [a]
commaSep1 = (`sepBy1` kw COMMA)

-- | Parse a list of items '[' item ',' ... ',' item ']'
list :: Parser a -> Parser [a]
list p = kw LBRACKET *> commaSep p <* kw RBRACKET


-- Identifiers and Variables
----------------------------

-- | Parse an identifier as a string
identifier :: Parser String
identifier = token extract
  where extract (IDENT name)
         -- don't allow certain reserved words as identifiers
         | not (name `elem` ["in","let","rule"]) = Just name
        extract _                                = Nothing

-- | Parse an identifier possibly indexed with a number.
indexedIdentifier :: Parser (String, Integer)
indexedIdentifier = do
    (,) <$> identifier
        <*> option 0 (try (kw DOT *> (fromIntegral <$> integer)))

-- | Parse a logical variable with the given sorts allowed.
sortedLVar :: [LSort] -> Parser LVar
sortedLVar ss =
    asum $ map (try . mkSuffixParser) ss ++ map mkPrefixParser ss
  where
    mkSuffixParser s = do
        (n, i) <- indexedIdentifier
        kw COLON
        string (sortSuffix s)
        return (LVar n s i)

    mkPrefixParser s = do
        case s of
          LSortMsg   -> pure ()
          LSortPub   -> kw DOLLAR
          LSortFresh -> kw TILDE
          LSortNode  -> kw SHARP
          LSortMSet  -> kw PERCENT
        (n, i) <- indexedIdentifier
        return (LVar n s i)

-- | An arbitrary logical variable.
lvar :: Parser LVar
lvar = sortedLVar [minBound..]

-- | Parse a non-node variable.
msgvar :: Parser LVar
msgvar = sortedLVar [LSortFresh, LSortPub, LSortMsg, LSortMSet]

-- | Parse a graph node variable.
nodevar :: Parser NodeId
nodevar = asum
  [ sortedLVar [LSortNode]
  , (\(n, i) -> LVar n LSortNode i) <$> indexedIdentifier ]
  <?> "node"

-- | Parse a literal fresh name, e.g., @~'n'@.
freshName :: Parser String
freshName = try (kw TILDE *> singleQuoted identifier)

-- | Parse a literal public name, e.g., @'n'@.
pubName :: Parser String
pubName = singleQuoted identifier


-- Term Operators
------------

-- | The exponentiation operator @^@.
opExp :: Parser ()
opExp = kw HAT

-- | The multiplication operator @*@.
opMult :: Parser ()
opMult = kw STAR

-- | The timepoint comparison operator @<@.
opLess :: Parser ()
opLess = kw LESS

-- | The action-at-timepoint operator \@.
opAt :: Parser ()
opAt = kw AT

-- | The equality operator @=@.
opEqual :: Parser ()
opEqual = kw EQUAL

-- | The logical-forall operator @All@ or @∀@.
opForall :: Parser ()
opForall = string "All" <|> kw FORALL

-- | The logical-exists operator @Ex@ or @∃@.
opExists :: Parser ()
opExists = string "Ex" <|> kw EXISTS

-- | The logical-implies operator @==>@.
opImplies :: Parser ()
opImplies = kw EQUAL *> kw EQUAL *> kw GREATER

-- | The logical-equivalence operator @<=>@.
opLEquiv :: Parser  ()
opLEquiv = try (kw LESS *> kw EQUAL *> kw GREATER)

-- | The logical-and operator @&@ or @∧@.
opLAnd :: Parser ()
opLAnd = kw LAND <|> kw AND

-- | The logical-or operator @|@ or @∨@.
opLOr :: Parser ()
opLOr = kw MID <|> kw LOR

-- | The logical not operator @not@ or @¬@.
opLNot :: Parser  ()
opLNot = kw LNOT <|> string "not"


-- Pseudo operators (to be replaced by usage of proper tokens)
--------------------------------------------------------------

-- | The equal sign @=@.
equalSign :: Parser ()
equalSign = kw EQUAL

-- | The dot operator @.@.
opDot :: Parser ()
opDot = kw DOT

-- | The comma operator @,@.
opComma :: Parser ()
opComma = kw COMMA

-- | The slash operator @/@.
opSlash :: Parser ()
opSlash = kw SLASH

-- | The bang operator @!@.
opBang :: Parser ()
opBang = kw BANG

-- | The sharp operator @#@.
opSharp :: Parser ()
opSharp = kw SHARP

-- | The colon operator @:@.
opColon :: Parser ()
opColon = kw COLON

-- | The minus operator @-@.
opMinus :: Parser ()
opMinus = kw MINUS

-- | The leftarrow operator @<--@.
opLeftarrow :: Parser ()
opLeftarrow = kw LEFTARROW

-- | The rightarrow operator @-->@.
opRightarrow :: Parser ()
opRightarrow = kw RIGHTARROW

-- | The longleftarrow operator @<--@.
opLongleftarrow :: Parser ()
opLongleftarrow = kw LONGLEFTARROW

-- | The longrightarrow operator @-->@.
opLongrightarrow :: Parser ()
opLongrightarrow = kw LONGRIGHTARROW
