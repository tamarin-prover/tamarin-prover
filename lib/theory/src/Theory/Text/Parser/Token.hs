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
  -- * Symbols
    symbol
  , symbol_
  , dot
  , comma
  , colon

  , natural
  , naturalSubscript

  -- ** Formal comments
  , formalComment

  -- * Identifiers and Variables
  , identifier
  , indexedIdentifier

  , hexColor

  , freshName
  , pubName
  , natName

  , sortedLVar
  , userSortedLVar
  , lvar
  , msgvar
  , nodevar

  , letIdentifier

  -- * Operators
--  , opDiff

  , opExp
  , opMult

  , opXor

  , opEqual
  , opSubterm
  , opLess
  , opAt
  , opForall
  , opExists
  , opImplies
  , opLEquiv
  , opLAnd
  , opLOr
  , opLNot
  , opLFalse
  , opLTrue

  , opParallel
  , opParallelDepr
  , opSeq
  , opNDC
  , opNull

  , opRequires
  , opChain

  -- ** Pseudo operators
  , equalSign
  , opSharp
  , opBang
  , opSlash
  , opMinus
  , opPlus
  , opUnion
  , opLeftarrow
  , opRightarrow
  , opLongleftarrow
  , opLongrightarrow

  -- * Parentheses/quoting
  , braced
  , parens
  , angled
  , brackets
  , singleQuoted
  , doubleQuoted

  -- * List parsing
  , commaSep
  , commaSep1
  , list
  , wsSep
  , commaSepN

    -- * Basic Parsing
  , Parser
  , parseFile
  , parseString
  ) where

import           Prelude             hiding (id, (.))

import           Data.Foldable       (asum)
import           Data.List (foldl')

import           Control.Applicative hiding (empty, many, optional)
import           Control.Category
import           Control.Monad

import           Text.Parsec         hiding ((<|>))
import qualified Text.Parsec.Token   as T

import           Theory


------------------------------------------------------------------------------
-- Parser
------------------------------------------------------------------------------

-- | A parser for a stream of tokens.
type Parser a = Parsec String MaudeSig a

-- Use Parsec's support for defining token parsers.
spthy :: T.TokenParser MaudeSig
spthy =
    T.makeTokenParser spthyStyle
  where
    spthyStyle = T.LanguageDef
      { T.commentStart   = "/*"
      , T.commentEnd     = "*/"
      , T.commentLine    = "//"
      , T.nestedComments = True
      , T.identStart     = alphaNum
      , T.identLetter    = alphaNum <|> oneOf "_"
      , T.reservedNames  = ["in","let","rule","diff"]
      , T.opStart        = oneOf ":!$%&*+./<=>?@\\^|-#"
      , T.opLetter       = oneOf ":!$%&*+./<=>?@\\^|-#"
      , T.reservedOpNames= []
      , T.caseSensitive  = True
      }

-- | Run a parser on the contents of a file.
parseFile :: Parser a -> FilePath -> IO a
parseFile parser inFile = do
    inp <- readFile inFile
    case parseString inFile parser inp of
        Right x  -> return x
        Left err -> error $ show err

-- | Run a given parser on a given string.
parseString :: FilePath
            -- ^ Description of the source file. (For error reporting.)"
            -> Parser a
            -> String         -- ^ Input string.
            -> Either ParseError a
parseString srcDesc parser =
    runParser (T.whiteSpace spthy *> parser) pairMaudeSig srcDesc
                                           -- was "minimalMaudeSig" -> could lead to errors with parsing diff terms!

-- Token parsers
----------------

-- | Parse a symbol.
symbol :: String -> Parser String
symbol sym = try (T.symbol spthy sym) <?> ("\"" ++ sym ++ "\"")

-- | Parse a symbol without returning the parsed string.
symbol_ :: String -> Parser ()
symbol_ = void . symbol

-- | Between braces.
braced :: Parser a -> Parser a
braced = T.braces spthy

-- | Between brackets.
brackets :: Parser a -> Parser a
brackets = T.brackets spthy

-- | Between parentheses.
parens :: Parser a -> Parser a
parens = T.parens spthy

-- | Between angular brackets.
angled :: Parser a -> Parser a
angled = T.angles spthy

-- | Between single quotes.
singleQuoted :: Parser a -> Parser a
singleQuoted = between (symbol "'") (symbol "'")

-- | Between double quotes.
doubleQuoted :: Parser a -> Parser a
doubleQuoted = between (symbol "\"") (symbol "\"")

-- | A dot @.@.
dot :: Parser ()
dot = void $ T.dot spthy

-- | A comma @,@.
comma :: Parser ()
comma = void $ T.comma spthy

-- -- | A semicolon @;@.
-- semicolon :: Parser ()
-- semicolon = void $ T.semi spthy

-- | A colon @:@.
colon :: Parser ()
colon = void $ T.colon spthy

-- | Parse an natural.
natural :: Parser Integer
natural = T.natural spthy

-- | Parse a Unicode-subscripted natural number.
naturalSubscript :: Parser Integer
naturalSubscript = T.lexeme spthy $ do
    digits <- many1 (oneOf "₀₁₂₃₄₅₆₇₈₉")
    let n = foldl' (\x d -> 10*x + subscriptDigitToInteger d) 0 digits
    seq n (return n)
  where
    subscriptDigitToInteger d = toInteger $ fromEnum d - fromEnum '₀'

    
-- | A comma separated list of elements.
commaSep :: Parser a -> Parser [a]
commaSep = T.commaSep spthy

-- | A comma separated non-empty list of elements.
commaSep1 :: Parser a -> Parser [a]
commaSep1 = T.commaSep1 spthy

-- | Parse a list of items '[' item ',' ... ',' item ']'
list :: Parser a -> Parser [a]
list = brackets . commaSep

-- | A whitespace separated list of elements.
wsSep :: Parser a -> Parser [a]
wsSep p = sepBy p (T.whiteSpace spthy)

-- | A comma separated list of elements.
commaSepN :: [Parser a] -> Parser [a]
commaSepN []     = return []
commaSepN (p:ps) = do
  r <- p
  T.whiteSpace spthy
  if not $ null ps
    then do
      void $ T.comma spthy
      rs <- commaSepN ps
      return $ r : rs
    else
      return [r]

-- | A formal comment; i.e., (header, body)
formalComment :: Parser (String, String)
formalComment = T.lexeme spthy $ do
    header <- try (many1 letter <* string "{*")
    body   <- many bodyChar <* string "*}"
    return (header, body)
  where
    bodyChar = try $ do
      c <- anyChar
      case c of
        '\\' -> char '\\' <|> char '*'
        '*'  -> mzero
        _    -> return c

-- Identifiers and Variables
----------------------------

-- | Parse an identifier as a string
identifier :: Parser String
identifier = T.identifier spthy

-- | Parse an identifier possibly indexed with a number.
indexedIdentifier :: Parser (String, Integer)
indexedIdentifier = do
    (,) <$> identifier
        <*> option 0 (try (dot *> (fromIntegral <$> natural)))

-- | Parse a hex RGB color code
hexColor :: Parser String
hexColor = T.lexeme spthy (singleQuoted hexCode <|> hexCode)
  where
    hexCode = optional (symbol "#") *> many1 hexDigit

-- | Parse a logical variable with the given sorts allowed.
sortedLVar :: [LSort] -> Parser LVar
sortedLVar ss =
    asum $ map (try . mkSuffixParser) ss ++ map mkPrefixParser ss
  where
    mkSuffixParser s = do
        (n, i) <- indexedIdentifier <* colon
        symbol_ (sortSuffix s)
        return (LVar n s i)

    mkPrefixParser s = do
        case s of
          LSortMsg       -> pure ()
          LSortPub       -> void $ char '$'
          LSortFresh     -> void $ char '~'
          LSortNode      -> void $ char '#'
          LSortNat       -> void $ char '%'
          (LSortUser st) -> do
              void $ char '?'
              symbol_ st
              void $ char '?'
        (n, i) <- indexedIdentifier
        return (LVar n s i)

-- | Parse a logical variable of an arbitrary user-defined sort.
userSortedLVar :: Parser LVar
userSortedLVar =
    asum $ map try [suffixParser, prefixParser]
  where
    suffixParser = do
        (n, i) <- indexedIdentifier <* colon
        sort <- identifier
        if elem sort $ map sortSuffix [LSortFresh, LSortPub, LSortNat, LSortNode, LSortMsg]
          then fail "Invalid user-sort"
          else return (LVar n (LSortUser sort) i)

    prefixParser = do
        void $ char '?'
        sort <- identifier
        void $ char '?'
        (n, i) <- indexedIdentifier
        return (LVar n (LSortUser sort) i)

-- | An arbitrary logical variable.
lvar :: Parser LVar
lvar = asum $ map try
  [ userSortedLVar
  , sortedLVar [LSortFresh, LSortPub, LSortNat, LSortMsg, LSortNode] ]

-- | Parse a non-node variable.
msgvar :: Parser LVar
msgvar = asum $ map try
  [ userSortedLVar
  , sortedLVar [LSortFresh, LSortPub, LSortNat, LSortMsg] ]

-- | Parse a graph node variable.
nodevar :: Parser NodeId
nodevar = asum
  [ sortedLVar [LSortNode]
  , (\(n, i) -> LVar n LSortNode i) <$> indexedIdentifier ]
  <?> "timepoint variable"

-- | Parse a literal fresh name, e.g., @~'n'@.
freshName :: Parser String
freshName = try (symbol "~" *> singleQuoted identifier)

-- | Parse a literal public name, e.g., @'n'@.
pubName :: Parser String
pubName = singleQuoted identifier

-- | Parse a literal nat name, e.g. @:'n'@.
natName :: Parser String
natName = try (symbol ":" *> singleQuoted identifier)


-- Term Operators
-----------------

{-
-- Note that this would conflict with the parsing of "identifier", somehow need to mark this as special!
-- | The diff operator @diff@.
opDiff :: Parser ()
opDiff = symbol_ "diff"
-}

-- | The exponentiation operator @^@.
opExp :: Parser ()
opExp = symbol_ "^"

-- | The multiplication operator @*@.
opMult :: Parser ()
opMult = symbol_ "*"

-- | The addition operator @%+@.
opPlus :: Parser ()
opPlus = symbol_ "%+"

-- | The multiset operator @+@.
opUnion :: Parser ()
opUnion = symbol_ "++" <|> symbol_ "+"

-- | The xor operator @XOR@ or @⊕@.
opXor :: Parser ()
opXor = symbol_ "XOR" <|> symbol_ "⊕"

-- | The timepoint comparison operator @<@.
opLess :: Parser ()
opLess = symbol_ "<"

-- | The action-at-timepoint operator \@.
opAt :: Parser ()
opAt = symbol_ "@"

-- | The equality operator @=@.
opEqual :: Parser ()
opEqual = symbol_ "="

-- | The equality operator @=@.
opSubterm :: Parser ()
opSubterm = symbol_ "<<" <|> symbol_ "⊏"

-- | The logical-forall operator @All@ or @∀@.
opForall :: Parser ()
opForall = symbol_ "All" <|> symbol_ "∀"

-- | The logical-exists operator @Ex@ or @∃@.
opExists :: Parser ()
opExists = symbol_ "Ex" <|> symbol_ "∃"

-- | The logical-implies operator @==>@.
opImplies :: Parser ()
opImplies = symbol_ "==>" <|> symbol_ "⇒"

-- | The logical-equivalence operator @<=>@.
opLEquiv :: Parser  ()
opLEquiv = symbol_ "<=>" <|> symbol_ "⇔"

-- | The logical-and operator @&@ or @∧@.
opLAnd :: Parser ()
opLAnd = symbol_ "&" <|> symbol_ "∧"

-- | The logical-or operator @|@ or @∨@.
opLOr :: Parser ()
opLOr = symbol_ "|" <|> symbol_ "∨"

-- | The logical not operator @not@ or @¬@.
opLNot :: Parser  ()
opLNot = symbol_ "¬" <|> symbol_ "not"

-- | A logical false, @F@ or @⊥@.
opLFalse :: Parser  ()
opLFalse = symbol_ "⊥" <|> T.reserved spthy "F"

-- | A logical false, @T@ or @⊥@.
opLTrue :: Parser  ()
opLTrue = symbol_ "⊤" <|> T.reserved spthy "T"

-- Operators for constraints
----------------------------

-- | The requires-a-premise operator, @▶ subscript-idx@.
opRequires :: Parser PremIdx
opRequires = (PremIdx . fromIntegral) <$> (symbol "▶" *> naturalSubscript)

-- | The chain operator @~~>@.
opChain :: Parser ()
opChain = symbol_ "~~>"


-- Pseudo operators (to be replaced by usage of proper tokens)
--------------------------------------------------------------

-- | The equal sign @=@.
equalSign :: Parser ()
equalSign = symbol_ "="

-- | The slash operator @/@.
opSlash :: Parser ()
opSlash = symbol_ "/"

-- | The bang operator @!@.
opBang :: Parser ()
opBang = symbol_ "!"

-- | The sharp operator @#@.
opSharp :: Parser ()
opSharp = symbol_ "#"

-- | The minus operator @-@.
opMinus :: Parser ()
opMinus = symbol_ "-"

-- | The leftarrow operator @<--@.
opLeftarrow :: Parser ()
opLeftarrow = symbol_ "<-"

-- | The rightarrow operator @-->@.
opRightarrow :: Parser ()
opRightarrow = symbol_ "->"

-- | The longleftarrow operator @<--@.
opLongleftarrow :: Parser ()
opLongleftarrow = symbol_ "<--"

-- | The longrightarrow operator @-->@.
opLongrightarrow :: Parser ()
opLongrightarrow = symbol_ "-->"



-- | The operator for parallel running processes @||@.
opParallel :: Parser()
opParallel = symbol_ "|"

-- | The operator for parallel running processes @||@. (deprecated)
opParallelDepr :: Parser()
opParallelDepr = symbol_ "||"

-- | The let identifier @let@.
letIdentifier :: Parser()
letIdentifier = symbol_ "let"

-- | operator for sequential actions in processes
opSeq :: Parser()
opSeq = symbol_ ";"

-- | operator for non-deterministic choice in processes
opNDC :: Parser()
opNDC = symbol_ "+"  --TODO-PARSER

-- | Operator for 0-process (terminator of sequence)
opNull :: Parser()
opNull = symbol_ "0"
