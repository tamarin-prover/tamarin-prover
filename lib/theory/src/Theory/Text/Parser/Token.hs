-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Tokenizing infrastructure

{-# LANGUAGE FlexibleInstances #-}
module Theory.Text.Parser.Token (
    lexeme
  -- * Symbols
  , symbol
  , symbol_
  , dot
  , comma
  , colon

  , natural
  , naturalSubscript

  -- ** Formal comments
  , formalComment

  -- ** File Path
  , filePath

  -- * Identifiers and Variables
  , identifier
  , indexedIdentifier

  , hexColor

  , freshName
  , pubName
  , natName


  , typep
  , sortedLVar
  , lvar
  , msgvar
  , nodevar
  , sapicvar
  , sapicpatternvar
  , sapicnodevar

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
  , stringLiteral

  -- * List parsing
  , commaSep
  , commaSep1
  , list

  -- * Parsing State
  , ParserState(..)
  , mkStateSig
  , modifyStateSig
  , modifyStateFlag

    -- * Basic Parsing
  , Parser
  , parseFile
  , parseFileWState
  , parseString
  , parseStringWState
  ,opLessTerm
  ,extIdentifier
  ,betweenMatching
  ,manyCharsExcept) where

import           Prelude             hiding (id, (.))

-- import           Data.Label
-- import           Data.Binary
import           Data.List (foldl')
-- import           Control.DeepSeq
import qualified Data.Set                   as S

-- import           GHC.Generics                        (Generic)

import           Control.Applicative hiding (empty, many, optional)
import           Control.Category
import           Control.Monad

import           System.FilePath

import           Text.Parsec         hiding ((<|>))
import qualified Text.Parsec.Token   as T

import           Theory
import qualified Control.Monad.Catch as Catch
import Data.Functor.Identity
import Theory.Sapic.Pattern
import Theory.Sapic


------------------------------------------------------------------------------
-- Parser
------------------------------------------------------------------------------

data ParserState = PState
       { sig  :: MaudeSig              -- Current signature
       , flags ::  S.Set String        -- Defined flags for pre-processing
       }
       deriving( Eq, Ord, Show )

-- | A monoid instance to combine parser signatures.
instance Semigroup ParserState where
 PState sig1 flags1 <> PState sig2 flags2 =
   PState (sig1 <> sig2) (flags1 `S.union` flags2)

instance Monoid ParserState where
  mempty = PState {sig=mempty, flags = S.empty}

mkStateSig :: MaudeSig -> ParserState
mkStateSig sign = mempty {sig=sign}

modifyStateSig ::  Monad m => (MaudeSig -> MaudeSig) -> ParsecT s ParserState m ()
modifyStateSig modifier = do
   st <- getState
   setState (st {sig = modifier $ sig st})

modifyStateFlag ::  Monad m => (S.Set String -> S.Set String) -> ParsecT s ParserState m ()
modifyStateFlag modifier = do
   st <- getState
   setState (st {flags = modifier $ flags st})

-- | A parser for a stream of tokens.
type Parser a = Parsec String ParserState a

-- We can throw exceptions, but not catch them
instance Catch.MonadThrow (ParsecT String ParserState Data.Functor.Identity.Identity) where
    throwM e = fail (show e)

-- Use Parsec's support for defining token parsers.
spthy :: T.TokenParser ParserState
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
parseFileWState :: ParserState -> Parser a -> FilePath -> IO a
parseFileWState initState parser inFile = do
    inp <- readFile inFile
    case parseStringWState initState inFile parser inp of
        Right x  -> return x
        Left err -> error $ show err

-- | Run a given parser on a given string.
parseStringWState :: ParserState
            -> FilePath
            -- ^ Description of the source file. (For error reporting.)"
            -> Parser a
            -> String         -- ^ Input string.
            -> Either ParseError a
parseStringWState initState srcDesc parser =
    runParser (T.whiteSpace spthy *> parser) initState srcDesc
                                           -- was "minimalMaudeSig" -> could lead to errors with parsing diff terms!

-- | Run a given parser on a given string.
parseString :: [String] -- flags
            -> FilePath
            -- ^ Description of the source file. (For error reporting.)"
            -> Parser a
            -> String         -- ^ Input string.
            -> Either ParseError a
parseString flags0 = parseStringWState $ mempty {sig=pairMaudeSig, flags=S.fromList flags0}

parseFile :: [String] -> Parser a -> FilePath -> IO a
parseFile flags0 = parseFileWState $ mempty {sig=pairMaudeSig, flags=S.fromList flags0}


-- Token parsers
----------------

lexeme :: ParsecT String ParserState Identity a -> ParsecT String ParserState Identity a
lexeme = T.lexeme spthy

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


-- | Parse between two matching symbols like @"@ and @"@ or @(@ and @)@. Tells parser these symbols so it can ignore it.
betweenMatching  :: ((Char, Char) -> Parser a) -> Parser a
betweenMatching p = asum (betweenSymbolsParse <$> matches)
     where
     matches = [
        ('"', '"'),
        ('\'', '\''),
        ('(', ')'),
        ('[', ']'),
        ('{', '}'),
        ('|', '|'),
        ('<', '>') ]
     betweenSymbolsParse (l,r) = try $ between (char' l) (char' r) (p (l,r))
     char' = T.lexeme spthy . char -- need to remove whitespace after r, like symbol does.

-- | consume all chars except those in l,  until we reach on in l. Does not consume that last char.
manyCharsExcept :: [Char] -> Parser [Char]
manyCharsExcept l = T.lexeme spthy $ manyTill (noneOf l) (lookAhead $ oneOf l)

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


-- | A comma separated list of elements, optionally ended with a comma.
commaSep :: Parser a -> Parser [a]
commaSep = flip sepEndBy comma

-- | A comma separated non-empty list of elements, optionally ended with a comma.
commaSep1 :: Parser a -> Parser [a]
commaSep1 = flip sepEndBy1 comma

-- | Parse a list of items '[' item ',' ... ',' item ']', or ended with ',]'
list :: Parser a -> Parser [a]
list = brackets . commaSep

-- | Parse an arbitrary string literal
stringLiteral :: Parser String
stringLiteral = T.stringLiteral spthy

-- | Parse a string literal marked as external, i.e., starting with "x-"
extIdentifier :: Parser String
extIdentifier= T.lexeme spthy $ do
    _ <- try (string "x-")
    identifier

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
        (n, i) <- indexedIdentifier
        return (LVar n s i)

-- | An arbitrary logical variable.
lvar :: Parser LVar
lvar = sortedLVar [minBound..]

-- | Parse a non-node variable.
msgvar :: Parser LVar
msgvar = sortedLVar [LSortFresh, LSortPub, LSortNat, LSortMsg]

-- | Parse a graph node variable.
nodevar :: Parser NodeId
nodevar = asum
  [ sortedLVar [LSortNode]
  , (\(n, i) -> LVar n LSortNode i) <$> indexedIdentifier ]
  <?> "timepoint variable"

-- | Parse a non-empty single-quoted string
-- | that does not contain a single-quote or newline.
singleQuotedString :: Parser String
singleQuotedString = singleQuoted $ many1 (noneOf "'\n")

-- | Parse a literal fresh name, e.g., @~'n'@.
freshName :: Parser String
freshName = try (symbol "~" *> singleQuotedString)

-- | Parse a literal public name, e.g., @'n'@.
pubName :: Parser String
pubName = singleQuotedString

-- | Parse a literal nat name, e.g. @%'n'@.
natName :: Parser String
natName = try (symbol "%" *> singleQuotedString)

-- | Parse a Sapic Type
typep :: Parser SapicType
typep = ( try (symbol defaultSapicTypeS) *> return Nothing)
            <|> Just <$> identifier

-- | Parse a variable in sapic that is typed:
--   first parse for lvar, then parse for one more type
--   so:
--   ~x: foo
--   $x: bar
--   x: foo
--   are all valid, but
--   x: pub: foo
--   is not
-- We first redefine lvars but forbidding the suffix

sortedLVarNoSuffix :: [LSort] -> Parser LVar
sortedLVarNoSuffix ss =
    asum $ map mkPrefixParser ss
  where
    mkPrefixParser s = do
        case s of
          LSortMsg       -> pure ()
          LSortPub       -> void $ char '$'
          LSortFresh     -> void $ char '~'
          LSortNode      -> void $ char '#'
          LSortNat       -> void $ char '%'
        (n, i) <- indexedIdentifier
        return (LVar n s i)

-- | An arbitrary logical variable.
lvarNoSuffix :: Parser LVar
lvarNoSuffix = sortedLVarNoSuffix [minBound..]


sapicvar :: Parser SapicLVar
sapicvar = do
        v <- lvarNoSuffix
        t <- option Nothing $ colon *> typep
        return (SapicLVar v t)

sapicpatternvar :: Parser PatternSapicLVar
sapicpatternvar = do
        eq <- option False parseq
        v  <- sapicvar
        return (if eq then PatternMatch v else PatternBind v)
        where parseq = do
                _ <- opEqual
                return True


sapicnodevar :: Parser SapicLVar
sapicnodevar = do
    v <- nodevar
    return (SapicLVar v defaultSapicNodeType)


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

-- | The multiset comparison operator @(<)@.
opLessTerm :: Parser ()
opLessTerm = symbol_ "(<)"

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
opRequires = PremIdx . fromIntegral <$> (symbol "▶" *> naturalSubscript)

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
opNDC = symbol_ "+"

-- | Operator for 0-process (terminator of sequence)
opNull :: Parser()
opNull = symbol_ "0"


-- File Path
-- | Parse a file path, returned with the given prefix s
filePath :: Parser FilePath
filePath = many charDir
  where
    charDir = alphaNum <|> oneOf ("." <> [pathSeparator])
