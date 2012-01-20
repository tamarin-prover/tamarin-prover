-- | 'Document' class allowing to have different interpretations of the
-- HughesPJ pretty-printing combinators.
module Text.PrettyPrint.Class (
        P.Doc
     ,  Document(..)
     ,  P.isEmpty
     ,  P.render
     ,  P.renderStyle
     ,  P.style
     ,  P.Style(..)
     ,  P.Mode(..)

     , ($--$)
     , semi 
     , colon
     , comma
     , space
     , equals
     , lparen
     , rparen
     , lbrack
     , rbrack
     , lbrace
     , rbrace
  
     , int
     , integer
     , float
     , double
     , rational
     , quotes
     , doubleQuotes
     , parens
     , brackets
     , braces
  
     , hang
     , punctuate
) where

import Prelude
import qualified Text.PrettyPrint.HughesPJ as P

infixl 6 <> 
infixl 6 <->
infixl 5 $$, $-$, $--$

class Document d where
  char :: Char -> d
  text :: String -> d
  zeroWidthText :: String -> d
  emptyDoc :: d
  (<>)  :: d -> d -> d
  (<->) :: d -> d -> d
  hcat  :: [d] -> d
  hsep  :: [d] -> d
  ($$)  :: d -> d -> d
  ($-$) :: d -> d -> d
  vcat  :: [d] -> d
  sep   :: [d] -> d
  cat   :: [d] -> d
  fsep  :: [d] -> d
  fcat  :: [d] -> d
  nest  :: Int -> d -> d
  caseEmptyDoc :: d -> d -> d -> d

instance Document P.Doc where
  char = P.char
  text = P.text
  zeroWidthText = P.zeroWidthText
  emptyDoc = P.empty
  (<>)  = (P.<>)
  (<->) = (P.<+>)
  hcat  = P.hcat
  hsep  = P.hsep
  ($$)  = (P.$$)
  ($-$) = (P.$+$)
  vcat  = P.vcat
  sep   = P.sep
  cat   = P.cat
  fsep  = P.fsep
  fcat  = P.fcat
  nest  = P.nest
  caseEmptyDoc yes no d = if P.isEmpty d then yes else no

-- | Vertical concatentation of two documents with an empty line in between.
($--$) :: Document d => d -> d -> d
d1 $--$ d2 = 
   caseEmptyDoc d2 (caseEmptyDoc d1 (d1 $-$ text "" $-$ d2) d2) d1

semi, colon, comma, space, equals, 
  lparen, rparen, lbrack, rbrack, lbrace, rbrace :: Document d => d

semi  = char ';'
colon = char ':'
comma = char ','
space = char ' '
equals = char '='
lparen = char '('
rparen = char ')'
lbrack = char '['
rbrack = char ']'
lbrace = char '{'
rbrace = char '}'

int :: Document d => Int -> d
int      n = text (show n)

integer :: Document d => Integer -> d
integer  n = text (show n)

float :: Document d => Float -> d
float    n = text (show n)

double :: Document d => Double -> d
double   n = text (show n)

rational :: Document d => Rational -> d
rational n = text (show n)

quotes, doubleQuotes, parens, brackets, braces :: Document d => d -> d
quotes p        = char '\'' <> p <> char '\''
doubleQuotes p  = char '"' <> p <> char '"'
parens p        = char '(' <> p <> char ')'
brackets p      = char '[' <> p <> char ']'
braces p        = char '{' <> p <> char '}'

hang :: Document d => d -> Int -> d -> d
hang d1 n d2 = sep [d1, nest n d2]

punctuate :: Document d => d -> [d] -> [d]
punctuate _ []     = []
punctuate p (d:ds) = go d ds
                   where
                     go d' [] = [d']
                     go d' (e:es) = (d' <> p) : go e es
