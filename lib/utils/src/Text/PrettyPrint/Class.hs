{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- 'Document' class allowing to have different interpretations of the
-- HughesPJ pretty-printing combinators.
module Text.PrettyPrint.Class (
        Doc
     ,  Document(..)
     ,  isEmpty
     ,  render
     ,  renderStyle
     ,  defaultStyle
     ,  P.Style(..)
     ,  P.Mode(..)

     , ($--$)
     , emptyDoc
     , (<>)
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

     -- * Additional combinators
     , nestBetween
     , nestShort
     , nestShort'
     , nestShortNonEmpty
     , nestShortNonEmpty'
     , fixedWidthText
     , symbol
     , numbered
     , numbered'
) where

import           Control.DeepSeq        (NFData(..))

import           Data.List              (intersperse)

import           Extension.Data.Monoid  ((<>))
import           Extension.Prelude      (flushRight)

import qualified Text.PrettyPrint.HughesPJ as P

infixr 6 <->
infixl 5 $$, $-$, $--$

newtype Doc = Doc { getPrettyLibraryDoc :: P.Doc }

isEmpty :: Doc -> Bool
isEmpty (Doc d) = P.isEmpty d

render :: Doc -> String
render (Doc d) = P.render d

renderStyle :: P.Style -> Doc -> String
renderStyle s (Doc d) = P.renderStyle s d

-- emptyDoc = P.empty
-- (<>)  = (P.<>)

class (Monoid d, NFData d) => Document d where
  char :: Char -> d
  text :: String -> d
  zeroWidthText :: String -> d
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

-- | The default 'P.Style'.
defaultStyle :: P.Style
defaultStyle = P.style

-- | The empty document.
emptyDoc :: Document d => d
emptyDoc = mempty

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


------------------------------------------------------------------------------
-- The 'Document' instance for 'Text.PrettyPrint.Doc'
------------------------------------------------------------------------------

-- Must be removed for GHC 7.10, needed before
instance NFData Doc where
  rnf = rnf . P.render . getPrettyLibraryDoc

instance Document Doc where
  char = Doc . P.char
  text = Doc . P.text
  zeroWidthText = Doc . P.zeroWidthText
  (<->) (Doc d1) (Doc d2) = Doc $ (P.<+>) d1 d2
  hcat  = Doc . P.hcat . map getPrettyLibraryDoc 
  hsep  = Doc . P.hsep . map getPrettyLibraryDoc 
  ($$) (Doc d1) (Doc d2) = Doc $ (P.$$) d1 d2
  ($-$) (Doc d1) (Doc d2) = Doc $ (P.$+$) d1 d2
  vcat  = Doc . P.vcat . map getPrettyLibraryDoc
  sep   = Doc . P.sep . map getPrettyLibraryDoc
  cat   = Doc . P.cat . map getPrettyLibraryDoc
  fsep  = Doc . P.fsep . map getPrettyLibraryDoc
  fcat  = Doc . P.fcat . map getPrettyLibraryDoc
  nest i (Doc d) = Doc $ P.nest i d
  caseEmptyDoc yes no (Doc d) = if P.isEmpty d then yes else no

instance Monoid Doc where
    mempty = Doc $ P.empty
    mappend (Doc d1) (Doc d2) = Doc $ (P.<>) d1 d2
  
------------------------------------------------------------------------------
-- Additional combinators
------------------------------------------------------------------------------

-- | Nest a document surrounded by a leading and a finishing document breaking
-- lead, body, and finish onto separate lines, if they don't fit on a single
-- line.
nestBetween :: Document d =>
               Int -- ^ Indent of body
            -> d -- ^ Leading document
            -> d -- ^ Finishing document
            -> d -- ^ Body document
            -> d
nestBetween n l r x = sep [l, nest n x, r]

-- | Nest a document surrounded by a leading and a finishing document with an
-- non-compulsory break between lead and body.
nestShort :: Document d =>
             Int -- ^ Indent of body
          -> d -- ^ Leading document
          -> d -- ^ Finishing document
          -> d -- ^ Body document
          -> d
nestShort n lead finish body = sep [lead $$ nest n body, finish]

-- | Nest document between two strings and indent body by @length lead + 1@.
nestShort' :: Document d => String -> String -> d -> d
nestShort' lead finish = 
  nestShort (length lead + 1) (text lead) (text finish)

-- | Like 'nestShort' but doesn't print the lead and finish, if the document is
-- empty.
nestShortNonEmpty :: Document d => Int -> d -> d -> d -> d
nestShortNonEmpty n lead finish body =
  caseEmptyDoc emptyDoc (nestShort n lead finish body) body

-- | Like 'nestShort'' but doesn't print the lead and finish, if the document is
-- empty.
nestShortNonEmpty' :: Document d => String -> String -> d -> d
nestShortNonEmpty' lead finish = 
  nestShortNonEmpty (length lead + 1) (text lead) (text finish)

-- | Output text with a fixed width: if it is smaller then nothing happens,
-- otherwise care is taken to make the text appear having the given width.
fixedWidthText :: Document d => Int -> String -> d
fixedWidthText n cs
  | length cs <= n  = text cs
  | otherwise = text as <> zeroWidthText bs
  where
    (as,bs) = splitAt n cs

-- | Print string as symbol having width 1.
symbol :: Document d => String -> d
symbol = fixedWidthText 1

-- | Number a list of documents that are vertically separated by the given
-- separator.
numbered :: Document d => d -> [d] -> d
numbered _   [] = emptyDoc
numbered vsep ds = 
    foldr1 ($-$) $ intersperse vsep $ map pp $ zip [(1::Int)..] ds
  where
    n         = length ds
    nWidth    = length (show n)
    pp (i, d) = text (flushRight nWidth (show i)) <> d

-- | Number a list of documents with numbers terminated by "." and vertically
-- separate using an empty line.
numbered' :: Document d => [d] -> d
numbered' = numbered (text "") . map (text ". " <>)
