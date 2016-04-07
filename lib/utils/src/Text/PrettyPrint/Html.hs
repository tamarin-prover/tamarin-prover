{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Pretty-printing with support for HTML markup and proper HTML escaping.
module Text.PrettyPrint.Html (
  -- * HtmlDocument class
    HtmlDocument(..)

  , withTag
  , withTagNonEmpty
  , closedTag

  , module Text.PrettyPrint.Highlight

  -- * HtmlDoc: adding HTML markup
  , HtmlDoc
  , htmlDoc
  , getHtmlDoc
  , postprocessHtmlDoc
  , renderHtmlDoc

  -- * NoHtmlDoc: ignoring HTML markup
  , noHtmlDoc
  , getNoHtmlDoc
  ) where

import Data.Char (isSpace)
-- import Data.Traversable (sequenceA)
import Data.Monoid

import Control.Arrow (first)
import Control.Applicative
import Control.Monad.Identity
import Control.DeepSeq

import Text.PrettyPrint.Class
import Text.PrettyPrint.Highlight

------------------------------------------------------------------------------
-- HtmlDocument class
------------------------------------------------------------------------------


class HighlightDocument d => HtmlDocument d where
    -- | @unescapedText str@ converts the 'String' @str@ to a document without
    -- performing any escaping.
    unescapedText :: String -> d

    -- | @unescapedZeroWidthText str@ converts the 'String' @str@ to a document
    -- with zero width without performing any escaping.
    unescapedZeroWidthText :: String -> d

-- | @withTag tag attrs inner@ adds the tag @tag@ with the attributes
-- @attrs@ around the @inner@ document.
withTag :: HtmlDocument d => String -> [(String,String)] -> d -> d
withTag tag attrs inner =
    unescapedZeroWidthText open <> inner <> unescapedZeroWidthText close
  where
    open  = "<" ++ tag ++ concatMap attribute attrs ++ ">"
    close = "</" ++ tag ++ ">"

-- | @closedTag tag attrs@ builds the closed tag @tag@ with the attributes
-- @attrs@; e.g.,
--
-- > closedTag "img" "href" "here" = HtmlDoc (text "<img href=\"here\"/>)
--
closedTag :: HtmlDocument d => String -> [(String,String)] -> d
closedTag tag attrs = 
    unescapedZeroWidthText $ "<" ++ tag ++ concatMap attribute attrs ++ "/>"

-- | @withTagNonEmpty tag attrs inner@ adds the tag @tag@ with the attributes
-- @attrs@ around the @inner@ document iff @inner@ is a non-empty document.
withTagNonEmpty :: HtmlDocument d => String -> [(String,String)] -> d -> d
withTagNonEmpty tag attrs inner =
    caseEmptyDoc inner emptyDoc $ withTag tag attrs inner

-- | Render an attribute.
attribute :: (String, String) -> String
attribute (key,value) = " " ++ key ++ "=\"" ++ escapeHtmlEntities value ++ "\""


------------------------------------------------------------------------------
-- HtmlDoc: adding HTML markup
------------------------------------------------------------------------------

-- | A 'Document' transformer that adds proper HTML escaping.
newtype HtmlDoc d = HtmlDoc { getHtmlDoc :: d }
    deriving( Monoid )

-- | Wrap a document such that HTML markup can be added without disturbing the
-- layout.
htmlDoc :: d -> HtmlDoc d
htmlDoc = HtmlDoc

instance NFData d => NFData (HtmlDoc d) where
    rnf = rnf . getHtmlDoc

instance Document d => Document (HtmlDoc d) where
    char          = HtmlDoc . text . escapeHtmlEntities . return
    text          = HtmlDoc . text . escapeHtmlEntities 
    zeroWidthText = HtmlDoc . zeroWidthText . escapeHtmlEntities

    HtmlDoc d1 <-> HtmlDoc d2 = HtmlDoc $ d1 <-> d2
    hcat = HtmlDoc . hcat . map getHtmlDoc
    hsep = HtmlDoc . hsep . map getHtmlDoc

    HtmlDoc d1 $$  HtmlDoc d2 = HtmlDoc $ d1 $$ d2
    HtmlDoc d1 $-$ HtmlDoc d2 = HtmlDoc $ d1 $-$ d2
    vcat = HtmlDoc . vcat . map getHtmlDoc

    sep = HtmlDoc . sep . map getHtmlDoc
    cat = HtmlDoc . cat . map getHtmlDoc

    fsep = HtmlDoc . fsep . map getHtmlDoc
    fcat = HtmlDoc . fcat . map getHtmlDoc

    nest i = HtmlDoc . nest i . getHtmlDoc
    caseEmptyDoc (HtmlDoc d1) (HtmlDoc d2) (HtmlDoc d3) = 
        HtmlDoc $ caseEmptyDoc d1 d2 d3

instance Document d => HtmlDocument (HtmlDoc d) where
    unescapedText = HtmlDoc . text
    unescapedZeroWidthText = HtmlDoc . zeroWidthText

instance Document d => HighlightDocument (HtmlDoc d) where
    highlight hlStyle = 
        withTag "span" [("class", hlClass hlStyle)]
      where
        hlClass Comment  = "hl_comment"
        hlClass Keyword  = "hl_keyword"
        hlClass Operator = "hl_operator"

-- | Escape HTML entities in a string
--
-- Copied from 'blaze-html'.
escapeHtmlEntities :: String  -- ^ String to escape
                   -> String  -- ^ Resulting string
escapeHtmlEntities []     = []
escapeHtmlEntities (c:cs) = case c of
    '<'  -> "&lt;"   ++ escapeHtmlEntities cs
    '>'  -> "&gt;"   ++ escapeHtmlEntities cs
    '&'  -> "&amp;"  ++ escapeHtmlEntities cs
    '"'  -> "&quot;" ++ escapeHtmlEntities cs
    '\'' -> "&#39;"  ++ escapeHtmlEntities cs
    x    -> x : escapeHtmlEntities cs

-- | @renderHtmlDoc = 'postprocessHtmlDoc' . 'render' . 'getHtmlDoc'@ 
renderHtmlDoc :: HtmlDoc Doc -> String
renderHtmlDoc = postprocessHtmlDoc . render . getHtmlDoc

-- | @postprocessHtmlDoc cs@ converts the line-breaks of @cs@ to @<br>@ tags and
-- the prefixed spaces in every line of @cs@ by non-breaing HTML spaces @&nbsp;@.
postprocessHtmlDoc :: String -> String
postprocessHtmlDoc = 
    unlines . map (addBreak . indent) . lines
  where
    addBreak = (++"<br/>")
    indent   = uncurry (++) . (first $ concatMap (const "&nbsp;")) . span isSpace

------------------------------------------------------------------------------
-- NoHtmlDoc: ignoring HTML markup
------------------------------------------------------------------------------

-- | A 'Document' transformer that ignores all 'HtmlDocument' specific methods.
newtype NoHtmlDoc d = NoHtmlDoc { unNoHtmlDoc :: Identity d }
  deriving( Functor, Applicative )


-- | Wrap a document such that all 'HtmlDocument' specific methods are ignored.
noHtmlDoc :: d -> NoHtmlDoc d
noHtmlDoc = NoHtmlDoc . Identity

-- | Extract the wrapped document.
getNoHtmlDoc :: NoHtmlDoc d -> d
getNoHtmlDoc = runIdentity . unNoHtmlDoc

instance NFData d => NFData (NoHtmlDoc d) where
    rnf = rnf . getNoHtmlDoc

instance Monoid d => Monoid (NoHtmlDoc d) where
  mempty = pure mempty
  mappend = liftA2 mappend

instance Document d => Document (NoHtmlDoc d) where
  char = pure . char
  text = pure . text
  zeroWidthText = pure . zeroWidthText
  (<->) = liftA2 (<->)
  hcat  = liftA hcat . sequenceA
  hsep  = liftA hsep . sequenceA
  ($$)  = liftA2 ($$)
  ($-$) = liftA2 ($-$)
  vcat  = liftA vcat  . sequenceA
  sep   = liftA sep   . sequenceA
  cat   = liftA cat   . sequenceA
  fsep  = liftA fsep  . sequenceA
  fcat  = liftA fcat  . sequenceA
  nest  = liftA2 nest . pure
  caseEmptyDoc = liftA3 caseEmptyDoc

instance Document d => HtmlDocument (NoHtmlDoc d) where
    unescapedText          = noHtmlDoc . text
    unescapedZeroWidthText = noHtmlDoc . zeroWidthText

instance Document d => HighlightDocument (NoHtmlDoc d) where
    highlight _ = id
