-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Pretty-printing with support for highlighting keywords and comments.
-- Currently this module is not functional on itself, but geared towards its
-- use in Text.PrettyPrint.Html.
module Text.PrettyPrint.Highlight (
  -- * Highlight style
    HighlightStyle(..)
  
  -- * HighlightDocument class
  , HighlightDocument(..)

  , comment
  , keyword
  , operator

  , comment_
  , keyword_
  , operator_

  , opParens

  , module Text.PrettyPrint.Class
  ) where

import Text.PrettyPrint.Class

-- | Currently we support only keywords, operators, and comments.
data HighlightStyle = Keyword | Comment | Operator
       deriving( Eq, Ord, Show )

class Document d => HighlightDocument d where
    -- 'highlight' @style d@ marks that the document @d@ should be highlighted
    -- using the @style@.
    highlight :: HighlightStyle -> d -> d

instance HighlightDocument Doc where
    highlight _ = id

------------------------------------------------------------------------------
-- General highlighters
------------------------------------------------------------------------------

comment, keyword, operator :: HighlightDocument d => d -> d
comment  = highlight Comment
keyword  = highlight Keyword
operator = highlight Operator

comment_, keyword_, operator_ :: HighlightDocument d => String -> d
comment_  = comment  . text
keyword_  = keyword  . text
operator_ = operator . text

opParens :: HighlightDocument d => d -> d
opParens d = operator_ "(" <> d <> operator_ ")"



