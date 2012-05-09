-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- General support for pretty printing theories.
module Theory.Text.Pretty (
  -- * General highlighters
    module Text.PrettyPrint.Highlight

  -- * Comments
  , lineComment
  , multiComment

  , lineComment_
  , multiComment_

  -- * Keywords
  , kwTheoryHeader
  , kwEnd
  , kwModulo
  , kwBy
  , kwCase
  , kwNext
  , kwQED

  -- ** Composed forms
  , kwLemmaModulo
  , kwRuleModulo
  , kwInstanceModulo
  , kwVariantsModulo
  , kwTypesModulo

  -- * Operators
  , opProvides
  , opRequires
  , opAction
  , opPath
  , opLess
  , opEqual
  , opDedBefore
  , opEdge

  ) where

import Text.PrettyPrint.Highlight

------------------------------------------------------------------------------
-- Comments
------------------------------------------------------------------------------

lineComment :: HighlightDocument d => d -> d
lineComment d = comment $ text "//" <-> d

lineComment_ :: HighlightDocument d => String -> d
lineComment_ = lineComment . text

multiComment :: HighlightDocument d => d -> d
multiComment d = comment $ fsep [text "/*", d, text "*/"]

multiComment_ :: HighlightDocument d => [String] -> d
multiComment_ ls = comment $ fsep [text "/*", vcat $ map text ls, text "*/"]

------------------------------------------------------------------------------
-- Keywords
------------------------------------------------------------------------------

kwTheoryHeader :: HighlightDocument d => String -> d
kwTheoryHeader name = keyword_ "theory" <-> text name <-> keyword_ "begin"

kwEnd, kwBy, kwCase, kwNext, kwQED :: HighlightDocument d => d
kwEnd    = keyword_ "end"
kwBy     = keyword_ "by"
kwCase   = keyword_ "case"
kwNext   = keyword_ "next"
kwQED    = keyword_ "qed"

kwModulo :: HighlightDocument d
         => String  -- ^ What
         -> String  -- ^ modulo theory
         -> d
kwModulo what thy = keyword_ what <-> parens (keyword_ "modulo" <-> text thy)

kwLemmaModulo, kwRuleModulo, kwInstanceModulo, kwTypesModulo, kwVariantsModulo
  :: HighlightDocument d => String -> d
kwLemmaModulo    = kwModulo "lemma"
kwRuleModulo     = kwModulo "rule"
kwInstanceModulo = kwModulo "instance"
kwTypesModulo    = kwModulo "type assertions"
kwVariantsModulo = kwModulo "variants"


------------------------------------------------------------------------------
-- Operators
------------------------------------------------------------------------------

opProvides, opRequires, opAction, opPath, opLess, opEqual, opDedBefore, opEdge
  :: HighlightDocument d => d
opProvides  = operator_ ":>"
opRequires  = operator_ "<:"
opAction    = operator_ "@"
opPath      = operator_ ">+>"
opLess      = operator_ "<"
opEqual     = operator_ "="
opDedBefore = operator_ "--|"
opEdge      = operator_ ">->"

