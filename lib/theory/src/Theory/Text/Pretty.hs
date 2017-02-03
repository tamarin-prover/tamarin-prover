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

  -- * Additional combinators
  , vsep
  , fsepList

  -- * Comments
  , lineComment
  , multiComment
  , closedComment

  , lineComment_
  , multiComment_
  , closedComment_

  -- * Keywords
  , kwTheoryHeader
  , kwEnd
  , kwModulo
  , kwBy
  , kwCase
  , kwNext
  , kwQED
  , kwLemma
  , kwDiffLemma
  , kwRestriction

  -- ** Composed forms
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

  , opExists
  , opForall
  , opLAnd
  , opLOr
  , opImp
  , opIff
  , opDot

  ) where

import Text.PrettyPrint.Highlight


------------------------------------------------------------------------------
-- Additional combinators
------------------------------------------------------------------------------

-- | Vertically separate a list of documents by empty lines.
vsep :: Document d => [d] -> d
vsep = foldr ($--$) emptyDoc

-- | Pretty print a list of values as a comma-separated list wrapped in
-- paragraph mode.
fsepList :: Document d => (a -> d) -> [a] -> d
fsepList pp = fsep . punctuate comma . map pp


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

closedComment :: HighlightDocument d => d -> d
closedComment d = comment $ fsep [text "/*", d, text "*/"]

closedComment_ :: HighlightDocument d => String -> d
closedComment_ ls = comment $ fsep [text "/*", text ls, text "*/"]

------------------------------------------------------------------------------
-- Keywords
------------------------------------------------------------------------------

kwTheoryHeader :: HighlightDocument d => d -> d
kwTheoryHeader name = keyword_ "theory" <-> name <-> keyword_ "begin"

kwEnd, kwBy, kwCase, kwNext, kwQED, kwRestriction, kwLemma, kwDiffLemma :: HighlightDocument d => d
kwEnd         = keyword_ "end"
kwBy          = keyword_ "by"
kwCase        = keyword_ "case"
kwNext        = keyword_ "next"
kwQED         = keyword_ "qed"
kwRestriction = keyword_ "restriction"
kwLemma       = keyword_ "lemma"
kwDiffLemma   = keyword_ "diffLemma"

kwModulo :: HighlightDocument d
         => String  -- ^ What
         -> String  -- ^ modulo theory
         -> d
kwModulo what thy = keyword_ what <-> parens (keyword_ "modulo" <-> text thy)

kwRuleModulo, kwInstanceModulo, kwTypesModulo, kwVariantsModulo
  :: HighlightDocument d => String -> d
kwRuleModulo     = kwModulo "rule"
kwInstanceModulo = kwModulo "instance"
kwTypesModulo    = kwModulo "type assertions"
kwVariantsModulo = kwModulo "variants"


------------------------------------------------------------------------------
-- Operators
------------------------------------------------------------------------------

opProvides, opRequires, opAction, opPath, opLess, opEqual, opDedBefore, opEdge,
  opExists, opForall, opLAnd, opLOr, opImp, opIff, opDot
    :: HighlightDocument d => d
opProvides  = operator_ ":>"
opRequires  = operator_ "<:"
opAction    = operator_ "@"
opPath      = operator_ ">+>"
opLess      = operator_ "<"
opEqual     = operator_ "="
opDedBefore = operator_ "--|"
opEdge      = operator_ ">->"
opExists    = operator_ "∃ " -- "Ex "
opForall    = operator_ "∀ " -- "All "
opLAnd      = operator_ "∧" -- "&"
opLOr       = operator_ "∨" -- "|"
opImp       = operator_ "⇒" -- "==>"
opIff       = operator_ "⇔" -- "<=>"
opDot       = operator_ "."

