-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing protocol theories. See the MANUAL for a high-level description of
-- the syntax.

module Theory.Text.Parser.Let(
    letBlock
)
where

import Term.Substitution
import Theory.Text.Parser.Token
import Text.Parsec
import Theory.Text.Parser.Term

-- | Parse a let block with bottom-up application semantics.
letBlock :: Parser LNSubst
letBlock = toSubst <$> (symbol "let" *> many1 definition <* symbol "in")
  where
    toSubst = foldr1 compose . map (substFromList . return)
    definition = (,) <$> (sortedLVar [LSortMsg] <* equalSign) <*> msetterm False llit