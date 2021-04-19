-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing Restrictions

module Theory.Text.Parser.Restriction
  ( parseRestriction
    , restriction
    , legacyAxiom
    , diffRestriction
    , legacyDiffAxiom
    , isLeftRestriction
    , isRightRestriction
    , toRestriction
  )
where

------------------------------------------------------------------------------
-- ParseRestriction datatype and functions to parse diff restrictions
------------------------------------------------------------------------------
import           Prelude                    hiding (id, (.))
import           Data.Foldable              (asum)
-- import           Data.Monoid                hiding (Last)
import           Text.Parsec                hiding ((<|>))
import           Theory
import           Debug.Trace

import Theory.Text.Parser.Token
import Theory.Text.Parser.Formula

-- | A restriction describes a property that must hold for all traces.
-- | Restrictions are always used as lemmas in proofs.
data ParseRestriction = ParseRestriction
       { pRstrName       :: String
       , pRstrAttributes :: [RestrictionAttribute]
       , pRstrFormula    :: LNFormula
       }
       deriving( Eq, Ord, Show )

-- | True iff the restriction is a LHS restriction.
isLeftRestriction :: ParseRestriction -> Bool
isLeftRestriction rstr =
     LHSRestriction `elem` pRstrAttributes rstr

-- | True iff the restriction is a RHS restriction.
isRightRestriction :: ParseRestriction -> Bool
isRightRestriction rstr =
     RHSRestriction `elem` pRstrAttributes rstr

-- -- | True iff the restriction is a Both restriction.
-- isBothRestriction :: ParseRestriction -> Bool
-- isBothRestriction rstr =
--      (BothRestriction `elem` pRstrAttributes rstr)

-- | Converts ParseRestrictions to Restrictions
toRestriction :: ParseRestriction -> Restriction
toRestriction rstr = Restriction (pRstrName rstr) (pRstrFormula rstr)

-- | Parse a lemma for an open theory from a string.
parseRestriction :: String -> Either ParseError SyntacticRestriction
parseRestriction = parseString "<unknown source>" restriction

-- | Parse a 'RestrictionAttribute'.
restrictionAttribute :: Parser RestrictionAttribute
restrictionAttribute = asum
  [ symbol "left"          *> pure LHSRestriction
  , symbol "right"         *> pure RHSRestriction
  , symbol "both"          *> pure BothRestriction
  ]

-- | Parse a restriction.
restriction :: Parser SyntacticRestriction
restriction = Restriction <$> (symbol "restriction" *> identifier <* colon)
                          <*> doubleQuoted standardFormula

-- | Fail on parsing an old "axiom" keyword.
--legacyAxiom :: Parser Restriction
--legacyAxiom = symbol "axiom" *> fail "Using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'."

-- | Parse a legacy axiom, now called restriction.
legacyAxiom :: Parser SyntacticRestriction
legacyAxiom = trace ("Deprecation Warning: using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'.") Restriction <$> (symbol "axiom" *> identifier <* colon)
                          <*> doubleQuoted standardFormula

-- | Parse a diff restriction.
diffRestriction :: Parser ParseRestriction
diffRestriction = ParseRestriction <$> (symbol "restriction" *> identifier)
                    <*> (option [] $ list restrictionAttribute)
                    <*> (colon *> doubleQuoted plainFormula)

-- | Fail on parsing an old "axiom" keyword.
--legacyDiffAxiom :: Parser ParseRestriction
--legacyDiffAxiom = symbol "axiom" *> fail "Using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'."

-- | Parse a legacy diff axiom, now called restriction. Emits warning.
legacyDiffAxiom :: Parser ParseRestriction
legacyDiffAxiom = trace ("Deprecation Warning: using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'.") ParseRestriction <$> (symbol "axiom" *> identifier)
              <*> (option [] $ list restrictionAttribute)
              <*> (colon *> doubleQuoted plainFormula)