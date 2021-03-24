-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing Standard and Guarded Formulas

module Theory.Text.Parser.Formula
  ( standardFormula,
    plainFormula,
    guardedFormula,
  )
where
import           Prelude                    hiding (id, (.))
import           Data.Foldable              (asum)
-- import           Data.Monoid                hiding (Last)
import           Control.Applicative        hiding (empty, many, optional)
import           Control.Category
import           Text.Parsec                hiding ((<|>))
import           Text.PrettyPrint.Class     (render)
import           Term.Substitution
import           Theory
import           Theory.Text.Parser.Token

import           Theory.Text.Parser.Fact
import           Theory.Text.Parser.Term

-- | Parse an atom with possibly bound logical variables.
blatom :: Parser (SyntacticAtom BLTerm)
blatom = fmap (fmapTerm (fmap Free)) <$> asum
  [ Last        <$> try (symbol "last" *> parens nodevarTerm)        <?> "last atom"
  , flip Action <$> try (fact llit <* opAt)        <*> nodevarTerm   <?> "action atom"
  , Syntactic . Pred <$> try (fact llit)                             <?> "predicate atom"
  , Less        <$> try (nodevarTerm <* opLess)    <*> nodevarTerm   <?> "less atom"
  , EqE         <$> try (msetterm False llit <* opEqual) <*> msetterm False llit <?> "term equality"
  , EqE         <$>     (nodevarTerm  <* opEqual)  <*> nodevarTerm   <?> "node equality"
  ]
  where
    nodevarTerm = lit . Var <$> nodevar

-- | Parse an atom of a formula.
fatom :: Parser  SyntacticLNFormula
fatom = asum
  [ pure lfalse <* opLFalse
  , pure ltrue  <* opLTrue
  , Ato <$> try blatom
  , quantification
  , parens iff
  ]
  where
    quantification = do
        q <- (pure forall <* opForall) <|> (pure exists <* opExists)
        vs <- many1 lvar <* dot
        f  <- iff
        return $ foldr (hinted q) f vs

-- | Parse a negation.
negation :: Parser SyntacticLNFormula
negation = opLNot *> (Not <$> fatom) <|> fatom

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser SyntacticLNFormula
conjuncts = chainl1 negation ((.&&.) <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser SyntacticLNFormula
disjuncts = chainl1 conjuncts ((.||.) <$ opLOr)

-- | An implication.
imp :: Parser SyntacticLNFormula
imp = do
  lhs <- disjuncts
  asum [ opImplies *> ((lhs .==>.) <$> imp)
       , pure lhs ]

-- | An logical equivalence.
iff :: Parser SyntacticLNFormula
iff = do
  lhs <- imp
  asum [opLEquiv *> ((lhs .<=>.) <$> imp), pure lhs ]

-- | Parse a standard formula.
standardFormula :: Parser (SyntacticLNFormula)
standardFormula = iff


plainFormula :: Parser LNFormula
plainFormula = try $ do
    lnf <- toLNFormula <$> standardFormula
    case lnf of
        Nothing -> fail "Syntactic sugar is not allowed, guarded formula expected."
        Just lnf' -> return lnf'

-- | Parse a guarded formula using the hack of parsing a standard formula and
-- converting it afterwards.
-- FIXME: Write a proper parser.
guardedFormula :: Parser LNGuarded
guardedFormula = do
    pf <- plainFormula
    case formulaToGuarded pf of
           Left d   -> fail $ render d
           Right gf -> return gf
