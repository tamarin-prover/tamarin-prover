-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
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
import Control.Basics

smallerp :: Ord v => Parser v -> Parser (ProtoAtom SyntacticSugar (Term (Lit Name v)))
smallerp varp = do
    mset <- enableMSet . sig <$> getState
    unless mset (fail "Need builtins: multiset to use multiset comparison operator.")
    a <- try (termp <* opLessTerm)
    b <- termp
    return $ (Syntactic . Pred) $ protoFact Linear "Smaller" [a,b]
  where
    termp =  msetterm False (vlit varp)

------------------------------------------------------------------------------
-- Parsing Standard and Guarded Formulas
------------------------------------------------------------------------------
-- | Parse an atom with possibly bound logical variables.
blatom :: (Hinted v, Ord v) => Parser v -> Parser v -> Parser (SyntacticAtom (VTerm Name (BVar v)))
blatom varp nodep = fmap (fmapTerm (fmap Free)) <$> asum
  [ Last        <$> try (symbol "last" *> parens nodevarTerm)        <?> "last atom"
  , flip Action <$> try (fact (vlit varp) <* opAt)        <*> nodevarTerm   <?> "action atom"
  , Subterm     <$> try (msetterm False (vlit varp) <* opSubterm) <*> msetterm False (vlit varp) <?> "subterm predicate"    
  , Less        <$> try (nodevarTerm <* opLess)    <*> nodevarTerm   <?> "less atom"
  , smallerp varp <?> "multiset comparisson"
  , EqE         <$> try (termp <* opEqual) <*> termp <?> "term equality"
  , Syntactic . Pred <$> try (fact (vlit (try varp <|> nodep) ))                    <?> "predicate atom"
      -- Predicates can be called for timepoints in addition to other logical vars.
      -- Note that lexemes that are ambigous (e.g., a variable without a sort)
      -- will be interpreted by varp.
  , EqE         <$>     (nodevarTerm  <* opEqual)  <*> nodevarTerm   <?> "node equality"
  ]
  where
    nodevarTerm = lit . Var <$> nodep
    termp =  msetterm False (vlit varp)


-- | Parse an atom of a formula.
fatom :: (Hinted v, Ord v) => Parser v -> Parser v -> Parser (SyntacticNFormula v)
fatom varp nodep = asum
  [ lfalse <$ opLFalse
  , ltrue <$ opLTrue
  , Ato <$> try (blatom varp nodep)
  , quantification
  , parens (iff varp nodep)
  ]
  where
    quantification = do
        q <- (forAll <$ opForall) <|> (exists <$ opExists)
        vs <- many1 (try varp <|> nodep)  <* dot
        f  <- iff varp nodep
        return $ foldr (hinted q) f vs

-- | Parse a negation.
negation :: (Hinted v, Ord v) => Parser v -> Parser v -> Parser (SyntacticNFormula v)
negation varp nodep = opLNot *> (Not <$> fatom varp nodep) <|> fatom varp nodep

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: (Hinted v, Ord v) => Parser v -> Parser v -> Parser (SyntacticNFormula v)
conjuncts varp nodep = chainl1 (negation varp nodep) ((.&&.) <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: (Hinted v, Ord v) => Parser v -> Parser v -> Parser (SyntacticNFormula v)
disjuncts varp nodep = chainl1 (conjuncts varp nodep) ((.||.) <$ opLOr)

-- | An implication.
imp :: (Hinted v, Ord v) => Parser v -> Parser v -> Parser (SyntacticNFormula v)
imp varp nodep = do
  lhs <- disjuncts varp nodep
  asum [ opImplies *> ((lhs .==>.) <$> imp varp nodep)
       , pure lhs ]

-- | An logical equivalence.
-- iff :: Parser SyntacticLNFormula
-- iff :: Parser (VTerm n v) -> Parser (SyntacticFormula (String, LSort) n v)
iff :: (Hinted v, Ord v) => Parser v  -> Parser v -> Parser (SyntacticNFormula v)
iff varp nodep = do
  lhs <- imp varp nodep
  asum [opLEquiv *> ((lhs .<=>.) <$> imp varp nodep), pure lhs ]

-- | Parse a standard formula.
-- standardFormula :: Parser (SyntacticLNFormula)
standardFormula :: (Hinted v, Ord v) => Parser v  -> Parser v -> Parser (SyntacticNFormula v)
standardFormula = iff


plainFormula :: Parser LNFormula
plainFormula = try $ do
    lnf <- toLNFormula <$> standardFormula msgvar nodevar
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
