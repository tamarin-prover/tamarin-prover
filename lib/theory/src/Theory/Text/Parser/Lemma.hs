-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing Lemmas

module Theory.Text.Parser.Lemma(
      lemma
      , plainLemma
      , diffLemma
)
where

import           Prelude                    hiding (id, (.))
import           Data.Foldable              (asum)
-- import           Data.Monoid                hiding (Last)
import           Control.Applicative        hiding (empty, many, optional)
import           Text.Parsec                hiding ((<|>))
import           Theory
import           Theory.Text.Parser.Token
import           Debug.Trace
import Theory.Text.Parser.Formula
import Theory.Text.Parser.Rule
import Theory.Text.Parser.Proof

-- | Parse a 'LemmaAttribute'.
lemmaAttribute :: Bool -> Parser LemmaAttribute
lemmaAttribute diff = asum
  [ symbol "typing"        *> trace ("Deprecation Warning: using 'typing' is retired notation, replace all uses of 'typing' by 'sources'.\n") pure SourceLemma -- legacy support, emits deprecation warning
--  , symbol "typing"        *> fail "Using 'typing' is retired notation, replace all uses of 'typing' by 'sources'."
  , symbol "sources"       *> pure SourceLemma
  , symbol "reuse"         *> pure ReuseLemma
  , symbol "diff_reuse"    *> pure ReuseDiffLemma
  , symbol "use_induction" *> pure InvariantLemma
  , symbol "hide_lemma="   *> (HideLemma <$> identifier)
  , symbol "heuristic="    *> (LemmaHeuristic <$> parseGoalRanking)
  , symbol "left"          *> pure LHSLemma
  , symbol "right"         *> pure RHSLemma
--   , symbol "both"          *> pure BothLemma
  ]
  where
    parseGoalRanking = case diff of
        True  -> map charToGoalRankingDiff <$> many1 letter
        False -> map charToGoalRanking     <$> many1 letter

-- | Parse a 'TraceQuantifier'.
traceQuantifier :: Parser TraceQuantifier
traceQuantifier = asum
  [ symbol "all-traces" *> pure AllTraces
  , symbol "exists-trace"  *> pure ExistsTrace
  ]

protoLemma :: Parser f -> Parser (ProtoLemma f ProofSkeleton)
protoLemma parseFormula = skeletonLemma <$> (symbol "lemma" *> optional moduloE *> identifier)
                      <*> (option [] $ list (lemmaAttribute False))
                      <*> (colon *> option AllTraces traceQuantifier)
                      <*> doubleQuoted parseFormula
                      <*> (startProofSkeleton <|> pure (unproven ()))

-- | Parse a lemma.
lemma :: Parser (SyntacticLemma ProofSkeleton)
lemma = protoLemma standardFormula

-- | Parse a lemma w/o syntactic sugar
plainLemma :: Parser (Lemma ProofSkeleton)
plainLemma = protoLemma plainFormula

-- | Parse a diff lemma.
diffLemma :: Parser (DiffLemma DiffProofSkeleton)
diffLemma = skeletonDiffLemma <$> (symbol "diffLemma" *> identifier)
                              <*> (option [] $ list (lemmaAttribute True))
                              <*> (colon *> (diffProofSkeleton <|> pure (diffUnproven ())))