-- Copyright   : (c) 2021 Robert Künnemann, Kevin Morio & Yavor Ivanov
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Parsing items needed for accountability.

module Theory.Text.Parser.Accountability(
        caseTest
      , lemmaAcc 
)
where

import           Prelude                    hiding (id, (.))
import           Theory
import           Theory.Text.Parser.Token
import           Theory.Text.Parser.Formula
import           Theory.Text.Parser.Lemma
import Text.Parsec
import Data.Either (lefts)

-- | Parse a case test which is used in an accountability lemma.
caseTest :: Parser CaseTest
caseTest =  CaseTest <$> (symbol "test" *> identifier)
                     <*> (colon *> doubleQuoted (standardFormula msgvar nodevar))

-- | Parse an accountability lemma.
lemmaAcc :: Maybe FilePath -> Parser AccLemma
lemmaAcc workDir = try $ do
               _ <-  symbol "lemma"
               name <- identifier
               attributes <- option [] $ list (try (Left <$> lemmaAttribute False workDir))
               _ <-  colon
               identifiers <- commaSep1 $ identifier
               _ <-  try (symbol "accounts for") <|> symbol "account for"
               formula <-  doubleQuoted $ standardFormula msgvar nodevar
               return $ AccLemma name (lefts attributes) identifiers [] formula
