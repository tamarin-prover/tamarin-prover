-- |
--  Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
--  License     : GPL v3 (see LICENSE)
--
--  Maintainer  : Simon Meier <iridcode@gmail.com>
--  Portability : portable
--
--  Parsing facts.

module Theory.Text.Parser.Fact
  ( fact,
    fact',
  )
where
import Theory.Text.Parser.Token
import Theory.Model.Fact
import Term.LTerm
import qualified Data.Set as S


import           Prelude                    hiding (id, (.))
import           Data.Char                  (isUpper, toUpper)
import           Data.Foldable              (asum)
-- import           Data.Monoid                hiding (Last)
import           Control.Category
import           Text.Parsec                hiding ((<|>))

import Theory.Text.Parser.Term

-- | Parse a fact annotation
factAnnotation :: Parser FactAnnotation
factAnnotation = asum
  [ opPlus  *> pure SolveFirst
  , opMinus *> pure SolveLast
  , symbol "no_precomp" *> pure NoSources
  ]

-- | Parse a fact that does not necessarily have a term in it.
fact' :: Parser t -> Parser (Fact t)
fact' pterm = try (
    do multi <- option Linear (opBang *> pure Persistent)
       i     <- identifier
       case i of
         []                -> fail "empty identifier"
         (c:_) | isUpper c -> if (map toUpper i == "FR") && multi == Persistent then fail "fresh facts cannot be persistent" else return ()
               | otherwise -> fail "facts must start with upper-case letters"
       ts    <- parens (commaSep pterm)
       ann   <- option [] $ list factAnnotation
       mkProtoFact multi i (S.fromList ann) ts
    <?> "fact" )
  where
    singleTerm _ constr [t] = return $ constr t
    singleTerm f _      ts  = fail $ "fact '" ++ f ++ "' used with arity " ++
                                     show (length ts) ++ " instead of arity one"

    mkProtoFact multi f ann = case map toUpper f of
      "OUT" -> singleTerm f outFact
      "IN"  -> singleTerm f (inFactAnn ann)
      "KU"  -> singleTerm f kuFact
      "KD"  -> singleTerm f kdFact
      "DED" -> singleTerm f dedLogFact
      "FR"  -> singleTerm f freshFact
      _     -> return . protoFactAnn multi f ann

-- | Parse a fact.
fact :: Ord l => Parser (Term l) -> Parser (Fact (Term l))
fact plit = fact' (msetterm False plit)
