-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Parsing Rules

module Theory.Text.Parser.Rule (
       moduloE
     , parseIntruderRules
     , genericRule
     , protoRule
     , intrRule
     , diffRule
)
where

import           Prelude                    hiding (id, (.))
import qualified Data.ByteString            as B
import qualified Data.ByteString.Char8      as BC
import           Data.Label
import           Data.Either
import           Data.Maybe
-- import           Data.Monoid                hiding (Last)
import qualified Data.Text                  as T
import qualified Data.Text.Encoding         as TE
import           Data.Color
import           Control.Applicative        hiding (empty, many, optional)
import           Control.Category
import           Control.Monad
import           Text.Parsec                hiding ((<|>))
import           Term.Substitution
import           Theory
import           Theory.Text.Parser.Token
import           Theory.Text.Parser.Let
import           Theory.Text.Parser.Fact
import           Theory.Text.Parser.Term
import           Theory.Text.Parser.Formula

-- | Parse a "(modulo ..)" information.
modulo :: String -> Parser ()
modulo thy = parens $ symbol_ "modulo" *> symbol_ thy

moduloE, moduloAC :: Parser ()
moduloE   = modulo "E"
moduloAC  = modulo "AC"

{- -- This has not been renamed from typing to source, as it is unclear.
-- | Parse a typing assertion modulo E.
typeAssertions :: Parser TypingE
typeAssertions = fmap TypingE $
    do try (symbols ["type", "assertions"])
       optional moduloE
       colon
       many1 ((,) <$> (try (msgvar <* colon))
                  <*> ( commaSep1 (try $ multterm llit) <|>
                        (opMinus *> pure [])
                      )
             )
    <|> pure []
-}

-- | Parse a 'RuleAttribute'.
ruleAttribute :: Parser (Maybe RuleAttribute)
ruleAttribute = asum
    [ symbol "colour=" *> (Just . RuleColor <$> parseColor)
    , symbol "color="  *> (Just . RuleColor <$> parseColor)
    , symbol "process="  *> parseAndIgnore
    , symbol "derivchecks" *> ignore
    , symbol "no_derivcheck" *> ignore
    , symbol "role=" *> (Just . Role <$> parseRole)
    , symbol "issapicrule" *> return (Just IsSAPiCRule)
    ]
  where
    parseColor = do
        hc <- hexColor
        case hexToRGB hc of
            Just rgb  -> return rgb
            Nothing -> fail $ "Color code " ++ show hc ++ " could not be parsed to RGB"
    parseAndIgnore = do
                        _ <-  symbol "\""
                        _ <- manyTill anyChar (try (symbol "\""))
                        return Nothing
    ignore = return (Just IgnoreDerivChecks)
    parseRole = do
      _ <- symbol "\'" <|> symbol "\""
      manyTill anyChar (try (symbol "\'" <|> symbol "\""))

ruleAttributesp :: Parser [RuleAttribute]
ruleAttributesp = option [] $ catMaybes <$> list ruleAttribute

-- | Parse RuleInfo
protoRuleInfo :: Parser ProtoRuleEInfo
protoRuleInfo = do
                _ <- symbol "rule"
                _ <- optional moduloE
                ident <- identifier
                att <- ruleAttributesp
                _ <- colon
                return $ ProtoRuleEInfo (StandRule ident) att []

-- | Parse a protocol rule. For the special rules 'Reveal_fresh', 'Fresh',
-- 'Knows', and 'Learn' no rule is returned as the default theory already
-- contains them.
diffRule :: Parser DiffProtoRule
diffRule = do
    ri@(ProtoRuleEInfo (StandRule name) _ _)  <- try protoRuleInfo
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst letBlock
    (ps0,as0,cs0,rs0) <- genericRule msgvar nodevar
    let (ps,as,cs,rs) = apply subst (ps0,as0,cs0,rs0)
    leftRight  <- optionMaybe ( (,) <$> (symbol "left"  *> protoRule) <*> (symbol "right" *> protoRule))
    return $ DiffProtoRule (Rule (modify preRestriction (++ rs) ri) ps cs as (newVariables ps $ cs ++ as)) leftRight

-- | Parse a protocol rule. For the special rules 'Reveal_fresh', 'Fresh',
-- 'Knows', and 'Learn' no rule is returned as the default theory already
-- contains them
protoRule :: Parser OpenProtoRule
protoRule = do
    ri@(ProtoRuleEInfo (StandRule name ) _ _)  <- try protoRuleInfo
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst letBlock
    (ps0,as0,cs0,rs0) <- genericRule msgvar nodevar
    let (ps,as,cs,rs) = apply subst (ps0,as0,cs0,rs0)
    variants <- option [] $ symbol "variants" *> commaSep1 protoRuleAC
    return $ OpenProtoRule (Rule (modify preRestriction (++ rs) ri) ps cs as (newVariables ps $ cs ++ as)) variants

-- | Parse RuleInfo
protoRuleACInfo :: Parser ProtoRuleACInfo
protoRuleACInfo = (ProtoRuleACInfo <$> (StandRule <$>
                                        (symbol "rule" *> moduloAC *> identifier))
                               <*> ruleAttributesp)
                               <*> pure (Disj [emptySubstVFresh]) <*> pure []
                               <*  colon

-- | Parse a protocol rule variant modulo AC.
protoRuleAC :: Parser ProtoRuleAC
protoRuleAC = do
    ri@(ProtoRuleACInfo (StandRule name) _ _ _)  <- try protoRuleACInfo
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst letBlock
    (ps0,as0,cs0,rs0) <- genericRule msgvar nodevar
    let (ps,as,cs,_) = apply subst (ps0,as0,cs0,rs0)
    return $ Rule ri ps cs as (newVariables ps $ cs ++ as)

-- | Parse an intruder rule.
intrRule :: Parser IntrRuleAC
intrRule = do
    info <- try (symbol "rule" *> moduloAC *> intrInfo <* colon)
    (ps,as,cs,[]) <- genericRule msgvar nodevar -- intruder rules should not introduce restrictions.
    return $ Rule info ps cs as (newVariables ps cs)
  where
    intrInfo = do
        name     <- identifier
        limit    <- option 0 natural
-- FIXME: Parse whether we have a subterm rule or a constant rule
--        Currently we (wrongly) always assume that we have a subterm rule, this prohibits recomputing variants
        case name of
          'c':cname -> return $ ConstrRule (BC.pack cname)
          'd':dname -> return $ DestrRule (BC.pack dname) (fromIntegral limit) True False
          _         -> fail $ "invalid intruder rule name '" ++ name ++ "'"

embeddedRestriction :: Parser a -> Parser a
embeddedRestriction factParser = symbol "_restrict" *> parens factParser <?> "restriction"

-- factOrRestr ::  Parser (Either SyntacticLNFormula LNFact)
factOrRestr :: (Ord v, Hinted v) => Parser v -> Parser v
                -> Parser (Either (SyntacticNFormula v) (NFact v))
factOrRestr varp nodep = Right <$> fact (vlit varp)
              <|> Left <$> embeddedRestriction (standardFormula varp nodep)


genericRule :: (Ord v, Hinted v) => Parser v -> Parser v -> Parser ([Fact (NTerm v)], [Fact (NTerm v)], [Fact (NTerm v)], [SyntacticFormula (String, LSort) Name v]) --- lhs, actions, rhs, restrictions
genericRule varp nodep = do
    lhs         <- list (fact (vlit varp))
    actsAndRsts <-
        (   (pure [] <* symbol "-->")
        <|> (symbol "--[" *> commaSep (factOrRestr varp nodep) <* symbol "]->")
        )
    rhs <- list (fact (vlit varp))
    return (lhs, rights actsAndRsts, rhs, lefts actsAndRsts)

{-
-- | Add facts to a rule.
addFacts :: String        -- ^ Command to be used: add_concs, add_prems
         -> Parser (String, [LNFact])
addFacts cmd =
    (,) <$> (symbol cmd *> identifier <* colon) <*> commaSep1 fact
-}

-- | Parse DH intruder rules.
parseIntruderRules
    :: MaudeSig -> String -> B.ByteString -> Either ParseError [IntrRuleAC]
parseIntruderRules msig ctxtDesc =
    parseString [] ctxtDesc (setState (mkStateSig msig) >> many intrRule)
  . T.unpack . TE.decodeUtf8
