-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing Signatures
------------------------------------------------------------------------------

module Theory.Text.Parser.Signature (
    heuristic
    , builtins
    , options
    , functions
    , equations
    , preddeclaration
    , goalRanking
    , diffbuiltins
)
where

import           Prelude                    hiding (id)
import qualified Data.ByteString.Char8      as BC
import           Data.Foldable              (asum)
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           Control.Applicative        hiding (empty, many, optional)
import           Control.Monad
import qualified Control.Monad.Catch        as Catch
import           Text.Parsec                hiding ((<|>))
import           Term.Substitution
import           Term.SubtermRule
import           Theory
import           Theory.Text.Parser.Token
import Theory.Text.Parser.Fact
import Theory.Text.Parser.Term
import Theory.Text.Parser.Formula
import Theory.Text.Parser.Exceptions


-- | Builtin signatures.
builtins :: OpenTheory -> Parser OpenTheory
builtins thy0 =do
            _  <- symbol "builtins"
            _  <- colon
            l <- commaSep1 builtinTheory -- l is list of lenses to set options to true with
                                         -- builtinTheory modifies signature in state.
            return $ foldl setOption' thy0 l
  where
    setOption' thy Nothing  = thy
    setOption' thy (Just l) = setOption l thy
    extendSig msig = do
        modifyState (`mappend` msig)
        return Nothing
    builtinTheory = asum
      [ try (symbol "diffie-hellman")
          *> extendSig dhMaudeSig
      , try (symbol "bilinear-pairing")
          *> extendSig bpMaudeSig
      , try (symbol "multiset")
          *> extendSig msetMaudeSig
      , try (symbol "xor")
          *> extendSig xorMaudeSig
      , try (symbol "symmetric-encryption")
          *> extendSig symEncMaudeSig
      , try (symbol "asymmetric-encryption")
          *> extendSig asymEncMaudeSig
      , try (symbol "signing")
          *> extendSig signatureMaudeSig
      , try (symbol "revealing-signing")
          *> extendSig revealSignatureMaudeSig
      , try (symbol "locations-report")
          *>  do
          modifyState (`mappend` locationReportMaudeSig)
          return (Just transReport)
      , try ( symbol "reliable-channel")
             *> return (Just transReliable)
      , symbol "hashing"
          *> extendSig hashMaudeSig
      ]

diffbuiltins :: Parser ()
diffbuiltins =
    symbol "builtins" *> colon *> commaSep1 builtinTheory *> pure ()
  where
    extendSig msig = modifyState (`mappend` msig)
    builtinTheory = asum
      [ try (symbol "diffie-hellman")
          *> extendSig dhMaudeSig
      , try (symbol "bilinear-pairing")
          *> extendSig bpMaudeSig
      , try (symbol "multiset")
          *> extendSig msetMaudeSig
      , try (symbol "xor")
          *> extendSig xorMaudeSig
      , try (symbol "symmetric-encryption")
          *> extendSig symEncMaudeSig
      , try (symbol "asymmetric-encryption")
          *> extendSig asymEncMaudeSig
      , try (symbol "signing")
          *> extendSig signatureMaudeSig
      , try (symbol "revealing-signing")
          *> extendSig revealSignatureMaudeSig
      , symbol "hashing"
          *> extendSig hashMaudeSig
      ]


functions :: Parser ()
functions =
    symbol "functions" *> colon *> commaSep1 functionSymbol *> pure ()
  where
    functionSymbol = do
        f   <- BC.pack <$> identifier <* opSlash
        k   <- fromIntegral <$> natural
        priv <- option Public (symbol "[private]" *> pure Private)
        if (BC.unpack f `elem` ["mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor"])
          then fail $ "`" ++ BC.unpack f ++ "` is a reserved function name for builtins."
          else return ()
        sig <- getState
        case lookup f [ o | o <- (S.toList $ stFunSyms sig)] of
          Just kp' | kp' /= (k,priv) ->
            fail $ "conflicting arities/private " ++
                   show kp' ++ " and " ++ show (k,priv) ++
                   " for `" ++ BC.unpack f
          _ -> setState (addFunSym (f,(k,priv)) sig)

equations :: Parser ()
equations =
      symbol "equations" *> colon *> commaSep1 equation *> pure ()
    where
      equation = do
        rrule <- RRule <$> term llitNoPub True <*> (equalSign *> term llitNoPub True)
        case rRuleToCtxtStRule rrule of
          Just str ->
              modifyState (addCtxtStRule str)
          Nothing  ->
              fail $ "Not a correct equation: " ++ show rrule

-- | options
options :: OpenTheory -> Parser OpenTheory
options thy0 =do
            _  <- symbol "options"
            _  <- colon
            l <- commaSep1 builtinTheory -- l is list of lenses to set options to true with
                                         -- builtinTheory modifies signature in state.
            return $ foldl setOption' thy0 l
  where
    setOption' thy Nothing  = thy
    setOption' thy (Just l) = setOption l thy
    builtinTheory = asum
      [  try (symbol "translation-progress")
             *> return (Just transProgress)
        , symbol "translation-allow-pattern-lookups"
             *> return (Just transAllowPatternMatchinginLookup)
      ]


predicate :: Parser Predicate
predicate = do
           f <- fact' lvar
           _ <- symbol "<=>"
           form <- plainFormula
           return $ Predicate f form
           <?> "predicate declaration"

preddeclaration :: OpenTheory -> Parser OpenTheory
preddeclaration thy = do
                    _          <- try (symbol "predicates") <|> symbol "predicate"
                    _          <- colon
                    predicates <- commaSep1 predicate
                    foldM liftedAddPredicate thy predicates
                    <?> "predicates"

heuristic :: Bool -> Maybe FilePath -> Parser [GoalRanking]
heuristic diff workDir = symbol "heuristic" *> char ':' *> skipMany (char ' ') *> many1 (goalRanking diff workDir) <* spaces

goalRanking :: Bool -> Maybe FilePath -> Parser GoalRanking
goalRanking diff workDir = try oracleRanking <|> regularRanking <?> "goal ranking"
   where
       regularRanking = toGoalRanking <$> letter <* skipMany (char ' ')

       oracleRanking = do
           goal <- toGoalRanking <$> oneOf "oO" <* skipMany (char ' ')
           relPath <- optionMaybe (char '"' *> many1 (noneOf "\"\n\r") <* char '"' <* skipMany (char ' '))

           return $ mapOracleRanking (maybeSetOracleRelPath relPath . maybeSetOracleWorkDir workDir) goal

       toGoalRanking = if diff then charToGoalRankingDiff else charToGoalRanking


liftedAddPredicate :: Catch.MonadThrow m =>
                      Theory sig c r p SapicElement
                      -> Predicate -> m (Theory sig c r p SapicElement)
liftedAddPredicate thy prd = liftMaybeToEx (DuplicateItem (PredicateItem prd)) (addPredicate prd thy)
