-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing Tactics
------------------------------------------------------------------------------

module Theory.Text.Parser.Tactics (
    tactic
)
where

import           Prelude                    hiding (id)
import           Control.Applicative        hiding (empty, many, optional)
import qualified Data.Map                   as M

import           Theory
import           Theory.Constraint.Solver.AnnotatedGoals
import           Theory.Text.Pretty         hiding (char,colon,symbol,opLAnd,opLOr)
import           Theory.Text.Parser.Token

import           Text.Parsec                hiding ((<|>))
import           Text.Regex.Posix

import           Debug.Trace


--Tactic
tacticName :: Parser String
tacticName = do 
    _ <- string "tactic"
    _ <- char ':'
    _ <- skipMany (char ' ')
    tName <- many (alphaNum <|> oneOf "_-@")
    _ <- newline
    return $ tName
-- Default heuristic
selectedPreSort :: Parser Char
selectedPreSort = string "heuristic" *> char ':' *> skipMany (char ' ') *> letter <* newline

--Function name
functionName :: Parser String
functionName = many (char ' ' <|> char '\t') *> many (alphaNum <|> oneOf "[]_-@")

--Function value
functionValue :: Parser String
functionValue = many $ noneOf "\n"

--Fonction
function :: Parser (AnnotatedGoal -> Bool)
function = do
    f <- functionName
    _ <- char ' '
    v <- functionValue
    _ <- newline
    return $ trace (show (f,v)) nameToFunction (f,v)

functionNot :: (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool)
functionNot f = not . f

functionAnd :: (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool)
functionAnd f g = (\x -> and [f x, g x])

functionOr :: (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool)
functionOr f g = (\x -> or [f x, g x])

-- | Parse a negation.
negation :: Parser (AnnotatedGoal -> Bool)
negation = opLNot *> (functionNot <$> function) <|> function

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser (AnnotatedGoal -> Bool)
conjuncts = chainl1 negation (functionAnd <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser (AnnotatedGoal -> Bool)
disjuncts = lookAhead (noneOf $ "prio:" <|> "deprio:") *> skipMany (char ' ') *> chainl1 conjuncts (functionOr <$ opLOr)

--Parsing prio
prio :: Parser Prio
prio = do
    _ <- string "prio:"
    _ <- skipMany (char ' ')
    _ <- newline
    fs <- many1 disjuncts
    -- _ <- newline
    return $ trace (show fs) Prio fs

--Parsing deprio
deprio :: Parser Deprio
deprio = do 
    _ <- string "deprio:"
    _ <- skipMany (char ' ')
    _ <- newline
    fs <- many1 negation
    -- _ <- newline
    return $ Deprio fs

tacticFunctions :: M.Map String (String -> AnnotatedGoal -> Bool)
tacticFunctions = M.fromList
                      [ ("regex", regex')
                      , ("isFactName", isFactName)
                      , ("isInFactTerms", isInFactTerms)
                      ]
  where 
    regex' :: String -> AnnotatedGoal -> Bool
    regex' s agoal = pg =~ s
        where
            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pg = concat . lines . render $ pgoal agoal

    isFactName :: String -> AnnotatedGoal -> Bool
    isFactName s ((PremiseG _ Fact {factTag = ProtoFact Linear test _, factAnnotations = _ , factTerms = _ }), (_,_)) = test == s
    -- Ligne pas forcément utile
    isFactName s (ActionG _ (Fact { factTag = test ,factAnnotations =  _ , factTerms = _ }), _ ) = show test == s
    isFactName _ _ = False

    isInFactTerms :: String -> AnnotatedGoal -> Bool
    isInFactTerms s (ActionG _ (Fact { factTag = _ ,factAnnotations =  _ , factTerms = [test]}), _ ) = show test =~ s
    isInFactTerms _ _ = False

nameToFunction :: (String, String) -> AnnotatedGoal -> Bool
nameToFunction (s,param) = case M.lookup s tacticFunctions of 
  Just f  -> f param
  Nothing ->  error $ "\nThe function "++ s
            ++" is not defined.\nUse one of the following:\n"++listTacticFunction

  where
    tacticFunctionName :: String -> String
    tacticFunctionName funct = case funct of
            "regex"            -> "match between the pretty goal and the given regex"
            "isFactName"       -> "match against the fact name"
            "isInFactTerms"    -> "match against the fact terms"
            _                  -> ""

    listTacticFunction:: String
    listTacticFunction = M.foldMapWithKey
        (\k _ -> "'"++k++"': " ++ tacticFunctionName k ++ "\n") tacticFunctions


tactic :: Parser TacticI
tactic = do
    tName <- tacticName
    heuristicDef <- option 's' selectedPreSort
    prios <- option [] $ many1 prio
    deprios <- option [] $ many1 deprio
    _ <- many1 newline
    return $ TacticI tName heuristicDef prios deprios
 
