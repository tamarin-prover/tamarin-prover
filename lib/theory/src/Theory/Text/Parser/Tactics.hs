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
    -- , aledTactic
)
where

import           Prelude                    hiding (id)
import           Control.Applicative        hiding (empty, many, optional)
import qualified Data.Map                   as M

import           Theory
import           Theory.Constraint.Solver.AnnotatedGoals
import           Theory.Constraint.Solver.Heuristics
import           Theory.Text.Pretty         hiding (char,colon,symbol,opLAnd,opLOr, space)
import           Theory.Text.Parser.Token
import           Theory.Text.Parser.Signature

import           Text.Parsec                hiding ((<|>))
import           Text.Regex.PCRE


-- import           Debug.Trace


--Tactic
tacticName :: Parser String
tacticName = do
    _ <- symbol "tactic"
    _ <- colon
    tName <- identifier
    return tName

goalRankingPresort :: Bool -> Parser GoalRanking
goalRankingPresort diff = regularRanking <?> "goal ranking"
   where
       regularRanking = toGoalRanking <$> many1 letter <* skipMany (char ' ')

       toGoalRanking = if diff then stringToGoalRankingDiff True else stringToGoalRanking True

-- Default heuristic
selectedPreSort :: Bool -> Parser GoalRanking
selectedPreSort diff = do
    _ <- symbol "presort"
    _ <- colon
    presort <- goalRankingPresort diff <* lexeme spaces 
    return $ presort

--Function name
functionName :: Parser String
functionName = many space *> many (alphaNum <|> oneOf "[]_-@")

--Function value
functionValue :: Parser String
functionValue = many $ noneOf "\"" --interdit de mettre des " dans les regex, dommage


--Fonction (fonction, pretty printing)
function :: Parser (AnnotatedGoal -> Bool, String)
function = do
    f <- identifier
    v <- doubleQuoted functionValue
    return $ (nameToFunction (f,v),f++" \""++v++"\"")

functionNot :: (AnnotatedGoal -> Bool, String) -> (AnnotatedGoal -> Bool, String)
functionNot (f,s) = (not . f, "not "++s)

functionAnd :: (AnnotatedGoal -> Bool, String) -> (AnnotatedGoal -> Bool, String) -> (AnnotatedGoal -> Bool, String)
functionAnd (f,s1) (g,s2) = ((\x -> and [f x, g x]),s1++" & "++s2)

functionOr :: (AnnotatedGoal -> Bool, String) -> (AnnotatedGoal -> Bool, String) -> (AnnotatedGoal -> Bool, String)
functionOr (f,s1) (g,s2) = ((\x -> or [f x, g x]),s1++" | "++s2)

-- | Parse a negation.
negation :: Parser (AnnotatedGoal -> Bool, String)
negation = opLNot *> (functionNot <$> function) <|> function

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser (AnnotatedGoal -> Bool, String)
conjuncts = chainl1 negation (functionAnd <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser (AnnotatedGoal -> Bool, String)
disjuncts = try $ (chainl1 conjuncts (functionOr <$ opLOr)) -- error here is not triggered when empty prio (appends higher -> function parsing)

--Parsing prio
prio :: Parser Prio
prio = do
    _ <- symbol "prio"
    _ <- colon
    fs <- many1 disjuncts
    return $ Prio (map fst fs) (map snd fs)

--Parsing deprio
deprio :: Parser Deprio
deprio = do
    _ <- symbol "deprio"
    _ <- colon
    fs <- many1 disjuncts
    return $ Deprio (map fst fs) (map snd fs)


tactic :: Bool -> Parser TacticI
tactic diff = do
    tName <- tacticName
    presort <- option (SmartRanking False) (selectedPreSort diff)
    prios <- option [] $ many1 prio
    deprios <- option [] $ many1 deprio
    return $ TacticI tName presort prios deprios

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
    -- Not necessarily usefull line
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
