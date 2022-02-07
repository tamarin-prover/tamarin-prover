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
import           Data.Foldable              (asum,msum)
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
    _ <- symbol "tactic"
    _ <- char ':'
    _ <- skipMany (char ' ')
    tName <- many (alphaNum <|> oneOf "_-@")
    _ <- newline
    return $ trace (show tName) tName

-- Default heuristic
selectedPreSort :: Parser Char
selectedPreSort = do 
    _ <- string "heuristic" *> char ':' *> skipMany (char ' ') 
    oui <- letter <* newline
    return $ trace (show oui) oui 

--Function name
functionName :: Parser String
functionName = many (char ' ' <|> char '\t') *> many (alphaNum <|> oneOf "[]_-@")

--Function value
functionValue :: Parser String
functionValue = many $ noneOf "\n|&\""
    {-liftA concat (manyTill (many (noneOf "\n)\\") <|> char '\\' *> escaped) eof )
    where 
        escaped = do 
            c <- anyChar
            return $ '\\':[c] -}

--Fonction
function :: Parser (AnnotatedGoal -> Bool)
function = do
    _ <- skipMany (char ' ')
    f <- functionName
    _ <- skipMany $ char ' '
    _ <- char '"'
    v <- functionValue
    _ <- char '"'
    _ <- skipMany (char ' ')
    return $ trace (show $ (f,v)) nameToFunction (f,v)

functionNot :: (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool)
functionNot f = not . f

functionAnd :: (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool)
functionAnd f g = (\x -> and [f x, g x])

functionOr :: (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool) -> (AnnotatedGoal -> Bool)
functionOr f g = (\x -> or [f x, g x])

-- | Parse a negation.
negation :: Parser (AnnotatedGoal -> Bool)
negation = opLNot *> (functionNot <$> function) <|> function
-- opLNot *> (functionNot <$> between (char '(') (char ')') function) <|> between (char '(') (char ')') function

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser (AnnotatedGoal -> Bool)
conjuncts = chainl1 negation (functionAnd <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser (AnnotatedGoal -> Bool)
disjuncts = lookAhead (noneOf $ "prio:" <|> "deprio:") *> skipMany (char ' ') *> chainl1 conjuncts (functionOr <$ opLOr) <* newline

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


tactic :: Parser TacticI
tactic = do
    tName <- tacticName
    heuristicDef <- option 's' selectedPreSort -- type String
    prios <- option [] $ many1 prio            -- type [Prio]
    deprios <- option [] $ many1 deprio
    _ <- many1 newline
    return $ TacticI tName heuristicDef prios deprios

{-setTacticName :: TacticI -> String -> TacticI
setTacticName tactic name = TacticI name (tacticiHeuristic tactic) (tacticiPrio tactic) (tacticiDeprio tactic) 

setTacticPresort :: TacticI -> Char -> TacticI
setTacticPresort tactic presort = TacticI (tacticiName tactic) presort (tacticiPrio tactic) (tacticiDeprio tactic) 

setTacticPrios :: TacticI -> [Prio] -> TacticI
setTacticPrios tactic prios = TacticI (tacticiName tactic) (tacticiHeuristic tactic) prios (tacticiDeprio tactic) 

setTacticDeprios :: TacticI -> [Deprio] -> TacticI
setTacticDeprios tactic deprios = TacticI (tacticiName tactic) (tacticiHeuristic tactic) (tacticiPrio tactic) deprios

aledTactic :: TacticI -> Parser TacticI
aledTactic tactic = asum 
    [ do tName <- tacticName
         return $ setTacticName tactic tName
    , do presort <- option 's' selectedPreSort
         return $ setTacticPresort tactic presort
    , do prios <- option [] $ many1 prio
         return $ setTacticPrios tactic prios
    , do deprios <- option [] $ many1 deprio
         _ <- many1 newline
         return $ setTacticDeprios tactic deprios
    ] -}

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
