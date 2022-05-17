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
import qualified Extension.Data.Label       as L
import qualified Data.Set                             as S

import           Theory
import           Theory.Constraint.Solver.AnnotatedGoals
--import           Theory.Constraint.Solver.Heuristics
--import           Theory.Constraint.System.Guarded
import           Theory.Text.Pretty         hiding (char,colon,symbol,opLAnd,opLOr, space)
import           Theory.Text.Parser.Token
--import           Theory.Text.Parser.Signature

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

goalRankingPresort :: Bool -> Parser (GoalRanking ProofContext)
goalRankingPresort diff = regularRanking <?> "goal ranking"
   where
       regularRanking = toGoalRanking <$> many1 letter <* skipMany (char ' ')

       toGoalRanking = if diff then stringToGoalRankingDiff True else stringToGoalRanking True

-- Default heuristic
selectedPreSort :: Bool -> Parser (GoalRanking ProofContext)
selectedPreSort diff = do
    _ <- symbol "presort"
    _ <- colon
    presort <- goalRankingPresort diff <* lexeme spaces 
    return $ presort

--Function name (remplaced by identifier)
--functionName :: Parser String
--functionName = many space *> many (alphaNum <|> oneOf "[]_-@")

--Function value
functionValue :: Parser String
functionValue = many $ noneOf "\"" --interdit de mettre des " dans les regex, dommage


--Fonction (fonction, pretty printing)
function :: Parser ((AnnotatedGoal, ProofContext, System) -> Bool, String)
function = do
    f <- identifier
    paramGoal <- doubleQuoted functionValue
    --Need to add something for the space?
    paramCtxt <- doubleQuoted functionValue
    paramSys <- doubleQuoted functionValue
    return $ (nameToFunction (f,paramGoal,paramCtxt,paramSys),f++" \""++paramGoal++"\""++" \""++paramCtxt++"\""++" \""++paramSys++"\"")

functionNot :: ((AnnotatedGoal, ProofContext, System) -> Bool, String) -> ((AnnotatedGoal, ProofContext, System) -> Bool, String)
functionNot (f,s) = (not . f, "not "++s)

functionAnd :: ((AnnotatedGoal, ProofContext, System) -> Bool, String) -> ((AnnotatedGoal, ProofContext, System) -> Bool, String) -> ((AnnotatedGoal, ProofContext, System) -> Bool, String)
functionAnd (f,s1) (g,s2) = ((\x -> and [f x, g x]),s1++" & "++s2)

functionOr :: ((AnnotatedGoal, ProofContext, System) -> Bool, String) -> ((AnnotatedGoal, ProofContext, System) -> Bool, String) -> ((AnnotatedGoal, ProofContext, System) -> Bool, String)
functionOr (f,s1) (g,s2) = ((\x -> or [f x, g x]),s1++" | "++s2)

-- | Parse a negation.
negation :: Parser ((AnnotatedGoal, ProofContext, System) -> Bool, String)
negation = opLNot *> (functionNot <$> function) <|> function

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser ((AnnotatedGoal, ProofContext, System) -> Bool, String)
conjuncts = chainl1 negation (functionAnd <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser ((AnnotatedGoal, ProofContext, System) -> Bool, String)
disjuncts = try $ (chainl1 conjuncts (functionOr <$ opLOr)) -- error here is not triggered when empty prio (appends higher -> function parsing)

--Parsing prio
prio :: Parser (Prio ProofContext)
prio = do
    _ <- symbol "prio"
    _ <- colon
    fs <- many1 disjuncts
    return $ Prio (map fst fs) (map snd fs)

--Parsing deprio
deprio :: Parser (Deprio ProofContext)
deprio = do
    _ <- symbol "deprio"
    _ <- colon
    fs <- many1 disjuncts
    return $ Deprio (map fst fs) (map snd fs)


tactic :: Bool -> Parser (TacticI ProofContext)
tactic diff = do
    tName <- tacticName
    presort <- option (SmartRanking False) (selectedPreSort diff)
    prios <- option [] $ many1 prio
    deprios <- option [] $ many1 deprio
    return $ TacticI tName presort prios deprios

tacticFunctions :: M.Map String (String -> String -> String -> (AnnotatedGoal, ProofContext, System) -> Bool)
tacticFunctions = M.fromList
                      [ ("regex", regex')
                      , ("sysParamRegex", sysParamRegex)
                      , ("isFactName", isFactName)
                      , ("isInFactTerms", isInFactTerms)
                      ]
  where
    regex' :: String -> String -> String -> (AnnotatedGoal, ProofContext,  System) -> Bool
    regex' regex _ _ (agoal,_,_) = pg =~ regex
        where
            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pg = concat . lines . render $ pgoal agoal

    sysParamRegex :: String -> String -> String -> (AnnotatedGoal, ProofContext,  System) -> Bool
    sysParamRegex pGoal pSys pSys2 (goal,_,sys) =  or $ map (applyRegexBool pg) patterns
        where 
            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pg = concat . lines . render $ pgoal goal

            pformulas = map prettyGuarded $ S.toList $ L.get sFormulas sys
            formulas = render $ pformulas
            testFormula = map ((flip applyRegexBool) pSys2) formulas --tab of Bool
            conformingFormulas = snd $ unzip $ filter (\(x,y) -> x==True) $ zip testFormula formulas

            patterns = map (=~ pSys2) conformingFormulas :: [String] --si ne passe pas, fonction aux
            --surtout que je vais avoir besoin d'ajouter ~n à la liste pour les safenonces

            applyRegexBool :: String -> String -> Bool
            applyRegexBool s reg = s =~ reg

    isFactName :: String -> String -> String -> (AnnotatedGoal, ProofContext,  System) -> Bool
    isFactName s _ _ (((PremiseG _ Fact {factTag = ProtoFact Linear test _, factAnnotations = _ , factTerms = _ }), (_,_)), _, _ ) = test == s
    -- Not necessarily usefull line
    isFactName s _ _ ((ActionG _ (Fact { factTag = test ,factAnnotations =  _ , factTerms = _ }), _ ), _, _ ) = show test == s
    isFactName _ _ _ (_,_,_) = False

    isInFactTerms :: String -> String -> String -> (AnnotatedGoal, ProofContext,  System) -> Bool
    isInFactTerms s _ _ ((ActionG _ (Fact { factTag = _ ,factAnnotations =  _ , factTerms = [test]}), _ ), _, _ ) = show test =~ s
    isInFactTerms _ _ _ (_, _, _) = False

nameToFunction :: (String, String, String, String) -> (AnnotatedGoal, ProofContext, System) -> Bool
nameToFunction (s,paramGoal,paramCtxt,paramSys) = case M.lookup s tacticFunctions of
  Just f  -> f paramGoal paramCtxt paramSys
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
