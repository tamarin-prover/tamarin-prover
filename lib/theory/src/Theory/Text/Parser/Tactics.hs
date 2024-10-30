-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
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
import qualified Data.Set                   as S
import           Data.List

import           Theory
import           Theory.Constraint.Solver.AnnotatedGoals
--import           Theory.Constraint.Solver.Heuristics
--import           Theory.Constraint.System.Guarded
import           Theory.Text.Pretty         hiding (char,colon,symbol,opLAnd,opLOr, space)
import           Theory.Text.Parser.Token
--import           Theory.Text.Parser.Signature

import           Text.Parsec                hiding ((<|>))
import           Text.Regex.PCRE


--Tactic
tacticName :: Parser String
tacticName = do
    _ <- symbol "tactic"
    _ <- colon
    tName <- identifier
    return tName

goalRankingPresort :: Bool -> Parser (GoalRanking ProofContext)
goalRankingPresort diff = regularRanking <?> "proof method ranking"
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


--Function value
functionValue :: Parser String
functionValue = many $ noneOf "\"" --forbid using " char in parameter 


--Fonction (fonction, pretty printing)
function :: Parser ((AnnotatedGoal, ProofContext, System) -> Bool, String)
function = do
    f <- identifier
    param <- many1 $ doubleQuoted functionValue
    return $ (nameToFunction (f,param), f++" \""++intercalate "\" \"" param++"\"")

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
disjuncts = try $ (chainl1 conjuncts (functionOr <$ opLOr))

--Parsing prio
prio :: Parser (Prio ProofContext)
prio = do
    ranking <- symbol "prio" *> colon *> option "id" (braced identifier) -- if none use default ranking
    -- _ <- newline
    fs <- many1 disjuncts --
    return $ Prio (nameToRanking ranking) ranking (map fst fs) (map snd fs) 

--Parsing deprio
deprio :: Parser (Deprio ProofContext)
deprio = do
    ranking <- symbol "deprio" *> colon *> option "id" (braced identifier)
    fs <- many1 disjuncts
    return $ Deprio (nameToRanking ranking) ranking (map fst fs) (map snd fs)


tactic :: Bool -> Parser (Tactic ProofContext)
tactic diff = do
    tName <- tacticName
    presort <- option (SmartRanking diff) (selectedPreSort diff)
    prios <- option [] $ many1 prio
    deprios <- option [] $ many1 deprio
    return $ Tactic tName presort prios deprios

tacticFunctions :: M.Map String ([String] -> (AnnotatedGoal, ProofContext, System) -> Bool)
tacticFunctions = M.fromList
                      [ ("regex", regex')
                      , ("isFactName", isFactName)
                      , ("isInFactTerms", isInFactTerms)
                      , ("dhreNoise", dhreNoise)
                      , ("defaultNoise", defaultNoise)
                      , ("reasonableNoncesNoise",reasonableNoncesNoise)
                      , ("nonAbsurdConstraint", nonAbsurdConstraint)
                      ]
  where
    regex' :: [String] -> (AnnotatedGoal, ProofContext,  System) -> Bool
    regex' l (agoal,_,_) = case l of 
        (regex:_) -> pg =~ regex
        _     -> False
        where
            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pg = concat . lines . render $ pgoal agoal

    nonAbsurdConstraint :: [String] -> (AnnotatedGoal, ProofContext,  System) -> Bool
    nonAbsurdConstraint param (goal,_,sys) = hasSafeNonces && isSubset
        where
            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pg = concat . lines . render $ pgoal goal

            functionsDetection = "[^A-Za-z0-9][A-Za-z0-9]+\\("
            functions = retrieveFun pg
            isSubset = and $ map ((flip elem) ["Ku","inv"]) functions

            retrieveFun :: String -> [String]
            retrieveFun pgoal_ = map init $ map tail $ getAllTextMatches $ pgoal_ =~ functionsDetection

            safenoncePattern = "(~n|" ++ intercalate "|" (map show $ concat (map (checkFormula $ head param) (S.toList $ L.get sFormulas sys)))++")(?![.0-9a-zA-Z])"
            hasSafeNonces = not (pg =~ safenoncePattern)

    dhreNoise :: [String] -> (AnnotatedGoal, ProofContext,  System) -> Bool
    dhreNoise param (goal,_,sys) = pg =~ goalPattern
        where 
            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pg = concat . lines . render $ pgoal goal

            oracleType = head param
            sysPatternDiff = "(~[a-zA-Z0-9.]*)"
            sysPattern = if oracleType == "curve" then "(~n|" ++ intercalate "|" (map show $ concat (map (checkFormula oracleType) (S.toList $ L.get sFormulas sys)))++")(?![.0-9a-zA-Z])" else "(~n|" ++ intercalate "|" (map show $ concat (map (checkFormula oracleType) (S.toList $ L.get sFormulas sys)))++")"-- ++ head t (fst param f)
            goalPattern = if oracleType == "diff" then ".*(\\(("++sysPatternDiff++"\\*)+"++sysPatternDiff++"\\)|inv\\("++sysPatternDiff++"\\))" else ".*(\\(("++sysPattern++"\\*)+"++sysPattern++"\\)|inv\\("++sysPattern++"\\))"

    defaultNoise :: [String] -> (AnnotatedGoal, ProofContext,  System) -> Bool
    defaultNoise param (goal,_,sys) = or $ map ((flip elem) sysPattern) goalMatches
        where 
            paramGoal = head param
            oracleType = head $ tail param

            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pg = concat . lines . render $ pgoal goal
            goalMatches = getAllTextMatches $ pg =~ paramGoal -- "\\(?<!'g'^\\)~[a-zA-Z.0-9]*"

            sysPattern = map show $ concat (map (checkFormula oracleType) (S.toList $ L.get sFormulas sys))

    reasonableNoncesNoise :: [String] -> (AnnotatedGoal, ProofContext,  System) -> Bool
    reasonableNoncesNoise param (goal,_,sys) = or $ map ((flip elem) sysPattern) nonces
        where
            oracleType = head param

            nonces = map show (getFactTerms_ goal)

            -- reasonableNonces is designed to mimic reasonable_nonces from oracle.py of Vacarme,
            -- therefore it is meant to be used with regex "!KU\( *~.*\)", limiting the type of possible goals
            getFactTerms_ :: AnnotatedGoal -> [LNTerm]
            getFactTerms_ (ActionG _ (Fact { factTag = _ ,factAnnotations =  _ , factTerms = ft }), _ ) = ft
            getFactTerms_ _ = []

            sysPattern = "~n":(map show $ concat (map (checkFormula oracleType) (S.toList $ L.get sFormulas sys)))

    checkFormula :: String -> LNGuarded -> [LVar]
    checkFormula oracleType f = if rev && expG then concat $ getFormulaTermsCore f else []

        where
          getCore (Free v) = v
          getCore _ = error "It should really not happend"

          rev = or $ map matchReveal (map factTagName $ guardFactTags f)
          expG = if oracleType == "curve" then show (getFormulaTerms f) =~ "grpid,exp\\('g'" else show (getFormulaTerms f) =~ "exp\\('g'"

          matchReveal :: String -> Bool
          matchReveal s = s =~ "Reveal"

          getFormulaTerms :: LNGuarded -> [VTerm Name (BVar LVar)]
          getFormulaTerms (GGuarded _ _ [Action _ fa] _ ) = getFactTerms fa
          getFormulaTerms _ = []

          getFormulaTermsCore :: LNGuarded -> [[LVar]]
          getFormulaTermsCore (GGuarded _ _ [Action _ fa] _ ) = map (map getCore) (map varsVTerm (getFactTerms fa))
          getFormulaTermsCore _ = []


    isFactName :: [String] -> (AnnotatedGoal, ProofContext,  System) -> Bool
    isFactName (s:_) (((PremiseG _ Fact {factTag = ProtoFact Linear test _, factAnnotations = _ , factTerms = _ }), (_,_)), _, _ ) = test == s
    -- Not necessarily usefull line
    isFactName (s:_) ((ActionG _ (Fact { factTag = test ,factAnnotations =  _ , factTerms = _ }), _ ), _, _ ) = show test == s
    isFactName _ (_,_,_) = False

    isInFactTerms :: [String] -> (AnnotatedGoal, ProofContext,  System) -> Bool
    isInFactTerms (s:_) ((ActionG _ (Fact { factTag = _ ,factAnnotations =  _ , factTerms = [test]}), _ ), _, _ ) = show test =~ s
    isInFactTerms _ (_, _, _) = False

nameToFunction :: (String,[String]) -> (AnnotatedGoal, ProofContext, System) -> Bool
nameToFunction (s,param) = case M.lookup s tacticFunctions of
  Just f  -> f param
  Nothing ->  error $ "\nThe function "++ s
            ++" is not defined.\nUse one of the following:\n"++listTacticFunction

  where
    tacticFunctionName :: String -> String
    tacticFunctionName funct = case funct of
            "regex"                 -> "match between the pretty printed proof method and the given regex"
            "isFactName"            -> "match against the fact name"
            "isInFactTerms"         -> "match against the fact terms"
            "nonAbsurdConstraint"   -> "match non absurd constraints (vacarme oracle)"
            "dhreNoise"             -> "match diffie-hellman (vacarme oracle)"
            "defaultNoise"          -> "match default facts (vacarme oracle)"
            "reasonableNoncesNoise" -> "match reasonable noncesNoise (vacarme oracle)"
            _                       -> ""

    listTacticFunction:: String
    listTacticFunction = M.foldMapWithKey
        (\k _ -> "'"++k++"': " ++ tacticFunctionName k ++ "\n") tacticFunctions

rankingFunctions :: M.Map String ([AnnotatedGoal] -> [AnnotatedGoal])
rankingFunctions = M.fromList
                      [   ("smallest", smallest)
                        , ("id", idRanking)
                        , ("", idRanking)
                      ]
  where

    idRanking :: [AnnotatedGoal] -> [AnnotatedGoal]
    idRanking l = l

    smallest :: [AnnotatedGoal] -> [AnnotatedGoal]
    smallest agoalList = res
        where
            pgoal (g,(_nr,_usefulness)) = prettyGoal g
            pgList = map (concat . lines . render . pgoal) agoalList
            dblList = zip pgList agoalList

            tplList = map (\(x,y) -> (length x,(x,y))) dblList
            sortedTps = sortOn fst tplList
            res = snd $ unzip (snd $ unzip sortedTps)

nameToRanking :: String -> Maybe ([AnnotatedGoal] -> [AnnotatedGoal])
nameToRanking s = case M.lookup s rankingFunctions of
  Just f  -> Just f
  Nothing ->  error $ "\nThe function "++ s
           ++" is not defined.\nUse one of the following:\n"++listRankingFunction

  where
    rankingFunctionName :: String -> String
    rankingFunctionName funct = case funct of
            "smallest"         -> "return the smallest string first (pretty printing)"
            _                  -> ""

    listRankingFunction:: String
    listRankingFunction = M.foldMapWithKey
        (\k _ -> "'"++k++"': " ++ rankingFunctionName k ++ "\n") rankingFunctions