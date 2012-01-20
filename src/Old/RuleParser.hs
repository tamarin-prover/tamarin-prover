{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module RuleParser where

import ApplicativeParsec
import Term hiding ( Rule )
import TermPPP
import SymbolicDerivationGraph
import Utils

-- ***************************************************************************
-- Parser for facts and rules
-- ***************************************************************************

readRulesFiles :: [FilePath] -> IO ([Rule], RuleSet)
readRulesFiles fnames = do
  contents <- mapM readFile fnames
  let rules = parseAll pRules (concat contents)
  return ([ r | (Goal,r) <- rules],
          RS {forwardRules = [r | (Forward,r) <- rules],
              backwardRules = [r | (Backward,r) <- rules],
              stepRules = [r | (Step,r) <- rules],
              threadRules = [r | (Thread,r) <- rules],
              ikRules = [r | (IK,r) <- rules]})

pFact :: GenParser Char () Fact
pFact = pP <|> pKV <|> pSV <|> pK <|> pS <|> pEq <|> pEqV <|> pDisj
 where pDisj = do
         string "OR"
         char '('
         fs <- sepBy pFact (char ',')
         char ')'
         return (Disj fs)
       pP = do
         string "P["
         rname <- many1 (noneOf ",")
         char ','
         stepnum <- many1 digit
         string "]("
         ts <- sepBy TermPPP.expr (char ',')
         char ')'
         return (P rname (read stepnum) (map N ts))
       pK = do
         try (string "K%(")
         t <- TermPPP.expr
         char ')'
         return (K (T t))
       pKV = do -- variant
         try (string "K(")
         t <- TermPPP.expr
         char ')'
         return (K (N t))
       pSV = do
         try (string "S(")
         t <- TermPPP.expr
         char ')'
         return (S (N t))
       pS = do
         try (string "S%(")
         t <- TermPPP.expr
         char ')'
         return (S (T t))
       pEq = do
         try (string "EQ(")
         t1 <- TermPPP.expr
         char ','
         t2 <- TermPPP.expr
         char ')'
         return (Eq (N t1) (N t2))
       pEqV = do
         try (string "EQ%(")
         t1 <- TermPPP.expr
         char ','
         t2 <- TermPPP.expr
         char ')'
         return (Eq (T t1) (T t2))

pRule :: GenParser Char () Rule
pRule = do
  rname <- many1 (noneOf ":")
  string ":"
  spaces
  char '['
  assms <- sepBy pFact (char ',')
  char ']'
  spaces
  string "-["
  evars0 <- sepBy TermPPP.expr (char ',')
  string "]->"
  spaces
  char '['
  concs <- sepBy pFact (char ',')
  char ']'

  let evars = [EVar x | Atom (Var x) <- evars0]
  if length evars /= length evars0 then
    error "can only specify existential variables, not terms"
    else return (Rule rname assms evars concs)


pRuleType :: GenParser Char st RuleType
pRuleType =
      string "forward:" *> return Forward
  <|> string "backward:" *> return Backward
  <|> string "goal:" *> return Goal
  <|> string "step:" *> return Step
  <|> string "thread:" *> return Thread
  <|> string "ik:" *> return IK

pRules :: GenParser Char () [(RuleType, Rule)]
pRules = go Nothing
 where
  go :: (Maybe RuleType) -> GenParser Char () [(RuleType,Rule)]
  go Nothing =
   eol *> go Nothing -- skip empty lines
   <|>
   char '#' *> (many (noneOf "\n") *> eol) *> go Nothing
   <|>
   (do rt <- pRuleType <* eol
       go (Just rt))
  go (Just rt) =
   eol *> go (Just rt) -- skip empty lines
   <|>
   char '#' *> (many (noneOf "\n") *> eol) *> go (Just rt)
   <|>
   eof *> return []
   <|>
    (do rtype <- try (pRuleType) <* eol
        go (Just rtype))
   <|>
    (do r <- pRule <* eol
        res <- go (Just rt)
        return $ (rt,r):res)
      

data RuleType = Goal | Forward | Backward | Step | Thread |IK
 deriving (Show,Eq,Ord)

-- TODO: implement check that all rules are well-formed
validateRules :: [Rule] -> RuleSet -> Bool
validateRules _goals _ruleSet = True
