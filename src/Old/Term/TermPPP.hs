{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Term.TermPPP
where
  
import Utils.ApplicativeParsec
import Text.ParserCombinators.Parsec.Expr
import Term.Term
import Utils.Misc
import Term.Substitution
import Term.Maude.Substitution
  
expr :: Parser MTerm
expr = buildExpressionParser ptable factor <?> "expression"

ptable :: [[ Operator Char st MTerm ]]
ptable = [ [ op "*" (Mult) AssocLeft ],
           [ op "^" (Exp) AssocLeft ] ]
  where
    op s f assoc = Infix (f <$ string s) assoc

factor :: GenParser Char () MTerm 
factor = char '(' *> expr <* char ')'
   <|> variable
   <|> constant
--   <|> binop1
--   <|> binop2
   <|> inverse
   <|> pone
   <|> pmsg
   <?> "simple expression"

pmsg :: Parser MTerm
pmsg =  pOp1 <|> pOp2
 where preBinop1 s c = do
         try (string (s++"("))
         e <- factor
         char ')'
         return (Op1 c e)
       preBinop2 s c = do
         try (string (s++"("))
         e1 <- factor
         char ','
         e2 <- factor
         char ')'
         return (Op2 c e1  e2)
       pOp1 = foldr (\(t,s) p -> p <|> preBinop1 s t) pzero [(o, show o) | o <- [toEnum 0 ..]]
       pOp2 = foldr (\(t,s) p -> p <|> preBinop2 s t) pzero [(o, show o) | o <- [toEnum 0 ..]]

pone :: Parser MTerm
pone = Unit <$ char '1' <?> "one"

variable :: Parser MTerm 
variable = Lit . Var <$> (char 'x' *> pNat) <?> "var"

constant :: Parser MTerm
constant = Lit . Name <$> (try (char 'a' *> pNat))
        <?> "const"

--binop1 :: GenParser Char () MTerm 
--binop1 = Op1 <$> (try (string "op1_") *> pNat <* char '(') <*> (factor <* char ')')
--      <?> "binop1"

inverse :: GenParser Char () MTerm 
inverse = Inv <$> (string "~" *> factor) <?> "inv"

--binop2 :: GenParser Char () MTerm 
--binop2 = Op2 <$> (try (string "op2_") *> pNat <* char '(') <*> (factor <* char ',') <*> (factor <* char ')')
--       <?> "binop2"

parseTerm :: String -> MTerm
parseTerm s = parseAll expr s

parseSubst :: String -> MSubst
parseSubst s = parseAll psubst s

psubst :: GenParser Char () MSubst
psubst = do
  char '{'
  s <- substEntry `sepBy` char ','
  char '}'
  return $ substFromListS "parsed" s

substEntry :: GenParser Char () (Int,MTerm)
substEntry = do
  e <- expr
  char '/'
  Lit (Var v) <- variable
  return (v,e)

t1_subst :: String
t1_subst = "{x10*~(x4*fst(pair(x5,verify(x7,x6))))*x8/x1,x5*x11*~(x12*x8)/x2}"
tpp_t1 :: Bool
tpp_t1 = (show $ parseSubst t1_subst) == t1_subst