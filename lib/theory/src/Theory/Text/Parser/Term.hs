-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing Terms

module Theory.Text.Parser.Term (
    msetterm
    , llit
    , term
    , llitNoPub
)
where

import           Prelude                    hiding (id, (.))
import qualified Data.ByteString.Char8      as BC
import           Data.Foldable              (asum)
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           Control.Category
import           Control.Monad
import           Text.Parsec                hiding ((<|>))
import           Term.Substitution
import           Theory
import           Theory.Text.Parser.Token


-- | Parse an lit with logical variables.
llit :: Parser LNTerm
llit = asum [freshTerm <$> freshName, pubTerm <$> pubName, varTerm <$> msgvar]

-- | Parse an lit with logical variables without public names in single constants.
llitNoPub :: Parser LNTerm
llitNoPub = asum [freshTerm <$> freshName, varTerm <$> msgvar]

-- | Lookup the arity of a non-ac symbol. Fails with a sensible error message
-- if the operator is not known.
lookupArity :: String -> Parser (Int, Privacy)
lookupArity op = do
    maudeSig <- getState
    case lookup (BC.pack op) (S.toList (noEqFunSyms maudeSig) ++ [(emapSymString, (2,Public))]) of
        Nothing    -> fail $ "unknown operator `" ++ op ++ "'"
        Just (k,priv) -> return (k,priv)

-- | Parse an n-ary operator application for arbitrary n.
naryOpApp :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
naryOpApp eqn plit = do
    op <- identifier
    --traceM $ show op ++ " " ++ show eqn
    when (eqn && op `elem` ["mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor"])
      $ error $ "`" ++ show op ++ "` is a reserved function name for builtins."
    (k,priv) <- lookupArity op
    ts <- parens $ if k == 1
                     then return <$> tupleterm eqn plit
                     else commaSep (msetterm eqn plit)
    let k' = length ts
    when (k /= k') $
        fail $ "operator `" ++ op ++"' has arity " ++ show k ++
               ", but here it is used with arity " ++ show k'
    let app o = if BC.pack op == emapSymString then fAppC EMap else fAppNoEq o
    return $ app (BC.pack op, (k,priv)) ts

-- | Parse a binary operator written as @op{arg1}arg2@.
binaryAlgApp :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
binaryAlgApp eqn plit = do
    op <- identifier
    when (eqn && op `elem` ["mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor"])
      $ error $ "`" ++ show op ++ "` is a reserved function name for builtins."
    (k,priv) <- lookupArity op
    arg1 <- braced (tupleterm eqn plit)
    arg2 <- term plit eqn
    when (k /= 2) $ fail
      "only operators of arity 2 can be written using the `op{t1}t2' notation"
    return $ fAppNoEq (BC.pack op, (2,priv)) [arg1, arg2]

diffOp :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
diffOp eqn plit = do
  ts <- symbol "diff" *> parens (commaSep (msetterm eqn plit))
  when (2 /= length ts) $ fail
    "the diff operator requires exactly 2 arguments"
  diff <- enableDiff <$> getState
  when eqn $ fail
    "diff operator not allowed in equations"
  unless diff $ fail
    "diff operator found, but flag diff not set"
  let arg1 = head ts
  let arg2 = head (tail ts)
  return $ fAppDiff (arg1, arg2)

-- | Parse a term.
term :: Ord l => Parser (Term l) -> Bool -> Parser (Term l)
term plit eqn = asum
    [ pairing       <?> "pairs"
    , parens (msetterm eqn plit)
    , symbol "1" *> pure fAppOne
    , application <?> "function application"
    , nullaryApp
    , plit
    ]
    <?> "term"
  where
    application = asum $ map (try . ($ plit)) [naryOpApp eqn, binaryAlgApp eqn, diffOp eqn]
    pairing = angled (tupleterm eqn plit)
    nullaryApp = do
      maudeSig <- getState
      -- FIXME: This try should not be necessary.
      asum [ try (symbol (BC.unpack sym)) *> pure (fApp (NoEq (sym,(0,priv))) [])
           | NoEq (sym,(0,priv)) <- S.toList $ funSyms maudeSig ]

-- | A left-associative sequence of exponentations.
expterm :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
expterm eqn plit = chainl1 (term plit eqn) (curry fAppExp <$ opExp)

-- | A left-associative sequence of multiplications.
multterm :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
multterm eqn plit = do
    dh <- enableDH <$> getState
    if dh && not eqn -- if DH is not enabled, do not accept 'multterm's and 'expterm's
        then chainl1 (expterm eqn plit) ((\a b -> fAppAC Mult [a,b]) <$ opMult)
        else term plit eqn

-- | A left-associative sequence of xors.
xorterm :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
xorterm eqn plit = do
    xor <- enableXor <$> getState
    if xor && not eqn-- if xor is not enabled, do not accept 'xorterms's
        then chainl1 (multterm eqn plit) ((\a b -> fAppAC Xor [a,b]) <$ opXor)
        else multterm eqn plit

-- | A left-associative sequence of multiset unions.
msetterm :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
msetterm eqn plit = do
    mset <- enableMSet <$> getState
    if mset && not eqn-- if multiset is not enabled, do not accept 'msetterms's
        then chainl1 (xorterm eqn plit) ((\a b -> fAppAC Union [a,b]) <$ opPlus)
        else xorterm eqn plit

-- | A right-associative sequence of tuples.
tupleterm :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
tupleterm eqn plit = chainr1 (msetterm eqn plit) (curry fAppPair <$ comma)
