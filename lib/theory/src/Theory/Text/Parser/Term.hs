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
    , natLit
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
import           Text.Parsec                --hiding ((<|>))
import           Term.Substitution
import           Theory
import           Theory.Text.Parser.Token


-- | Parse an lit with logical variables.
llit :: Parser LNTerm
llit = asum [freshTerm <$> freshName, pubTerm <$> pubName, natTerm <$> natName, varTerm <$> msgvar]

natLit :: Parser LNTerm
natLit = natTerm <$> natName

-- | Parse an lit with logical variables without public names in single constants.
llitNoPub :: Parser LNTerm
llitNoPub = asum [freshTerm <$> freshName, varTerm <$> msgvar]

-- | Lookup the arity of a non-ac symbol. Fails with a sensible error message
-- if the operator is not known.
lookupArity :: String -> Parser (Int, Privacy)
lookupArity op = do
    maudeSig <- sig <$> getState
    case lookup (BC.pack op) (S.toList (noEqFunSyms $ maudeSig) ++ [(emapSymString, (2,Public))]) of
        Nothing    -> fail $ "unknown operator `" ++ op ++ "'"
        Just (k,priv) -> return (k,priv)

-- | Parse an n-ary operator application for arbitrary n.
naryOpApp :: Bool -> Parser LNTerm -> Parser LNTerm
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
binaryAlgApp :: Bool -> Parser LNTerm -> Parser LNTerm
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

diffOp :: Bool -> Parser LNTerm -> Parser LNTerm
diffOp eqn plit = do
  ts <- symbol "diff" *> parens (commaSep (msetterm eqn plit))
  when (2 /= length ts) $ fail
    "the diff operator requires exactly 2 arguments"
  diff <- enableDiff . sig <$> getState
  when eqn $ fail
    "diff operator not allowed in equations"
  unless diff $ fail
    "diff operator found, but flag diff not set"
  let arg1 = head ts
  let arg2 = head (tail ts)
  return $ fAppDiff (arg1, arg2)

-- | Parse a term.
term :: Parser LNTerm -> Bool -> Parser LNTerm
term plit eqn = asum
    [ pairing       <?> "pairs"
    , parens (msetterm eqn plit)
    , symbol "1:nat"      *> pure fAppNatOne
    , symbol "%1"         *> pure fAppNatOne
    , symbol "1"          *> pure fAppOne
    , symbol "DH_neutral" *> pure fAppDHNeutral
    , application        <?> "function application"
    , nullaryApp
    , plit
    ]
    <?> "term"
  where
    application = asum $ map (try . ($ plit)) [naryOpApp eqn, binaryAlgApp eqn, diffOp eqn]
    pairing = angled (tupleterm eqn plit)
    nullaryApp = do
      maudeSig <- sig <$> getState
      -- FIXME: This try should not be necessary.
      asum [ try (symbol (BC.unpack sym)) *> pure (fApp (NoEq (sym,(0,priv))) [])
           | NoEq (sym,(0,priv)) <- S.toList $ funSyms $ maudeSig ]

-- | A left-associative sequence of exponentations.
expterm :: Bool -> Parser LNTerm -> Parser LNTerm
expterm eqn plit = chainl1 (term plit eqn) (curry fAppExp <$ opExp)

-- | A left-associative sequence of multiplications.
multterm :: Bool -> Parser LNTerm -> Parser LNTerm
multterm eqn plit = do
    dh <- enableDH . sig  <$> getState
    if dh && not eqn -- if DH is not enabled, do not accept 'multterm's and 'expterm's
        then chainl1 (expterm eqn plit) ((\a b -> fAppAC Mult [a,b]) <$ opMult)
        else term plit eqn

-- | A left-associative sequence of xors.
xorterm :: Bool -> Parser LNTerm -> Parser LNTerm
xorterm eqn plit = do
    xor <- enableXor . sig <$> getState
    if xor && not eqn-- if xor is not enabled, do not accept 'xorterms's
        then chainl1 (multterm eqn plit) ((\a b -> fAppAC Xor [a,b]) <$ opXor)
        else multterm eqn plit

-- | A left-associative sequence of multiset unions.
msetterm :: Bool -> Parser LNTerm -> Parser LNTerm
msetterm eqn plit = do
    mset <- enableMSet . sig <$> getState
    if mset && not eqn-- if multiset is not enabled, do not accept 'msetterms's
        then chainl1 (natterm eqn plit) ((\a b -> fAppAC Union [a,b]) <$ opUnion)
        else natterm eqn plit

-- | A left-associative sequence of terms on natural numbers.
natterm :: Bool -> Parser LNTerm -> Parser LNTerm
natterm eqn plit = do
    nats <- enableNat . sig <$> getState
    if nats -- if nat is not enabled, do not accept 'natterms's
        then try (xorterm eqn plit) <|> sumterm  --TODO-UNCERTAIN: not sure whether the order (mset-nat-xor-mult) matters (Cedric's was nat-mult-mset)
        else xorterm eqn plit
  where
    sumterm = chainl1 subNatTerm ((\a b -> fAppAC NatPlus [a,b]) <$ opPlus)

    subNatTerm = try $ asum
      [ parens sumterm
      , symbol "1:nat" *> pure fAppNatOne
      , symbol "%1"    *> pure fAppNatOne
      , symbol "1"     *> pure fAppNatOne  -- if we expect a nat, we take 1 as nat instead of diffie-hellman
      , natLlit
      ]

    natLlit = varTerm <$> asum
      [ try $ sortedLVar [LSortNat]
      , do (n, i) <- indexedIdentifier
           return $ LVar n LSortNat i ]


-- | A right-associative sequence of tuples.
tupleterm :: Bool -> Parser LNTerm -> Parser LNTerm
tupleterm eqn plit = chainr1 (msetterm eqn plit) (curry fAppPair <$ comma)
