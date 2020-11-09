{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts          #-}


{-# LANGUAGE PatternGuards          #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing protocol theories. See the MANUAL for a high-level description of
-- the syntax.
module Theory.Text.Parser (
    parseOpenTheory
  , parseOpenTheoryString
  , parseOpenDiffTheory
  , parseOpenDiffTheoryString
  , parseLemma
  , parseRestriction
  , parseIntruderRules
  , newVariables
  , liftedAddProtoRule
  , liftedAddRestriction
  ) where

import           Prelude                    hiding (id, (.))

import qualified Data.ByteString            as B
import qualified Data.ByteString.Char8      as BC
import           Data.Char                  (isUpper, toUpper)
import           Data.Foldable              (asum)
import           Data.Label
import           Data.Either
import qualified Data.Map                   as M
import           Data.Maybe  --TODO-UNCERTAIN test if it can be removed
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
-- import           Data.List                  (foldl1')  --TODO-UNCERTAIN test if it can be removed
import qualified Data.Text                  as T
import qualified Data.Text.Encoding         as TE
import           Data.Color

import           Control.Applicative        hiding (empty, many, optional)
import           Control.Category
import           Control.Monad
import qualified Control.Monad.Fail         as Fail
import qualified Control.Monad.Catch        as Catch

import           Text.Parsec                hiding ((<|>))
import           Text.PrettyPrint.Class     (render)

-- import           System.Process

-- import qualified Extension.Data.Label       as L

import           Term.Substitution
import           Term.SubtermRule
import           Term.Maude.Signature  --TODO-UNCERTAIN test if it can be removed
import           Theory
import           Theory.Sapic
import           Theory.Text.Parser.Token

import           Debug.Trace

import           Data.Functor.Identity

------------------------------------------------------------------------------
-- ParseRestriction datatype and functions to parse diff restrictions
------------------------------------------------------------------------------

-- | A restriction describes a property that must hold for all traces.
-- | Restrictions are always used as lemmas in proofs.
data ParseRestriction = ParseRestriction
       { pRstrName       :: String
       , pRstrAttributes :: [RestrictionAttribute]
       , pRstrFormula    :: LNFormula
       }
       deriving( Eq, Ord, Show )


-- | True iff the restriction is a LHS restriction.
isLeftRestriction :: ParseRestriction -> Bool
isLeftRestriction rstr =
     LHSRestriction `elem` pRstrAttributes rstr

-- | True iff the restriction is a RHS restriction.
isRightRestriction :: ParseRestriction -> Bool
isRightRestriction rstr =
     RHSRestriction `elem` pRstrAttributes rstr

-- -- | True iff the restriction is a Both restriction.
-- isBothRestriction :: ParseRestriction -> Bool
-- isBothRestriction rstr =
--      (BothRestriction `elem` pRstrAttributes rstr)

-- | Converts ParseRestrictions to Restrictions
toRestriction :: ParseRestriction -> Restriction
toRestriction rstr = Restriction (pRstrName rstr) (pRstrFormula rstr)

------------------------------------------------------------------------------
-- Lexing and parsing theory files and proof methods
------------------------------------------------------------------------------

-- | Parse a security protocol theory file.
parseOpenTheory :: [String] -- ^ Defined flags
                -> FilePath
                -> IO OpenTheory
parseOpenTheory flags file = parseFile (theory flags) file  --do
                               --thy <- parseFile (theory flags) file
                               --putStrLn $ render (prettyOpenTheory thy)
                               --return thy
--TODO-UNDEBUG

-- | Parse a security protocol theory file.
parseOpenDiffTheory :: [String] -- ^ Defined flags
                -> FilePath
                -> IO OpenDiffTheory
parseOpenDiffTheory flags = parseFile (diffTheory flags)


-- | Parse DH intruder rules.
parseIntruderRules
    :: MaudeSig -> String -> B.ByteString -> Either ParseError [IntrRuleAC]
parseIntruderRules msig ctxtDesc =
    parseString ctxtDesc (setState msig >> many intrRule)
  . T.unpack . TE.decodeUtf8

-- | Parse a security protocol theory from a string.
parseOpenTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> Either ParseError OpenTheory
parseOpenTheoryString flags = parseString "<unknown source>" (theory flags)

-- | Parse a security protocol theory from a string.
parseOpenDiffTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> Either ParseError OpenDiffTheory
parseOpenDiffTheoryString flags = parseString "<unknown source>" (diffTheory flags)

-- | Parse a lemma for an open theory from a string.
parseLemma :: String -> Either ParseError (SyntacticLemma ProofSkeleton)
parseLemma = parseString "<unknown source>" lemma

-- | Parse a lemma for an open theory from a string.
parseRestriction :: String -> Either ParseError SyntacticRestriction
parseRestriction = parseString "<unknown source>" restriction

------------------------------------------------------------------------------
-- Parsing Terms
------------------------------------------------------------------------------

-- | Parse an lit with logical variables.
llit :: Parser LNTerm
llit = asum [freshTerm <$> freshName, pubTerm <$> pubName, natTerm <$> natName, varTerm <$> msgvar]

-- | Parse an lit with logical variables of the given sort.
sortedLlit :: LSort -> Parser LNTerm
sortedLlit s@(LSortUser _) =
    varTerm <$> asum
      [ try $ sortedLVar [s]
      , do (n, i) <- indexedIdentifier
           return $ LVar n s i ]
sortedLlit s@LSortNat =
    varTerm <$> asum
      [ try $ sortedLVar [s]
      , do (n, i) <- indexedIdentifier
           return $ LVar n s i ]
sortedLlit _ = llit

-- | Parse an lit with logical variables without public names in single constants.
llitNoPub :: Parser LNTerm
llitNoPub = asum [freshTerm <$> freshName, varTerm <$> msgvar]

-- | Lookup the arity of a non-ac symbol. Fails with a sensible error message
-- if the operator is not known.
lookupArity :: String -> Parser (Int, Privacy, Maybe [String])
lookupArity op = do
    maudeSig <- getState
    case lookup (BC.pack op) [ (noEqOp o, o) | o <- allSyms maudeSig ] of
        Nothing -> do
          fail $ "unknown operator `" ++ op ++ "'"
        Just (NoEqSym _ k priv sts) -> return (k,priv,sts)
  where
    allSyms maudeSig =
      S.toList (noEqFunSyms maudeSig)
      ++ [NoEqSym emapSymString 2 Public Nothing]
      ++ (catMaybes $ map mapACSym (S.toList $ userACSyms maudeSig))
    noEqOp (NoEqSym f _ _ _) = f
    --TODO-UNCERTAIN why do we add the user-defined AC-symbols (not the normal AC ones) despite the function description? Commit 09577fc
    mapACSym (UserAC f s) = Just (NoEqSym (BC.pack f) 2 Public (Just [s,s,s]))
    mapACSym _            = Nothing

-- | Parse an n-ary operator application for arbitrary n.
naryOpApp :: Bool -> Parser (LNTerm) -> Parser (LNTerm)
naryOpApp eqn plit = do
    op <- identifier
    --traceM $ show op ++ " " ++ show eqn
    when (eqn && op `elem` ["mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor"])
      $ error $ "`" ++ show op ++ "` is a reserved function name for builtins."
    (k,priv,sts) <- lookupArity op
    ts <- parens $ arguments op k sts
    -- Verify arity
    let k' = length ts
    when (k /= k' && k > 1) $ do
            let err = "operator `" ++ op ++"' has arity " ++ show k ++
                      ", but here it is used with arity " ++ show k'
            fail err
    let args  = if k' > k && k == 1
                  then [foldr1 (curry fAppPair) ts]
                  else ts
    let app o = if BC.pack op == emapSymString then fAppC EMap else fAppNoEq o
    msig <- getState
    return $ if op `elem` userACSyms' msig
      then lookupUserAC op (S.toList $ userACSyms msig) args
      else app (NoEqSym (BC.pack op) k priv sts) args
  where  --TODO-UNCERTAIN: did not double check the code in this where-block (might need to fix, see upper uncertainty)
    --TODO-UNCERTAIN: The main commits for this are: 8985fa4 -> 87076d7 -> 19a6b44
    -- Functions on built-in sorts
    arguments _  0 _       = return []
    arguments _  _ Nothing = commaSep (msetterm eqn plit)
    -- Functions on user-defined sorts (with type signature)
    arguments op _ (Just xs) =
      commaSepN $ map (sortedTerm op) (zip ([1..] :: [Integer]) $ init xs)

    lookupUserAC idn (sym@(UserAC idn' _):syms) as
      | idn == idn'              = fAppAC sym as
      | otherwise                = lookupUserAC idn syms as
    lookupUserAC idn (_:syms) as = lookupUserAC idn syms as
    lookupUserAC idn [] _ = error $
      "Theory.Text.naryOpApp: error parsing user AC symbol: " ++ idn

    -- Parse a term with the given sort
    sortedTerm op (idx, sortname) = do
      let sort = sortFromString sortname
      lnterm <- msetterm eqn $ asum [try $ sortedLlit sort, llit]
      let order = sortCompare (sortOfLNTerm lnterm) sort
      if order == (Just LT) || order == (Just EQ)
        then return lnterm
        -- XXX: Because of limitations in the way Parsec handles errors,  --TODO-UNCERTAIN removed this liftIO (and the one above)
        -- the error message from fail will not show up in the output which
        -- may be confusing to the user. We print an additional error message.
        else do
          pos <- getPosition
          let err = "Error: Function " ++ op ++ " expects argument of sort "
                    ++ sortname ++ " at position " ++ show idx ++
                    ", but found sort " ++ sortTypename (sortOfLNTerm lnterm)
                    ++ " instead! (line " ++ show (sourceLine pos) ++ ")."
          fail err

-- | Parse a binary operator written as @op{arg1}arg2@.
binaryAlgApp :: Bool -> Parser LNTerm -> Parser LNTerm
binaryAlgApp eqn plit = do
    op <- identifier
    when (eqn && op `elem` ["mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor"])
      $ error $ "`" ++ show op ++ "` is a reserved function name for builtins."
    (k,priv, sts) <- lookupArity op
    arg1 <- braced (tupleterm eqn plit)
    arg2 <- term plit eqn
    when (k /= 2) $ fail
      "only operators of arity 2 can be written using the `op{t1}t2' notation"
    return $ fAppNoEq (NoEqSym (BC.pack op) 2 priv sts) [arg1, arg2]

diffOp :: Bool -> Parser LNTerm -> Parser LNTerm
diffOp eqn plit = do
  ts <- symbol "diff" *> parens (commaSep (msetterm eqn plit))
  when (2 /= length ts) $ fail
    "the diff operator requires exactly 2 arguments"
  diff <- enableDiff <$> getState
  when eqn $ fail $
    "diff operator not allowed in equations"
  when (not diff) $ fail $
    "diff operator found, but flag diff not set"
  let arg1 = head ts
  let arg2 = head (tail ts)
  return $ fAppDiff (arg1, arg2)

-- | Parse a term.
term :: Parser LNTerm -> Bool -> Parser LNTerm
term plit eqn = asum
    [ pairing       <?> "pairs"
    , parens (msetterm eqn plit)
    , symbol "1:nat" *> pure fAppNatOne
    , symbol "%1"    *> pure fAppNatOne
    , symbol "1"     *> pure fAppOne
    , application   <?> "function application"
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
      asum [ try (symbol (BC.unpack sym)) *> pure (fApp (NoEq (NoEqSym sym 0 priv sts)) [])
           | NoEq (NoEqSym sym 0 priv sts) <- S.toList $ funSyms maudeSig ]

-- | A left-associative sequence of exponentations.
expterm :: Bool -> Parser LNTerm -> Parser LNTerm
expterm eqn plit = chainl1 (term plit eqn) ((\a b -> fAppExp (a,b)) <$ opExp)

-- | A left-associative sequence of multiplications.
multterm :: Bool -> Parser LNTerm -> Parser LNTerm
multterm eqn plit = do
    dh <- enableDH <$> getState
    if dh && not eqn -- if DH is not enabled, do not accept 'multterm's and 'expterm's
        then chainl1 (expterm eqn plit) ((\a b -> fAppAC Mult [a,b]) <$ opMult)
        else term plit eqn

-- | A left-associative sequence of xors.
xorterm :: Bool -> Parser LNTerm -> Parser LNTerm
xorterm eqn plit = do
    xor <- enableXor <$> getState
    if xor && not eqn-- if xor is not enabled, do not accept 'xorterms's
        then chainl1 (multterm eqn plit) ((\a b -> fAppAC Xor [a,b]) <$ opXor)
        else multterm eqn plit

-- | A left-associative sequence of multiset unions.
msetterm :: Bool -> Parser LNTerm -> Parser LNTerm
msetterm eqn plit = do
    mset <- enableMSet <$> getState
    if mset && not eqn-- if multiset is not enabled, do not accept 'msetterms's
        then chainl1 (natterm eqn plit) ((\a b -> fAppAC Union [a,b]) <$ opUnion)
        else natterm eqn plit

-- | A left-associative sequence of terms on natural numbers.
natterm :: Bool -> Parser LNTerm -> Parser LNTerm
natterm eqn plit = do
    nats <- enableNat <$> getState
    if nats -- if nat is not enabled, do not accept 'natterms's
        then try (xorterm eqn plit) <|> sumterm  --TODO-UNCERTAIN: not sure whether the order (mset-nat-xor-mult) matters (Cedric's was nat-mult-mset)
        else xorterm eqn plit
  where
    sumterm = chainl1 subnatterm ((\a b -> fAppAC NatPlus [a,b]) <$ opPlus)

    subnatterm = try $ asum
      [ parens sumterm
      , symbol "1:nat" *> pure fAppNatOne
      , symbol "1"     *> pure fAppNatOne  --TODO-UNCERTAIN (probably the intent was "if we expect a nat, we take 1 as nat instead of diffie-hellman")
      , sortedLlit LSortNat
      ]

-- | A right-associative sequence of tuples.
tupleterm :: Bool -> Parser LNTerm -> Parser LNTerm
tupleterm eqn plit = chainr1 (msetterm eqn plit) ((\a b -> fAppPair (a,b)) <$ comma)

-- | Parse a fact annotation
factAnnotation :: Parser FactAnnotation
factAnnotation = asum
  [ opUnion  *> pure SolveFirst
  , opMinus *> pure SolveLast
  , symbol "no_precomp" *> pure NoSources
  ]

-- | Parse a fact that does not necessarily have a term in it.
fact' :: Parser t -> Parser (Fact t)
fact' pterm = try (
    do multi <- option Linear (opBang *> pure Persistent)
       i     <- identifier
       case i of
         []                -> fail "empty identifier"
         (c:_) | isUpper c -> if (map toUpper i == "FR") && multi == Persistent then fail "fresh facts cannot be persistent" else return ()
               | otherwise -> fail "facts must start with upper-case letters"
       ts    <- parens (commaSep pterm)
       ann   <- option [] $ list factAnnotation
       mkProtoFact multi i (S.fromList ann) ts
    <?> "fact" )
  where
    singleTerm _ constr [t] = return $ constr t
    singleTerm f _      ts  = fail $ "fact '" ++ f ++ "' used with arity " ++
                                     show (length ts) ++ " instead of arity one"

    mkProtoFact multi f ann = case map toUpper f of
      "OUT" -> singleTerm f outFact
      "IN"  -> singleTerm f (inFactAnn ann)
      "KU"  -> singleTerm f kuFact
      "KD"  -> singleTerm f kdFact
      "DED" -> singleTerm f dedLogFact
      "FR"  -> singleTerm f freshFact
      _     -> return . protoFactAnn multi f ann

-- | Parse a fact.
fact :: Parser LNTerm -> Parser (Fact LNTerm)
fact plit = fact' (msetterm False plit)

------------------------------------------------------------------------------
-- Parsing Rules
------------------------------------------------------------------------------

-- | Parse a "(modulo ..)" information.
modulo :: String -> Parser ()
modulo thy = parens $ symbol_ "modulo" *> symbol_ thy

moduloE, moduloAC :: Parser ()
moduloE   = modulo "E"
moduloAC  = modulo "AC"

{- -- This has not been renamed from typing to source, as it is unclear.
-- | Parse a typing assertion modulo E.
typeAssertions :: Parser TypingE
typeAssertions = fmap TypingE $
    do try (symbols ["type", "assertions"])
       optional moduloE
       colon
       many1 ((,) <$> (try (msgvar <* colon))
                  <*> ( commaSep1 (try $ multterm llit) <|>
                        (opMinus *> pure [])
                      )
             )
    <|> pure []
-}

-- | Parse a 'RuleAttribute'.
ruleAttribute :: Parser RuleAttribute
ruleAttribute = asum
    [ symbol "colour=" *> (RuleColor <$> parseColor)
    , symbol "color="  *> (RuleColor <$> parseColor)
    ]
  where
    parseColor = do
        hc <- hexColor
        case hexToRGB hc of
            Just rgb  -> return rgb
            Nothing -> fail $ "Color code " ++ show hc ++ " could not be parsed to RGB"

-- | Parse RuleInfo
protoRuleInfo :: Parser ProtoRuleEInfo
protoRuleInfo = do
                _ <- symbol "rule"
                _ <- optional moduloE
                ident <- identifier
                att <- option [] $ list ruleAttribute
                _ <- colon
                return $ ProtoRuleEInfo (StandRule ident) att []

-- | Parse a protocol rule. For the special rules 'Reveal_fresh', 'Fresh',
-- 'Knows', and 'Learn' no rule is returned as the default theory already
-- contains them.
diffRule :: Parser (DiffProtoRule)
diffRule = do
    ri@(ProtoRuleEInfo (StandRule name) _ _)  <- try protoRuleInfo
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst letBlock
    (ps0,as0,cs0,rs0) <- genericRule
    let (ps,as,cs,rs) = apply subst (ps0,as0,cs0,rs0)
    leftRight  <- optionMaybe ( (,) <$> (symbol "left"  *> protoRule) <*> (symbol "right" *> protoRule))
    return $ DiffProtoRule (Rule (modify preRestriction (++ rs) ri) ps cs as (newVariables ps $ cs ++ as)) leftRight

-- | Parse a protocol rule. For the special rules 'Reveal_fresh', 'Fresh',
-- 'Knows', and 'Learn' no rule is returned as the default theory already
-- contains them
protoRule :: Parser (OpenProtoRule)
protoRule = do
    ri@(ProtoRuleEInfo (StandRule name ) _ _)  <- try protoRuleInfo
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst letBlock
    (ps0,as0,cs0,rs0) <- genericRule
    let (ps,as,cs,rs) = apply subst (ps0,as0,cs0,rs0)
    variants <- option [] $ symbol "variants" *> commaSep1 protoRuleAC
    return $ OpenProtoRule (Rule (modify preRestriction (++ rs) ri) ps cs as (newVariables ps $ cs ++ as)) variants

-- | Parse RuleInfo
protoRuleACInfo :: Parser ProtoRuleACInfo
protoRuleACInfo = (ProtoRuleACInfo <$> (StandRule <$>
                                        (symbol "rule" *> moduloAC *> identifier))
                               <*> (option [] $ list ruleAttribute))
                               <*> pure (Disj [emptySubstVFresh]) <*> pure []
                               <*  colon

-- | Parse a protocol rule variant modulo AC.
protoRuleAC :: Parser ProtoRuleAC
protoRuleAC = do
    ri@(ProtoRuleACInfo (StandRule name) _ _ _)  <- try protoRuleACInfo
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst letBlock
    (ps0,as0,cs0,rs0) <- genericRule
    let (ps,as,cs,_) = apply subst (ps0,as0,cs0,rs0)
    return $ Rule ri ps cs as (newVariables ps $ cs ++ as)

-- | Parse a let block with bottom-up application semantics.
letBlock :: Parser LNSubst
letBlock = toSubst <$> (symbol "let" *> many1 definition <* symbol "in")
  where
    toSubst = foldr1 compose . map (substFromList . return)
    definition = (,) <$> (sortedLVar [LSortMsg] <* equalSign) <*> msetterm False llit

-- | Parse an intruder rule.
intrRule :: Parser IntrRuleAC
intrRule = do
    info <- try (symbol "rule" *> moduloAC *> intrInfo <* colon)
    (ps,as,cs,[]) <- genericRule -- intruder rules should not introduce restrictions.
    return $ Rule info ps cs as (newVariables ps cs)
  where
    intrInfo = do
        name     <- identifier
        limit    <- option 0 natural
-- FIXME: Parse whether we have a subterm rule or a constant rule
--        Currently we (wrongly) always assume that we have a subterm rule, this prohibits recomputing variants
        case name of
          'c':cname -> return $ ConstrRule (BC.pack cname)
          'd':dname -> return $ DestrRule (BC.pack dname) (fromIntegral limit) True False
          _         -> fail $ "invalid intruder rule name '" ++ name ++ "'"

embeddedRestriction :: Parser a -> Parser a
embeddedRestriction factParser = symbol "_restrict" *> parens factParser <?> "restriction"

factOrRestr ::  Parser (Either SyntacticLNFormula LNFact)
factOrRestr = Right <$> fact llit
              <|> Left <$> embeddedRestriction standardFormula

genericRule :: Parser ([LNFact], [LNFact], [LNFact], [SyntacticLNFormula]) --- lhs, actions, rhs, restrictions
genericRule = do
    lhs         <- list (fact llit)
    actsAndRsts <-
        (   (pure [] <* symbol "-->")
        <|> (symbol "--[" *> commaSep factOrRestr <* symbol "]->")
        )
    rhs <- list (fact llit)
    return (lhs, rights actsAndRsts, rhs, lefts actsAndRsts)

newVariables :: [LNFact] -> [LNFact] -> [LNTerm]
newVariables prems concs = map varTerm $ S.toList newvars
  where
    newvars = S.difference concvars premvars
    premvars = S.fromList $ concatMap getFactVariables prems
    concvars = S.fromList $ concatMap getFactVariables concs

{-
-- | Add facts to a rule.
addFacts :: String        -- ^ Command to be used: add_concs, add_prems
         -> Parser (String, [LNFact])
addFacts cmd =
    (,) <$> (symbol cmd *> identifier <* colon) <*> commaSep1 fact
-}

------------------------------------------------------------------------------
-- Parsing transfer notation
------------------------------------------------------------------------------

{-
-- | Parse an lit with strings for both constants as well as variables.
tlit :: Parser TTerm
tlit = asum
    [ constTerm <$> singleQuoted identifier
    , varTerm  <$> identifier
    ]
-- | Parse a single transfer.
transfer :: Parser Transfer
transfer = do
  tf <- (\l -> Transfer l Nothing Nothing) <$> identifier <* kw DOT
  (do right <- kw RIGHTARROW *> identifier <* colon
      desc <- transferDesc
      return $ tf { tfRecv = Just (desc right) }
   <|>
   do right <- kw LEFTARROW *> identifier <* colon
      descr <- transferDesc
      (do left <- try $ identifier <* kw LEFTARROW <* colon
          descl <- transferDesc
          return $ tf { tfSend = Just (descr right)
                      , tfRecv = Just (descl left) }
       <|>
       do return $ tf { tfSend = Just (descr right) }
       )
   <|>
   do left <- identifier
      (do kw RIGHTARROW
          (do right <- identifier <* colon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc left)
                          , tfRecv = Just (desc right) }
           <|>
           do descl <- colon *> transferDesc
              (do right <- kw RIGHTARROW *> identifier <* colon
                  descr <- transferDesc
                  return $ tf { tfSend = Just (descl left)
                              , tfRecv = Just (descr right) }
               <|>
               do return $ tf { tfSend = Just (descl left) }
               )
           )
       <|>
       do kw LEFTARROW
          (do desc <- colon *> transferDesc
              return $ tf { tfRecv = Just (desc left) }
           <|>
           do right <- identifier <* colon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc right)
                          , tfRecv = Just (desc left) }
           )
       )
    )
  where
    transferDesc = do
        ts        <- tupleterm tlit
        moreConcs <- (symbol "note" *> many1 (try $ fact tlit))
                     <|> pure []
        types     <- typeAssertions
        return $ \a -> TransferDesc a ts moreConcs types
-- | Parse a protocol in transfer notation
transferProto :: Parser [ProtoRuleE]
transferProto = do
    name <- symbol "anb-proto" *> identifier
    braced (convTransferProto name <$> abbrevs <*> many1 transfer)
  where
    abbrevs = (symbol "let" *> many1 abbrev) <|> pure []
    abbrev = (,) <$> try (identifier <* kw EQUAL) <*> multterm tlit
-}

------------------------------------------------------------------------------
-- Parsing Standard and Guarded Formulas
------------------------------------------------------------------------------

-- | Parse an atom with possibly bound logical variables.
blatom :: Parser (SyntacticAtom BLTerm)
blatom = (fmap (fmapTerm (fmap Free))) <$> asum
  [ Last        <$> try (symbol "last" *> parens nodevarTerm)        <?> "last atom"
  , flip Action <$> try (fact llit <* opAt)        <*> nodevarTerm   <?> "action atom"
  , Syntactic . Pred <$> try (fact llit)                             <?> "predicate atom"
  , Subterm     <$> try (msetterm False llit <* opSubterm) <*> msetterm False llit <?> "subterm predicate"
  , Less        <$> try (nodevarTerm <* opLess)    <*> nodevarTerm   <?> "less atom"
  , EqE         <$> try (msetterm False llit <* opEqual) <*> msetterm False llit <?> "term equality"
  , EqE         <$>     (nodevarTerm  <* opEqual)  <*> nodevarTerm   <?> "node equality"
  ]
  where
    nodevarTerm = (lit . Var) <$> nodevar

-- | Parse an atom of a formula.
fatom :: Parser  SyntacticLNFormula
fatom = asum
  [ pure lfalse <* opLFalse
  , pure ltrue  <* opLTrue
  , Ato <$> try blatom
  , quantification
  , parens iff
  ]
  where
    quantification = do
        q <- (pure forall <* opForall) <|> (pure exists <* opExists)
        vs <- many1 lvar <* dot
        f  <- iff
        return $ foldr (hinted q) f vs

-- | Parse a negation.
negation :: Parser SyntacticLNFormula
negation = opLNot *> (Not <$> fatom) <|> fatom

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser SyntacticLNFormula
conjuncts = chainl1 negation ((.&&.) <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser SyntacticLNFormula
disjuncts = chainl1 conjuncts ((.||.) <$ opLOr)

-- | An implication.
imp :: Parser SyntacticLNFormula
imp = do
  lhs <- disjuncts
  asum [ opImplies *> ((lhs .==>.) <$> imp)
       , pure lhs ]

-- | An logical equivalence.
iff :: Parser SyntacticLNFormula
iff = do
  lhs <- imp
  asum [opLEquiv *> ((lhs .<=>.) <$> imp), pure lhs ]

-- | Parse a standard formula.
standardFormula :: Parser (SyntacticLNFormula)
standardFormula = iff


plainFormula :: Parser LNFormula
plainFormula = try $ do
    lnf <- toLNFormula <$> standardFormula
    case lnf of
        Nothing -> fail "Syntactic sugar is not allowed, guarded formula expected."
        Just lnf' -> return lnf'

-- | Parse a guarded formula using the hack of parsing a standard formula and
-- converting it afterwards.
-- FIXME: Write a proper parser.
guardedFormula :: Parser LNGuarded
guardedFormula = do
    pf <- plainFormula
    case formulaToGuarded pf of
           Left d   -> fail $ render d
           Right gf -> return gf


------------------------------------------------------------------------------
-- Parsing Restrictions
------------------------------------------------------------------------------

-- | Parse a 'RestrictionAttribute'.
restrictionAttribute :: Parser RestrictionAttribute
restrictionAttribute = asum
  [ symbol "left"          *> pure LHSRestriction
  , symbol "right"         *> pure RHSRestriction
  , symbol "both"          *> pure BothRestriction
  ]

-- | Parse a restriction.
restriction :: Parser SyntacticRestriction
restriction = Restriction <$> (symbol "restriction" *> identifier <* colon)
                          <*> doubleQuoted standardFormula

-- | Fail on parsing an old "axiom" keyword.
--legacyAxiom :: Parser Restriction
--legacyAxiom = symbol "axiom" *> fail "Using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'."

-- | Parse a legacy axiom, now called restriction.
legacyAxiom :: Parser SyntacticRestriction
legacyAxiom = trace ("Deprecation Warning: using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'.") Restriction <$> (symbol "axiom" *> identifier <* colon)
                          <*> doubleQuoted standardFormula

-- | Parse a diff restriction.
diffRestriction :: Parser ParseRestriction
diffRestriction = ParseRestriction <$> (symbol "restriction" *> identifier)
                    <*> (option [] $ list restrictionAttribute)
                    <*> (colon *> doubleQuoted plainFormula)

-- | Fail on parsing an old "axiom" keyword.
--legacyDiffAxiom :: Parser ParseRestriction
--legacyDiffAxiom = symbol "axiom" *> fail "Using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'."

-- | Parse a legacy diff axiom, now called restriction. Emits warning.
legacyDiffAxiom :: Parser ParseRestriction
legacyDiffAxiom = trace ("Deprecation Warning: using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'.") ParseRestriction <$> (symbol "axiom" *> identifier)
              <*> (option [] $ list restrictionAttribute)
              <*> (colon *> doubleQuoted plainFormula)

------------------------------------------------------------------------------
-- Parsing Lemmas
------------------------------------------------------------------------------

-- | Parse a 'LemmaAttribute'.
lemmaAttribute :: Bool -> Parser LemmaAttribute
lemmaAttribute diff = asum
  [ symbol "typing"        *> trace ("Deprecation Warning: using 'typing' is retired notation, replace all uses of 'typing' by 'sources'.\n") pure SourceLemma -- legacy support, emits deprecation warning
--  , symbol "typing"        *> fail "Using 'typing' is retired notation, replace all uses of 'typing' by 'sources'."
  , symbol "sources"       *> pure SourceLemma
  , symbol "reuse"         *> pure ReuseLemma
  , symbol "diff_reuse"    *> pure ReuseDiffLemma
  , symbol "use_induction" *> pure InvariantLemma
  , symbol "hide_lemma="   *> (HideLemma <$> identifier)
  , symbol "heuristic="    *> (LemmaHeuristic <$> parseGoalRanking)
  , symbol "left"          *> pure LHSLemma
  , symbol "right"         *> pure RHSLemma
--   , symbol "both"          *> pure BothLemma
  ]
  where
    parseGoalRanking = case diff of
        True  -> map charToGoalRankingDiff <$> many1 letter
        False -> map charToGoalRanking     <$> many1 letter

-- | Parse a 'TraceQuantifier'.
traceQuantifier :: Parser TraceQuantifier
traceQuantifier = asum
  [ symbol "all-traces" *> pure AllTraces
  , symbol "exists-trace"  *> pure ExistsTrace
  ]

protoLemma :: Parser f -> Parser (ProtoLemma f ProofSkeleton)
protoLemma parseFormula = skeletonLemma <$> (symbol "lemma" *> optional moduloE *> identifier)
                      <*> (option [] $ list (lemmaAttribute False))
                      <*> (colon *> option AllTraces traceQuantifier)
                      <*> doubleQuoted parseFormula
                      <*> (proofSkeleton <|> pure (unproven ()))

-- | Parse a lemma.
lemma :: Parser (SyntacticLemma ProofSkeleton)
lemma = protoLemma standardFormula

-- | Parse a lemma w/o syntactic sugar
plainLemma :: Parser (Lemma ProofSkeleton)
plainLemma = protoLemma plainFormula

-- | Parse a diff lemma.
diffLemma :: Parser (DiffLemma DiffProofSkeleton)
diffLemma = skeletonDiffLemma <$> (symbol "diffLemma" *> identifier)
                              <*> (option [] $ list (lemmaAttribute True))
                              <*> (colon *> (diffProofSkeleton <|> pure (diffUnproven ())))


------------------------------------------------------------------------------
-- Parsing Proofs
------------------------------------------------------------------------------

-- | Parse a node premise.
nodePrem :: Parser NodePrem
nodePrem = parens ((,) <$> nodevar
                       <*> (comma *> fmap (PremIdx . fromIntegral) natural))

-- | Parse a node conclusion.
nodeConc :: Parser NodeConc
nodeConc = parens ((,) <$> nodevar
                       <*> (comma *> fmap (ConcIdx .fromIntegral) natural))

-- | Parse a goal.
goal :: Parser Goal
goal = asum
    [ premiseGoal
    , actionGoal
    , chainGoal
    , disjSplitGoal
    , eqSplitGoal
    ]
  where
    actionGoal = do
        fa <- try (fact llit <* opAt)
        i  <- nodevar
        return $ ActionG i fa

    premiseGoal = do
        (fa, v) <- try ((,) <$> fact llit <*> opRequires)
        i  <- nodevar
        return $ PremiseG (i, v) fa

    chainGoal = ChainG <$> (try (nodeConc <* opChain)) <*> nodePrem

    disjSplitGoal = (DisjG . Disj) <$> sepBy1 guardedFormula (symbol "∥")

    eqSplitGoal = try $ do
        symbol_ "splitEqs"
        parens $ (SplitG . SplitId . fromIntegral) <$> natural


-- | Parse a proof method.
proofMethod :: Parser ProofMethod
proofMethod = asum
  [ symbol "sorry"         *> pure (Sorry Nothing)
  , symbol "simplify"      *> pure Simplify
  , symbol "solve"         *> (SolveGoal <$> parens goal)
  , symbol "contradiction" *> pure (Contradiction Nothing)
  , symbol "induction"     *> pure Induction
  ]

-- | Parse a proof skeleton.
proofSkeleton :: Parser ProofSkeleton
proofSkeleton =
    solvedProof <|> finalProof <|> interProof
  where
    solvedProof =
        symbol "SOLVED" *> pure (LNode (ProofStep Solved ()) M.empty)

    finalProof = do
        method <- symbol "by" *> proofMethod
        return (LNode (ProofStep method ()) M.empty)

    interProof = do
        method <- proofMethod
        cases  <- (sepBy oneCase (symbol "next") <* symbol "qed") <|>
                  ((return . (,) "") <$> proofSkeleton          )
        return (LNode (ProofStep method ()) (M.fromList cases))

    oneCase = (,) <$> (symbol "case" *> identifier) <*> proofSkeleton

-- | Parse a proof method.
diffProofMethod :: Parser DiffProofMethod
diffProofMethod = asum
  [ symbol "sorry"            *> pure (DiffSorry Nothing)
  , symbol "rule-equivalence" *> pure DiffRuleEquivalence
  , symbol "backward-search"  *> pure DiffBackwardSearch
  , symbol "step"             *> (DiffBackwardSearchStep <$> parens proofMethod)
  , symbol "ATTACK"           *> pure DiffAttack
  ]

-- | Parse a diff proof skeleton.
diffProofSkeleton :: Parser DiffProofSkeleton
diffProofSkeleton =
    solvedProof <|> finalProof <|> interProof
  where
    solvedProof =
        symbol "MIRRORED" *> pure (LNode (DiffProofStep DiffMirrored ()) M.empty)

    finalProof = do
        method <- symbol "by" *> diffProofMethod
        return (LNode (DiffProofStep method ()) M.empty)

    interProof = do
        method <- diffProofMethod
        cases  <- (sepBy oneCase (symbol "next") <* symbol "qed") <|>
                  ((return . (,) "") <$> diffProofSkeleton          )
        return (LNode (DiffProofStep method ()) (M.fromList cases))

    oneCase = (,) <$> (symbol "case" *> identifier) <*> diffProofSkeleton

------------------------------------------------------------------------------
-- Parsing Signatures
------------------------------------------------------------------------------

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
      , try (symbol "natural-numbers")
          *> extendSig natMaudeSig
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
      , try (symbol "natural-numbers")
          *> extendSig natMaudeSig
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

-- | User-defined sorts.
usersorts :: Parser ()
usersorts =
    symbol "usersorts" *> colon *> commaSep1 sortSymbol *> pure ()
  where
    sortSymbol = do
      ident <- identifier
      sig   <- getState
      setState (addUserSort ident sig)

functions :: Parser ()
functions =
    symbol "functions" *> colon *> commaSep1 functionSymbol *> pure ()
  where
    functionSymbol = do
        f          <- BC.pack <$> identifier
        (k, sorts) <- parseArity
        priv       <- option Public (symbol "[private]" *> pure Private)
        ac         <- option False (symbol "[AC]" *> pure True)
        if (BC.unpack f `elem` ["mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor"])
          then fail $ "`" ++ BC.unpack f ++ "` is a reserved function name for builtins."
          else return ()
        sig <- getState
        -- Sanity checks for user-sorted functions
        when (isJust sorts) (verifySorts (fromJust sorts) sig)
        if ac
          then do
            verifySymbol f (fromJust sorts)
            setState $ addUserACSym (UserAC (BC.unpack f) (head $ fromJust sorts)) sig
          else do
            let noeqsym = NoEqSym f k priv sorts
            verifyArities noeqsym sig
            setState $ addFunSym noeqsym sig

    -- Parse old-style function symbol (such as h/1, f/2, etc) or
    -- new-style function symbol (with function signature, such as
    -- f: Msg Msg -> Msg).
    parseArity = oldStyle <|> newStyle

    oldStyle = do
      k <- opSlash *> (fromIntegral <$> natural)
      return (k, Nothing)

    newStyle = do
      args <- colon *> wsSep identifier
      void $ symbol "->"
      retv <- identifier
      let sorts = args ++ [retv]
      return (length sorts - 1, Just sorts)

    verifySorts xs msig = flip mapM_ xs $ \sort ->
      if elem (sortFromString sort) (allSorts msig)
        then return ()
        else fail $ "Invalid sort specified: " ++ sort

    verifySymbol _ ([x,y,z]) | x == y && y == z = return ()
    verifySymbol f _ = fail $ "Invalid AC symbol: " ++ (BC.unpack f)

    verifyArities sym@(NoEqSym f _ _ _) sig =
      case lookup f [ (noEqOp o, o) | o <- S.toList (stFunSyms sig)] of
        Just other | other /= sym ->
          fail $ "conflicting symbols: " ++
                 show sym ++ " and " ++ show other
        _ -> return ()
      where
        noEqOp (NoEqSym fs _ _ _) = fs

    allSorts msig =
      [LSortMsg, LSortFresh, LSortPub, LSortNat] ++
      (S.toList $ userSortsForMaudeSig msig)

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
                    thy'       <-  foldM liftedAddPredicate thy predicates
                    return thy'
                    <?> "predicates"

-- used for debugging
-- println :: String -> ParsecT String u Identity ()
-- println str = traceShowM str

-- parse a process definition (let block)
processDef :: OpenTheory -> Parser ProcessDef
processDef thy= do
                letIdentifier
                i <- BC.pack <$> identifier
                equalSign
                p <- process thy
                return (ProcessDef (BC.unpack i) p )

-- | Parse a single sapic action, i.e., a thing that can appear before the ";"
-- (This includes almost all items that are followed by one instead of two
-- processes, the exception is replication)
sapicAction :: Parser SapicAction
sapicAction = try (do
                        _ <- symbol "new"
                        s <- msgvar
                        return (New s)
                   )
               <|> try (do
                        _ <- symbol "in"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- symbol ")"
                        return (ChIn Nothing t)
                   )
               <|> try (do
                        _ <- symbol "in"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- comma
                        t' <- msetterm False llit
                        _ <- symbol ")"
                        return (ChIn (Just t) t')
                   )
               <|> try (do
                        _ <- symbol "out"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- symbol ")"
                        return (ChOut Nothing t)
                   )
               <|> try (do
                        _ <- symbol "out"
                        _ <- symbol "("
                        t <- msetterm False llit
                        _ <- comma
                        t' <- msetterm False llit
                        _ <- symbol ")"
                        return (ChOut (Just t) t')
                   )
               <|> try (do
                        _ <- symbol "insert"
                        t <- msetterm False llit
                        _ <- comma
                        t' <- msetterm False llit
                        return (Insert t t')
                   )
               <|> try (do
                        _ <- symbol "delete"
                        t <- msetterm False llit
                        return (Delete t)
                   )
               <|> try (do
                        _ <- symbol "lock"
                        t <- msetterm False llit
                        return (Lock t)
                   )
               <|> try (do
                        _ <- symbol "unlock"
                        t <- msetterm False llit
                        return (Unlock t)
                   )
               <|> try (do
                        _ <- symbol "event"
                        f <- fact llit
                        return (Event f)
                   )
               <|> try ( MSR <$> genericRule)

-- | Parse a process. Process combinators like | are left-associative (not that
-- it matters), so we had to split the grammar for processes in two, so that
-- the precedence is expressed in a way that can be directly encoded in Parsec.
-- This is the grammar, more or less. (Process definition is written down in
-- a way that you can read of the precise definition from there
-- process:
--     | LP process RP
--     | LP process RP AT multterm
--     | actionprocess PARALLEL process
--     | actionprocess PLUS process
--     null

-- actionprocess:
--     | sapic_action optprocess
--     | NULL
--     | REP process
--     | IF if_cond THEN process ELSE process
--     | IF if_cond THEN process
--     | LOOKUP term AS literal IN process ELSE process
--     | LOOKUP term AS literal IN process
--     | LET id_eq_termseq IN process
--     | LET id_not_res EQ REPORT LP multterm RP IN process
--     | IDENTIFIER
--     | msr
process :: OpenTheory -> Parser Process
process thy=
            -- left-associative NDC and parallel using chainl1.
            -- Note: this roughly encodes the following grammar:
            -- <|>   try   (do
            --             p1 <- actionprocess thy
            --             opParallel
            --             p2 <- process thy
            --             return (ProcessParallel p1 p2))
                  try  (chainl1 (actionprocess thy) (
                             do { _ <- try opNDC; return (ProcessComb NDC mempty)}
                         <|> do { _ <- try opParallelDepr; return (ProcessComb Parallel mempty)}
                         <|> do { _ <- opParallel; return (ProcessComb Parallel mempty)}
                  ))
            <|>   try (do    -- parens parser + at multterm
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        _ <- symbol "@"
                        m <- msetterm False llit
                        return $ paddAnn p [ProcessLoc m]
                        )
                        -- TODO SAPIC parser: multterm return
                        -- This is what SAPIC did:  | LP process RP AT multterm                      { substitute "_loc_" $5 $2 }
            <|>    try  (do -- parens parser
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        return p)
            <|>    try  (do -- let expression parser
                        subst <- letBlock
                        p <- process thy
                        case Catch.catch (applyProcess subst p) (\ e  -> fail $ prettyLetExceptions e) of
                            (Left err) -> fail $ show err -- Should never occur, we handle everything above
                            (Right p') -> return p'
                        )
            <|>    do       -- action at top-level
                        p <- actionprocess thy
                        return p

actionprocess :: OpenTheory -> Parser Process
actionprocess thy=
            try (do         -- replication parser
                        _ <- symbol "!"
                        p <- process thy
                        return (ProcessAction Rep mempty p))
            <|> try (do     -- lookup / if with and w/o else branches
                        _ <- symbol "lookup"
                        t <- msetterm False llit
                        _ <- symbol "as"
                        v <- msgvar
                        _ <- symbol "in"
                        p <- process thy
                        _ <- symbol "else"
                        q <- process thy
                        return (ProcessComb (Lookup t v) mempty p q)
                   )
            <|> try (do
                        _ <- symbol "lookup"
                        t <- msetterm False llit
                        _ <- symbol "as"
                        v <- msgvar
                        _ <- symbol "in"
                        p <- process thy
                        return (ProcessComb (Lookup t v) mempty p (ProcessNull mempty))
                   )
            <|> try (do
                        _ <- symbol "if"
                        t1 <- msetterm False llit
                        _ <- opEqual
                        t2 <- msetterm False llit
                        _ <- symbol "then"
                        p <- process thy
                        q <- option (ProcessNull mempty) (symbol "else" *> process thy)
                        return (ProcessComb (CondEq t1 t2  ) mempty p q)
                        <?> "conditional process (with equality)"
                   )
            <|> try (do
                        _ <- symbol "if"
                        frml <- standardFormula
                        _ <- symbol "then"
                        p <- process thy
                        q <- option (ProcessNull mempty) (symbol "else" *> process thy)
                        return (ProcessComb (Cond frml) mempty p q)
                        <?> "conditional process (with predicate)"
                   )
            -- <|> try (do
            --             _ <- symbol "if"
            --             t1 <- msetterm llit
            --             _ <- opEqual
            --             t2 <- msetterm llit
            --             _ <- symbol "then"
            --             p <- process thy
            --             return (ProcessComb (CondEq t1 t2  ) mempty p (ProcessNull mempty))
            --        )
            -- <|> try (do
            --             _ <- symbol "if"
            --             pr <- fact llit
            --             _ <- symbol "then"
            --             p <- process thy
            --             return (ProcessComb (Cond pr) mempty p (ProcessNull mempty))
            --        )
            <|> try ( do  -- sapic actions are constructs separated by ";"
                        s <- sapicAction
                        _ <- opSeq
                        p <- actionprocess thy
                        return (ProcessAction s mempty p))
            <|> try ( do  -- allow trailing actions (syntactic sugar for action; 0)
                        s <- sapicAction
                        return (ProcessAction s mempty (ProcessNull mempty)))
            <|> try (do   -- null process: terminating element
                        _ <- opNull
                        return (ProcessNull mempty) )
            <|> try   (do -- parse identifier
                        -- println ("test process identifier parsing Start")
                        i <- BC.pack <$> identifier
                        a <- let p = checkProcess (BC.unpack i) thy in
                             (\x -> paddAnn x [ProcessName $ BC.unpack i]) <$> p
                        return a
                        )
            <|>    try  (do -- let expression parser
                        subst <- letBlock
                        p     <- process thy
                        case Catch.catch (applyProcess subst p) (\ e  -> fail $ prettyLetExceptions e) of
                            (Left err) -> fail $ show err -- Should never occur, we handle everything above
                            (Right p') -> return p'
                        )
            <|>   try (do    -- parens parser + at multterm
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        _ <- symbol "@"
                        m <- msetterm False llit
                        return $ paddAnn p [ProcessLoc m]
                        )
            <|> try (do        -- parens parser
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        return p
                    )

heuristic :: Bool -> Parser [GoalRanking]
heuristic diff = do
      symbol "heuristic" *> colon *> parseGoalRanking
  where
    parseGoalRanking = case diff of
        True  -> map charToGoalRankingDiff <$> identifier
        False -> map charToGoalRanking     <$> identifier


------------------------------------------------------------------------------
-- Parsing Theories
------------------------------------------------------------------------------

-- | Exception type for catching parsing errors
data ParsingException = UndefinedPredicate FactTag
                      | DuplicateItem OpenTheoryItem
                      | TryingToAddFreshRule

instance Show (ParsingException) where
    show (UndefinedPredicate facttag) = "undefined predicate "
                                         ++ showFactTagArity facttag
                                         -- ++ " in lemma: "
                                         -- ++ get lName lem
                                         -- ++ "."
    show (DuplicateItem (RuleItem ru)) = "duplicate rule: " ++ render (prettyRuleName $ get oprRuleE ru)
    show (DuplicateItem (LemmaItem lem)) =  "duplicate lemma: " ++ get lName lem
    show (DuplicateItem (RestrictionItem rstr)) =  "duplicate restriction: " ++ get rstrName rstr
    show (DuplicateItem (TextItem _)) =  undefined
    show (DuplicateItem (PredicateItem pr)) =  "duplicate predicate: " ++ render (prettyFact prettyLVar (get pFact pr))
    show (DuplicateItem (SapicItem (ProcessItem _))) =  undefined
    show (DuplicateItem (SapicItem (ProcessDefItem pDef))) =
        "duplicate process: " ++ get pName pDef
    show TryingToAddFreshRule = "The fresh rule is implicitely contained in the theory and does not need to be added."

instance Catch.Exception ParsingException

instance Fail.MonadFail (Either Catch.SomeException) where
  fail = Fail.fail


liftEitherToEx :: (Catch.MonadThrow m, Catch.Exception e) => (t -> e) -> Either t a -> m a
liftEitherToEx _ (Right r)     = return r
liftEitherToEx constr (Left l) = Catch.throwM $ constr l

liftMaybeToEx :: (Catch.MonadThrow m, Catch.Exception e) => e -> Maybe a -> m a
liftMaybeToEx _      (Just r) = return r
liftMaybeToEx constr Nothing  = Catch.throwM constr

liftedExpandFormula :: Catch.MonadThrow m =>
                       Theory sig c r p s -> SyntacticLNFormula -> m LNFormula
liftedExpandFormula thy = liftEitherToEx UndefinedPredicate . expandFormula thy

liftedExpandLemma :: Catch.MonadThrow m => Theory sig c r p1 s
                     -> ProtoLemma SyntacticLNFormula p2 -> m (ProtoLemma LNFormula p2)
liftedExpandLemma thy =  liftEitherToEx UndefinedPredicate . expandLemma thy

liftedExpandRestriction :: Catch.MonadThrow m =>
                           Theory sig c r p s
                           -> ProtoRestriction SyntacticLNFormula
                           -> m (ProtoRestriction LNFormula)
liftedExpandRestriction thy = liftEitherToEx UndefinedPredicate . expandRestriction thy

liftedAddProtoRuleNoExpand :: Catch.MonadThrow m => OpenTheory -> Theory.OpenProtoRule -> m OpenTheory
liftedAddProtoRuleNoExpand thy ru = liftMaybeToEx (DuplicateItem (RuleItem ru)) (addOpenProtoRule ru thy)

liftedAddPredicate :: Catch.MonadThrow m =>
                      Theory sig c r p SapicElement
                      -> Predicate -> m (Theory sig c r p SapicElement)
liftedAddPredicate thy prd = liftMaybeToEx (DuplicateItem (PredicateItem prd)) (addPredicate prd thy)

liftedAddRestriction :: Catch.MonadThrow m =>
                        Theory sig c r p s
                        -> ProtoRestriction SyntacticLNFormula -> m (Theory sig c r p s)
liftedAddRestriction thy rstr = do
        rstr' <- liftedExpandRestriction thy rstr
        liftMaybeToEx (DuplicateItem $ RestrictionItem rstr') (addRestriction rstr' thy)
                                 -- Could catch at which point in to lemma, but need MonadCatch
                                 -- ++ " in definition of predicate: "
                                 -- ++ get rstrName rstr
                                 -- ++ "."


liftedAddLemma :: Catch.MonadThrow m =>
                  Theory sig c r ProofSkeleton s
                  -> ProtoLemma SyntacticLNFormula ProofSkeleton
                  -> m (Theory sig c r ProofSkeleton s)
liftedAddLemma thy lem = do
        lem' <- liftedExpandLemma thy lem
        liftMaybeToEx (DuplicateItem $ LemmaItem lem') (addLemma lem' thy)
                                         -- Could catch at which point in to lemma, but need MonadCatch
                                         -- ++ " in lemma: "
                                         -- ++ get lName lem
                                         -- ++ "."

-- | Add new protocol rule and introduce restrictions for _restrict contruct
--  1. expand syntactic restrict constructs
--  2. for each, chose fresh action and restriction name
--  3. add action names to rule
--  4. add rule, fail if duplicate
--  5. add restrictions, fail if duplicate
-- FIXME: we only deal we the rule modulo E here, if variants modulo AC are
--        imported we do not check if they have _restrict annotations
--        (but they should not, as they will not be exported)
liftedAddProtoRule :: Catch.MonadThrow m => OpenTheory -> OpenProtoRule -> m (OpenTheory)
liftedAddProtoRule thy ru
    | (StandRule rname) <- get (preName . rInfo . oprRuleE) ru = do
        rformulasE <- mapM (liftedExpandFormula thy) (rfacts $ get oprRuleE ru)
        thy'      <- foldM addExpandedRestriction thy  (restrictions rname rformulasE)
        thy''     <- liftedAddProtoRuleNoExpand   thy' (addActions   rname rformulasE) -- TODO was ru instead of rformulas
        return thy''
    | otherwise = Catch.throwM TryingToAddFreshRule
            where
                rfacts = get (preRestriction . rInfo)
                addExpandedRestriction thy' xrstr = liftMaybeToEx
                                                     (DuplicateItem $ RestrictionItem xrstr)
                                                     (addRestriction xrstr thy')
                addActions   rname rformulas = modify (rActs . oprRuleE) (++ actions rname rformulas) ru

                restrictions rname rformulas =  map (fst . fromRuleRestriction' rname) (counter rformulas)
                actions      rname rformulas =  map (snd . fromRuleRestriction' rname) (counter rformulas)
                fromRuleRestriction' rname (i,f) = fromRuleRestriction (rname ++ "_" ++ show i) f
                counter = zip [1::Int ..]


-- | checks if process exists, if not -> error
checkProcess :: String -> OpenTheory -> Parser Process
checkProcess i thy = case lookupProcessDef i thy of
    Just p -> return $ get pBody p
    Nothing -> fail $ "process not defined: " ++ i

-- We can throw exceptions, but not catch them
instance Catch.MonadThrow (ParsecT String MaudeSig Data.Functor.Identity.Identity) where
    throwM e = fail (show e)

-- | Parse a theory.
theory :: [String]   -- ^ Defined flags.
       -> Parser OpenTheory
theory flags0 = do
    msig <- getState
    when ("diff" `S.member` (S.fromList flags0)) $ putState (msig `mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    symbol_ "begin"
        *> addItems (S.fromList flags0) (set thyName thyId (defaultOpenTheory ("diff" `S.member` (S.fromList flags0))))
        <* symbol "end"
  where
    addItems :: S.Set String -> OpenTheory -> Parser OpenTheory
    addItems flags thy = asum
      [ do thy' <- liftedAddHeuristic thy =<< (heuristic False)
           addItems flags thy'
      , do thy' <- builtins thy
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy'
      , do thy' <- options thy
           addItems flags thy'
      , do usersorts
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy
      , do functions
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy
      , do equations
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems flags thy'
      , do thy' <- liftedAddRestriction thy =<< restriction
           addItems flags thy'
      , do thy' <- liftedAddRestriction thy =<< legacyAxiom
           addItems flags thy'
           -- add legacy deprecation warning output
      , do thy' <- liftedAddLemma thy =<< lemma
           addItems flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
           -- thy'' <- foldM liftedAddRestriction thy' $
           --  map (Restriction "name") [get (preRestriction . rInfo) ru]
           addItems flags thy'
      , do r <- intrRule
           addItems flags (addIntrRuleACs [r] thy)
      , do c <- formalComment
           addItems flags (addFormalComment c thy)
      , do procc <- process thy                          -- try parsing a process
           addItems flags (addProcess procc thy)         -- add process to theoryitems and proceed parsing (recursive addItems call)
      , do thy' <- ((liftedAddProcessDef thy) =<<) (processDef thy)     -- similar to process parsing but in addition check that process with this name is only defined once (checked via liftedAddProcessDef)
           addItems flags thy'
      , do thy' <- preddeclaration thy
           addItems flags (thy')
      , do ifdef flags thy
      , do define flags thy
      , do return thy
      ]


    define flags thy = do
       flag <- try (symbol "#define") *> identifier
       addItems (S.insert flag flags) thy

    ifdef :: S.Set String -> OpenTheory -> Parser OpenTheory
    ifdef flags thy = do
       flag <- symbol_ "#ifdef" *> identifier
       if flag `S.member` flags
         then do thy' <- addItems flags thy
                 symbol_ "#endif"
                 addItems flags thy'
         else do _ <- manyTill anyChar (try (symbol_ "#endif"))
                 addItems flags thy

    -- check process defined only once
    -- add process to theoryitems
    liftedAddProcessDef thy pDef = case addProcessDef pDef thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate process: " ++ get pName pDef

    liftedAddHeuristic thy h = case addHeuristic h thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "default heuristic already defined"

-- | Parse a diff theory.
diffTheory :: [String]   -- ^ Defined flags.
       -> Parser OpenDiffTheory
diffTheory flags0 = do
    msig <- getState
    putState (msig `mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    symbol_ "begin"
        *> addItems (S.fromList flags0) (set diffThyName thyId (defaultOpenDiffTheory ("diff" `S.member` (S.fromList flags0))))
        <* symbol "end"
  where
    addItems :: S.Set String -> OpenDiffTheory -> Parser OpenDiffTheory
    addItems flags thy = asum
      [ do thy' <- liftedAddHeuristic thy =<< (heuristic True)
           addItems flags thy'
      , do
           diffbuiltins
           msig <- getState
           addItems flags $ set (sigpMaudeSig . diffThySignature) msig thy
      , do functions
           msig <- getState
           addItems flags $ set (sigpMaudeSig . diffThySignature) msig thy
      , do equations
           msig <- getState
           addItems flags $ set (sigpMaudeSig . diffThySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems flags thy'
      , do thy' <- liftedAddRestriction' thy =<< diffRestriction
           addItems flags thy'
      , do thy' <- liftedAddRestriction' thy =<< legacyDiffAxiom
           addItems flags thy'
           -- add legacy deprecation warning output
      , do thy' <- liftedAddLemma' thy =<< plainLemma
           addItems flags thy'
      , do thy' <- liftedAddDiffLemma thy =<< diffLemma
           addItems flags thy'
      , do ru <- diffRule
           thy' <- liftedAddDiffRule thy ru
           addItems flags thy'
      , do r <- intrRule
           addItems flags (addIntrRuleACsDiffAll [r] thy)
      , do c <- formalComment
           addItems flags (addFormalCommentDiff c thy)
      , do ifdef flags thy
      , do define flags thy
      , do return thy
      ]

    define :: S.Set String -> OpenDiffTheory -> Parser OpenDiffTheory
    define flags thy = do
       flag <- try (symbol "#define") *> identifier
       addItems (S.insert flag flags) thy

    ifdef :: S.Set String -> OpenDiffTheory -> Parser OpenDiffTheory
    ifdef flags thy = do
       flag <- symbol_ "#ifdef" *> identifier
       if flag `S.member` flags
         then do thy' <- addItems flags thy
                 symbol_ "#endif"
                 addItems flags thy'
         else do _ <- manyTill anyChar (try (string "#"))
                 symbol_ "endif"
                 addItems flags thy

    liftedAddHeuristic thy h = case addDiffHeuristic h thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "default heuristic already defined"

    liftedAddDiffRule thy ru = case addOpenProtoDiffRule ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate rule or inconsistent names: " ++ render (prettyRuleName $ get dprRule ru)

    liftedAddDiffLemma thy ru = case addDiffLemma ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate Diff Lemma: " ++ render (prettyDiffLemmaName ru)

    liftedAddLemma' thy lem = if isLeftLemma lem
                                then case addLemmaDiff LHS lem thy of
                                        Just thy' -> return thy'
                                        Nothing   -> fail $ "duplicate lemma: " ++ get lName lem
                                else if isRightLemma lem
                                     then case addLemmaDiff RHS lem thy of
                                             Just thy' -> return thy'
                                             Nothing   -> fail $ "duplicate lemma: " ++ get lName lem
                                     else case addLemmaDiff RHS (addRightLemma lem) thy of
                                             Just thy' -> case addLemmaDiff LHS (addLeftLemma lem) thy' of
                                                             Just thy'' -> return thy''
                                                             Nothing   -> fail $ "duplicate lemma: " ++ get lName lem
                                             Nothing   -> fail $ "duplicate lemma: " ++ get lName lem

    liftedAddRestriction' thy rstr = if isLeftRestriction rstr
                                       then case addRestrictionDiff LHS (toRestriction rstr) thy of
                                               Just thy' -> return thy'
                                               Nothing   -> fail $ "duplicate restriction: " ++ get rstrName (toRestriction rstr)
                                       else if isRightRestriction rstr
                                               then case addRestrictionDiff RHS (toRestriction rstr) thy of
                                                  Just thy' -> return thy'
                                                  Nothing   -> fail $ "duplicate restriction: " ++ get rstrName (toRestriction rstr)
                                               else case addRestrictionDiff RHS (toRestriction rstr) thy of
                                                  Just thy' -> case addRestrictionDiff LHS (toRestriction rstr) thy' of
                                                     Just thy'' -> return thy''
                                                     Nothing   -> fail $ "duplicate restriction: " ++ get rstrName (toRestriction rstr)
                                                  Nothing   -> fail $ "duplicate restriction: " ++ get rstrName (toRestriction rstr)
