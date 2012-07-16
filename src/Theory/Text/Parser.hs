{-# LANGUAGE TupleSections #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing protocol theories.
module Theory.Text.Parser (
    parseOpenTheory
  , parseOpenTheoryString
  , parseLemma
  , parseIntruderRulesDH
  ) where

import           Prelude                  hiding (id, (.))

import qualified Data.ByteString.Char8    as BC
import           Data.Char                (isUpper, toUpper)
import           Data.Foldable            (asum)
import           Data.Label
import qualified Data.Map                 as M
import           Data.Monoid
import qualified Data.Set                 as S

import           Control.Applicative      hiding (empty, many, optional)
import           Control.Category
import           Control.Monad

import           Text.Parsec              hiding (string, token, (<|>))
import           Text.PrettyPrint.Class   (render)

import           Term.Substitution
import           Term.SubtermRule
import           Theory
import           Theory.Text.Parser.Token


-- | A formal comment; i.e., (header, body)
formalComment :: Parser (String, String)
formalComment =
    (,) <$> text begin
        <*> (concat <$> many (text content) <* text end)
  where
    begin (TextBegin str)     = return str
    begin _                   = mzero
    content (TextContent str) = return str
    content _                 = mzero
    end (TextEnd)             = return ()
    end _                     = mzero


------------------------------------------------------------------------------
-- Lexing and parsing theory files and proof methods
------------------------------------------------------------------------------

-- | Parse a security protocol theory file.
parseOpenTheory :: [String] -- ^ Defined flags
                -> FilePath -> IO OpenTheory
parseOpenTheory flags = parseFile (theory flags)

-- | Parse DH intruder rules.
parseIntruderRulesDH :: FilePath -> IO [IntrRuleAC]
parseIntruderRulesDH = parseFile (setState dhMaudeSig >> many intrRule)

-- | Parse a security protocol theory from a string.
parseOpenTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> Either ParseError OpenTheory
parseOpenTheoryString flags = parseFromString (theory flags)

-- | Parse a lemma for an open theory from a string.
parseLemma :: String -> Either ParseError (Lemma ProofSkeleton)
parseLemma = parseFromString lemma

------------------------------------------------------------------------------
-- Parsing Terms
------------------------------------------------------------------------------


{-
BNF:  Not completely up to date...

theory      := 'theory' ident 'begin' protocol 'end'
protocol    := rules
rules       := rule | rule rules
intrrule    := ident '[' intrinfo ']' ':' terms '-->' terms
intrinfo    := 'Destr' | 'Constr'
protorule   := ident ':' factList '-->' factList
factList    := '[' [facts] ']'
facts       := fact | fact ',' facts
protoFact   := ident '(' terms ')'
terms       := term | term ',' terms
term        := lit | application | '<' term ',' terms '>'  -- right assoc pairing
application := ident '(' terms ')'
lit        := ident | '\'' ident '\''
ident       := <a-zA-Z> (<a-zA-Z0-9-_)


// example protocol rule

  Init_1:
    [ Pub(I), Pub(R), Fresh(ni) ]
    -->
    [ Init_1(I,R,ni), Send(encA(pk(R), <I,R,ni>)) ]

// example intruder rule

  Exp [Constr]:
    [ (x^_((x1*x2))), ((x3*x1)*_x4) ]
    -->
    [ (x^(x3*_((x4*x2)))) ]

-}

------------------------------------------------------------------------------
-- Parsing Terms
------------------------------------------------------------------------------

-- | Parse an lit with logical variables.
llit :: Parser LNTerm
llit = asum [freshTerm <$> freshName, pubTerm <$> pubName, varTerm <$> msgvar]

-- | Lookup the arity of a non-ac symbol. Fails with a sensible error message
-- if the operator is not known.
lookupNonACArity :: String -> Parser Int
lookupNonACArity op = do
    maudeSig <- getState
    case lookup (BC.pack op) (S.toList $ allFunctionSymbols maudeSig) of
        Nothing -> fail $ "unknown operator `" ++ op ++ "'"
        Just k  -> return k

-- | Parse an n-ary operator application for arbitrary n.
naryOpApp :: Ord l => Parser (Term l) -> Parser (Term l)
naryOpApp plit = do
    op <- identifier
    k  <- lookupNonACArity op
    ts <- parens $ if k == 1
                     then return <$> tupleterm plit
                     else commaSep (multterm plit)
    let k' = length ts
    when (k /= k') $
        fail $ "operator `" ++ op ++"' has arity " ++ show k ++
               ", but here it is used with arity " ++ show k'
    return $ fAppNonAC (BC.pack op, k') ts

-- | Parse a binary operator written as @op{arg1}arg2@.
binaryAlgApp :: Ord l => Parser (Term l) -> Parser (Term l)
binaryAlgApp plit = do
    op <- identifier
    k <- lookupNonACArity op
    arg1 <- braced (tupleterm plit)
    arg2 <- term plit
    when (k /= 2) $ fail $
      "only operators of arity 2 can be written using the `op{t1}t2' notation"
    return $ fAppNonAC (BC.pack op, 2) [arg1, arg2]

-- | Parse a term.
term :: Ord l => Parser (Term l) -> Parser (Term l)
term plit = asum
    [ pairing       <?> "pairs"
    , parens (multterm plit)
    , string "1" *> pure fAppOne
    , application <?> "function application"
    , nullaryApp
    , plit
    ]
    <?> "term"
  where
    application = asum $ map (try . ($ plit)) [naryOpApp, binaryAlgApp]
    pairing = angled (tupleterm plit)
    nullaryApp = do
      maudeSig <- getState
      asum [ try (string (BC.unpack sym)) *> pure (fApp (NonAC (sym,0)) [])
           | (sym,0) <- S.toList $ allFunctionSymbols maudeSig ]

-- | A left-associative sequence of exponentations.
expterm :: Ord l => Parser (Term l) -> Parser (Term l)
expterm plit = chainl1 (term plit) ((\a b -> fAppExp (a,b)) <$ opExp)

-- | A left-associative sequence of multiplications.
multterm :: Ord l => Parser (Term l) -> Parser (Term l)
multterm plit = do
    dh <- enableDH <$> getState
    if dh -- if DH is not enabled, do not accept 'multterm's and 'expterm's
        then chainl1 (expterm plit) ((\a b -> fAppMult [a,b]) <$ opMult)
        else term plit

-- | A right-associative sequence of tuples.
tupleterm :: Ord l => Parser (Term l) -> Parser (Term l)
tupleterm plit = chainr1 (multterm plit) ((\a b -> fAppPair (a,b))<$ opComma)

-- | Parse a fact.
fact :: Ord l => Parser (Term l) -> Parser (Fact (Term l))
fact plit =
    do multi <- option Linear (opBang *> pure Persistent)
       i     <- identifier
       case i of
         []                -> fail "empty identifier"
         (c:_) | isUpper c -> return ()
               | otherwise -> fail "facts must start with upper-case letters"
       ts    <- parens (commaSep (multterm plit))
       mkProtoFact multi i ts
    <?> "protocol fact"
  where
    singleTerm _ constr [t] = return $ constr t
    singleTerm f _      ts  = fail $ "fact '" ++ f ++ "' used with arity " ++
                                     show (length ts) ++ " instead of arity one"

    mkProtoFact multi f = case map toUpper f of
      "OUT" -> singleTerm f outFact
      "IN"  -> singleTerm f inFact
      "KU"  -> singleTerm f kuFact
      "KD"  -> return . Fact KDFact
      "DED" -> return . Fact DedFact
      "FR"  -> singleTerm f freshFact
      _     -> return . protoFact multi f


------------------------------------------------------------------------------
-- Parsing Rules
------------------------------------------------------------------------------

-- | Parse a "(modulo ..)" information.
modulo :: String -> Parser ()
modulo thy = parens $ strings ["modulo", thy]

moduloE, moduloAC :: Parser ()
moduloE  = modulo "E"
moduloAC = modulo "AC"

{-
-- | Parse a typing assertion modulo E.
typeAssertions :: Parser TypingE
typeAssertions = fmap TypingE $
    do try (strings ["type", "assertions"])
       optional moduloE
       opColon
       many1 ((,) <$> (try (msgvar <* opColon))
                  <*> ( commaSep1 (try $ multterm llit) <|>
                        (opMinus *> pure [])
                      )
             )
    <|> pure []
-}

-- | Parse a protocol rule. For the special rules 'Reveal_fresh', 'Fresh',
-- 'Knows', and 'Learn' no rule is returned as the default theory already
-- contains them.
protoRule :: Parser (ProtoRuleE)
protoRule = do
    name  <- try (string "rule" *> optional moduloE *> identifier <* opColon)
    subst <- option emptySubst letBlock
    (ps,as,cs) <- genericRule
    return $ apply subst $ Rule (StandRule name) ps cs as

-- | Parse a let block with bottom-up application semantics.
letBlock :: Parser LNSubst
letBlock = do
    toSubst <$> (string "let" *> many1 definition <* string "in")
  where
    toSubst = foldr1 compose . map (substFromList . return)
    definition = (,) <$> (sortedLVar [LSortMsg] <* equalSign) <*> multterm llit

-- | Parse an intruder rule.
intrRule :: Parser IntrRuleAC
intrRule = do
    info <- try (string "rule" *> moduloAC *> intrInfo <* opColon)
    (ps,as,cs) <- genericRule
    return $ Rule info ps cs as
  where
    intrInfo = do
        name <- identifier
        case name of
          'c':cname -> return $ ConstrRule (BC.pack cname)
          'd':dname -> return $ DestrRule (BC.pack dname)
          _         -> fail $ "invalid intruder rule name '" ++ name ++ "'"

genericRule :: Parser ([LNFact], [LNFact], [LNFact])
genericRule =
    (,,) <$> list (fact llit)
         <*> ((pure [] <* opLongrightarrow) <|>
              (opMinus *> opMinus *> list (fact llit) <* opRightarrow))
         <*> list (fact llit)

{-
-- | Add facts to a rule.
addFacts :: String        -- ^ Command to be used: add_concs, add_prems
         -> Parser (String, [LNFact])
addFacts cmd =
    (,) <$> (string cmd *> identifier <* opColon) <*> commaSep1 fact
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
  (do right <- kw RIGHTARROW *> identifier <* opColon
      desc <- transferDesc
      return $ tf { tfRecv = Just (desc right) }
   <|>
   do right <- kw LEFTARROW *> identifier <* opColon
      descr <- transferDesc
      (do left <- try $ identifier <* kw LEFTARROW <* opColon
          descl <- transferDesc
          return $ tf { tfSend = Just (descr right)
                      , tfRecv = Just (descl left) }
       <|>
       do return $ tf { tfSend = Just (descr right) }
       )
   <|>
   do left <- identifier
      (do kw RIGHTARROW
          (do right <- identifier <* opColon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc left)
                          , tfRecv = Just (desc right) }
           <|>
           do descl <- opColon *> transferDesc
              (do right <- kw RIGHTARROW *> identifier <* opColon
                  descr <- transferDesc
                  return $ tf { tfSend = Just (descl left)
                              , tfRecv = Just (descr right) }
               <|>
               do return $ tf { tfSend = Just (descl left) }
               )
           )
       <|>
       do kw LEFTARROW
          (do desc <- opColon *> transferDesc
              return $ tf { tfRecv = Just (desc left) }
           <|>
           do right <- identifier <* opColon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc right)
                          , tfRecv = Just (desc left) }
           )
       )
    )
  where
    transferDesc = do
        ts        <- tupleterm tlit
        moreConcs <- (string "note" *> many1 (try $ fact tlit))
                     <|> pure []
        types     <- typeAssertions
        return $ \a -> TransferDesc a ts moreConcs types


-- | Parse a protocol in transfer notation
transferProto :: Parser [ProtoRuleE]
transferProto = do
    name <- string "anb" *> opMinus *> string "proto" *> identifier
    braced (convTransferProto name <$> abbrevs <*> many1 transfer)
  where
    abbrevs = (string "let" *> many1 abbrev) <|> pure []
    abbrev = (,) <$> try (identifier <* kw EQUAL) <*> multterm tlit

-}

------------------------------------------------------------------------------
-- Parsing Proofs
------------------------------------------------------------------------------

{-
-- | Parse a node premise.
nodePrem :: Parser NodePrem
nodePrem = NodePrem <$> parens ((,) <$> nodevar <*> (kw COMMA *> integer))

-- | Parse a node conclusion.
nodeConc :: Parser NodeConc
nodeConc = NodeConc <$> parens ((,) <$> nodevar <*> (kw COMMA *> integer))
-}


{-
-- | Parse the @--|@ deduced before operator.
dedBeforeOp :: Parser ()
dedBeforeOp = try (opMinus *> opMinus *> kw MID)

-- | Parse the @<@ temporal less operator.
edgeOp :: Parser ()
edgeOp = try (kw GREATER *> kw RIGHTARROW)

-- | Parse the @~~>@ chain operator.
chainOp :: Parser ()
chainOp = kw TILDE *> kw TILDE *> kw TILDE *> kw GREATER
-}

-- | Parse a goal.
goal :: Parser Goal
goal = fail "SM: reimplement goal parsing" {- asum
  [ splitGoal
  , premiseGoal
  , chainGoal
  ]
  where
    premiseGoal = try $ do
        v  <- nodevar
        i  <- brackets integer <* requiresOp
        fa <- fact llit
        return $ PremiseGoal fa (NodePrem (v, i))

    chainGoal = ChainGoal
        <$> (try $ term llit <* opColon)
        <*> (Chain <$> (nodeConc <* chainOp) <*> nodePrem)

    splitGoal = do
        split <- (string "splitEqsOn"    *> pure SplitEqs) <|>
                 (string "splitTypingOn" *> pure SplitTyping)
        SplitGoal split <$> parens integer
-}

-- | Parse a proof method.
proofMethod :: Parser ProofMethod
proofMethod = asum
  [ string "sorry"         *> pure (Sorry "not yet proven")
  , string "simplify"      *> pure Simplify
  , string "solve"         *> (SolveGoal <$> parens goal)
  , string "contradiction" *> pure (Contradiction Nothing)
  ]

-- | Parse a proof skeleton.
proofSkeleton :: Parser ProofSkeleton
proofSkeleton =
    finalProof <|> interProof
  where
    finalProof = do
        method <- string "by" *> proofMethod
        return (LNode (ProofStep method ()) M.empty)

    interProof = do
        method <- proofMethod
        cases  <- (sepBy oneCase (string "next") <* string "qed") <|>
                  ((return . ("",)) <$> proofSkeleton           )
        return (LNode (ProofStep method ()) (M.fromList cases))

    oneCase = (,) <$> (string "case" *> identifier) <*> proofSkeleton

------------------------------------------------------------------------------
-- Parsing Formulas and Lemmas
------------------------------------------------------------------------------

-- | Parse an atom with possibly bound logical variables.
blatom :: Parser BLAtom
blatom = (fmap (fmapTerm (fmap Free))) <$> asum
  [ flip Action <$> try (fact llit <* opAt)        <*> nodevarTerm   <?> "action"
  , Less        <$> try (nodevarTerm <* opLess)    <*> nodevarTerm   <?> "less"
  , EqE         <$> try (multterm llit <* opEqual) <*> multterm llit <?> "term equality"
  , EqE         <$>     (nodevarTerm  <* opEqual)  <*> nodevarTerm   <?> "node equality"
  ]
  where
    nodevarTerm = (lit . Var) <$> nodevar
    -- nodePrem = annNode PremIdx
    -- nodeConc = annNode ConcIdx
    -- annNode mkAnn = parens ((,) <$> (nodevarTerm <* kw COMMA)
    --                             <*> (mkAnn <$> integer))

-- | Parse an atom of a formula.
fatom :: Parser (LFormula Name)
fatom = asum
  [ pure lfalse <* string "F"
  , pure ltrue  <* string "T"
  , Ato <$> try blatom
  , quantification
  , parens iff
  ]
  where
    quantification = do
        q <- (pure forall <* opForall) <|> (pure exists <* opExists)
        vs <- many1 lvar <* opDot
        f  <- iff
        return $ foldr (hinted q) f vs

    hinted :: ((String, LSort) -> LVar -> a) -> LVar -> a
    hinted f v@(LVar n s _) = f (n,s) v



-- | Parse a negation.
negation :: Parser (LFormula Name)
negation = opLNot *> (Not <$> fatom) <|> fatom

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser (LFormula Name)
conjuncts = chainl1 negation ((.&&.) <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser (LFormula Name)
disjuncts = chainl1 conjuncts ((.||.) <$ opLOr)

-- | An implication.
imp :: Parser (LFormula Name)
imp = do
  lhs <- disjuncts
  asum [ opImplies *> ((lhs .==>.) <$> imp)
       , pure lhs ]

-- | An logical equivalence.
iff :: Parser (LFormula Name)
iff = do
  lhs <- imp
  asum [opLEquiv *> ((lhs .<=>.) <$> imp), pure lhs ]

-- | Parse a 'LemmaAttribute'.
lemmaAttribute :: Parser LemmaAttribute
lemmaAttribute = asum
  [ string "typing"        *> pure TypingLemma
  , string "reuse"         *> pure ReuseLemma
  , string "use_induction" *> pure InvariantLemma
  ]

-- | Parse a 'TraceQuantifier'.
traceQuantifier :: Parser TraceQuantifier
traceQuantifier = asum
  [ string "all"    *> opMinus *> string "traces" *> pure AllTraces
  , string "exists" *> opMinus *> string "trace"  *> pure ExistsTrace
  ]

-- | Parse a lemma.
lemma :: Parser (Lemma ProofSkeleton)
lemma = skeletonLemma <$> (string "lemma" *> optional moduloE *> identifier)
                      <*> (option [] $ list lemmaAttribute)
                      <*> (opColon *> option AllTraces traceQuantifier)
                      <*> doubleQuoted iff
                      <*> (proofSkeleton <|> pure (unproven ()))

-- | Builtin signatures.
builtins :: Parser ()
builtins =
    string "builtins" *> opColon *> commaSep1 builtinTheory *> pure ()
  where
    extendSig msig = modifyState (`mappend` msig)
    builtinTheory = asum
      [ try (string "diffie"     *> opMinus *> string "hellman")
          *> extendSig dhMaudeSig
      , try (string "symmetric"  *> opMinus *> string "encryption")
          *> extendSig symEncMaudeSig
      , try (string "asymmetric" *> opMinus *> string "encryption")
          *> extendSig asymEncMaudeSig
      , try (string "signing")
          *> extendSig signatureMaudeSig
      , string "hashing"
          *> extendSig hashMaudeSig
      ]

functions :: Parser ()
functions =
    string "functions" *> opColon *> commaSep1 functionSymbol *> pure ()
  where
    functionSymbol = do
        funsym <- (,) <$> (BC.pack <$> identifier) <*> (opSlash *> integer)
        sig <- getState
        case lookup (fst funsym) (S.toList $ allFunctionSymbols sig) of
          Just k | k /= snd funsym ->
            fail $ "conflicting arities " ++
                   show k ++ " and " ++ show (snd funsym) ++
                   " for `" ++ BC.unpack (fst funsym)
          _ -> setState (addFunctionSymbol funsym sig)

equations :: Parser ()
equations =
    string "equations" *> opColon *> commaSep1 equation *> pure ()
  where
    equation = do
        rrule <- RRule <$> term llit <*> (equalSign *> term llit)
        case rRuleToStRule rrule of
          Just str ->
              modifyState (addStRule str)
          Nothing  ->
              fail $ "Not a subterm rule: " ++ show rrule

------------------------------------------------------------------------------
-- Parsing Theories
------------------------------------------------------------------------------


-- | Parse a theory.
theory :: [String]   -- ^ Defined flags.
       -> Parser OpenTheory
theory flags0 = do
    string "theory"
    thyId <- identifier
    string "begin"
        *> addItems (S.fromList flags0) (set thyName thyId defaultOpenTheory)
        <* string "end"
  where
    addItems :: S.Set String -> OpenTheory -> Parser OpenTheory
    addItems flags thy = asum
      [ do builtins
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
      , do thy' <- liftedAddLemma thy =<< lemma
           addItems flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
           addItems flags thy'
      , do r <- intrRule
           addItems flags (addIntrRuleACs [r] thy)
      , do c <- formalComment
           addItems flags (addFormalComment c thy)
      , do ifdef flags thy
      , do define flags thy
      , do return thy
      ]

    define :: S.Set String -> OpenTheory -> Parser OpenTheory
    define flags thy = do
       flag <- try (opSharp *> string "define") *> identifier
       addItems (S.insert flag flags) thy

    ifdef :: S.Set String -> OpenTheory -> Parser OpenTheory
    ifdef flags thy = do
       flag <- try (opSharp *> string "ifdef") *> identifier
       thy' <- addItems flags thy
       try (opSharp *> string "endif")
       if flag `S.member` flags
         then addItems flags thy'
         else addItems flags thy

    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate rule: " ++ render (prettyRuleName ru)

    liftedAddLemma thy l = case addLemma l thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate lemma: " ++ get lName l
