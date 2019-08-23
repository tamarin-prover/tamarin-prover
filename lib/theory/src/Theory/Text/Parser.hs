{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
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
  ) where

import           Prelude                    hiding (id, (.))

import qualified Data.ByteString            as B
import qualified Data.ByteString.Char8      as BC
import           Data.Char                  (isUpper, toUpper)
import           Data.Foldable              (asum)
import           Data.Label
import qualified Data.Map                   as M
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import qualified Data.Text                  as T
import qualified Data.Text.Encoding         as TE
-- import qualified Data.List                  as L
import           Data.Color

import           Control.Applicative        hiding (empty, many, optional)
import           Control.Category
import           Control.Monad
import qualified Control.Monad.Catch        as Catch

import           Text.Parsec                hiding ((<|>))
import           Text.PrettyPrint.Class     (render)

-- import           System.Process

-- import qualified Extension.Data.Label       as L

import           Term.Substitution
import           Term.SubtermRule
import           Theory
import           Theory.Sapic
import           Theory.Text.Parser.Token

import           Debug.Trace

import Data.Functor.Identity 

------------------------------------------------------------------------------
-- ParseRestriction datatype and functions to parse diff restrictions
------------------------------------------------------------------------------

-- | A restriction describes a property that must hold for all traces. Restrictions are
-- always used as lemmas in proofs.
data ParseRestriction = ParseRestriction
       { pRstrName       :: String
       , pRstrAttributes :: [RestrictionAttribute]
       , pRstrFormula    :: LNFormula
       }
       deriving( Eq, Ord, Show )


-- | True iff the restriction is a LHS restriction.
isLeftRestriction :: ParseRestriction -> Bool
isLeftRestriction rstr =
     (LHSRestriction `elem` pRstrAttributes rstr)

-- | True iff the restriction is a RHS restriction.
isRightRestriction :: ParseRestriction -> Bool
isRightRestriction rstr =
     (RHSRestriction `elem` pRstrAttributes rstr)

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
parseOpenTheory flags file = do 
          parseFile (theory flags) file

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
parseLemma :: String -> Either ParseError (Lemma ProofSkeleton)
parseLemma = parseString "<unknown source>" lemma

-- | Parse a lemma for an open theory from a string.
parseRestriction :: String -> Either ParseError Restriction
parseRestriction = parseString "<unknown source>" restriction

------------------------------------------------------------------------------
-- Parsing Terms
------------------------------------------------------------------------------

-- | Parse an lit with logical variables.
llit :: Parser LNTerm
llit = asum [freshTerm <$> freshName, pubTerm <$> pubName, varTerm <$> msgvar]

-- | Parse an lit with logical variables without public names in single constants.
llitNoPub :: Parser LNTerm
llitNoPub = asum [freshTerm <$> freshName, varTerm <$> msgvar]

-- | Parse an lit with logical typed variables for SAPIC
ltypedlit :: Parser SapicTerm
ltypedlit = asum [freshTerm <$> freshName, pubTerm <$> pubName, varTerm <$> sapicvar]

-- | Lookup the arity of a non-ac symbol. Fails with a sensible error message
-- if the operator is not known.
lookupArity :: String -> Parser (Int, Privacy)
lookupArity op = do
    maudeSig <- getState
    case lookup (BC.pack op) (S.toList (noEqFunSyms maudeSig) ++ [(emapSymString, (2,Public))]) of
        Nothing    -> fail $ "unknown operator `" ++ op ++ "'"
        Just (k,priv) -> return (k,priv)

-- | Parse an n-ary operator application for arbitrary n.
naryOpApp :: Ord l => Parser (Term l) -> Parser (Term l)
naryOpApp plit = do
    op <- identifier
    (k,priv) <- lookupArity op
    ts <- parens $ if k == 1
                     then return <$> tupleterm plit
                     else commaSep (msetterm plit)
    let k' = length ts
    when (k /= k') $
        fail $ "operator `" ++ op ++"' has arity " ++ show k ++
               ", but here it is used with arity " ++ show k'
    let app o = if BC.pack op == emapSymString then fAppC EMap else fAppNoEq o
    return $ app (BC.pack op, (k,priv)) ts

-- | Parse a binary operator written as @op{arg1}arg2@.
binaryAlgApp :: Ord l => Parser (Term l) -> Parser (Term l)
binaryAlgApp plit = do
    op <- identifier
    (k,priv) <- lookupArity op
    arg1 <- braced (tupleterm plit)
    arg2 <- term plit False
    when (k /= 2) $ fail $
      "only operators of arity 2 can be written using the `op{t1}t2' notation"
    return $ fAppNoEq (BC.pack op, (2,priv)) [arg1, arg2]

diffOp :: Ord l => Bool -> Parser (Term l) -> Parser (Term l)
diffOp eqn plit = do
  ts <- symbol "diff" *> parens (commaSep (msetterm plit))
  when (2 /= length ts) $ fail $
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
term :: Ord l => Parser (Term l) -> Bool -> Parser (Term l)
term plit eqn = asum
    [ pairing       <?> "pairs"
    , parens (msetterm plit)
    , symbol "1" *> pure fAppOne
    , application <?> "function application"
    , nullaryApp
    , plit
    ]
    <?> "term"
  where
    application = asum $ map (try . ($ plit)) [naryOpApp, binaryAlgApp, diffOp eqn]
    pairing = angled (tupleterm plit)
    nullaryApp = do
      maudeSig <- getState
      -- FIXME: This try should not be necessary.
      asum [ try (symbol (BC.unpack sym)) *> pure (fApp (NoEq (sym,(0,priv))) [])
           | NoEq (sym,(0,priv)) <- S.toList $ funSyms maudeSig ]

-- | A left-associative sequence of exponentations.
expterm :: Ord l => Parser (Term l) -> Parser (Term l)
expterm plit = chainl1 (term plit False) ((\a b -> fAppExp (a,b)) <$ opExp)

-- | A left-associative sequence of multiplications.
multterm :: Ord l => Parser (Term l) -> Parser (Term l)
multterm plit = do
    dh <- enableDH <$> getState
    if dh -- if DH is not enabled, do not accept 'multterm's and 'expterm's
        then chainl1 (expterm plit) ((\a b -> fAppAC Mult [a,b]) <$ opMult)
        else term plit False

-- | A left-associative sequence of xors.
xorterm :: Ord l => Parser (Term l) -> Parser (Term l)
xorterm plit = do
    xor <- enableXor <$> getState
    if xor -- if xor is not enabled, do not accept 'xorterms's
        then chainl1 (multterm plit) ((\a b -> fAppAC Xor [a,b]) <$ opXor)
        else multterm plit

-- | A left-associative sequence of multiset unions.
msetterm :: Ord l => Parser (Term l) -> Parser (Term l)
msetterm plit = do
    mset <- enableMSet <$> getState
    if mset -- if multiset is not enabled, do not accept 'msetterms's
        then chainl1 (xorterm plit) ((\a b -> fAppAC Union [a,b]) <$ opPlus)
        else xorterm plit

-- | A right-associative sequence of tuples.
tupleterm :: Ord l => Parser (Term l) -> Parser (Term l)
tupleterm plit = chainr1 (msetterm plit) ((\a b -> fAppPair (a,b)) <$ comma)

-- | Parse a fact annotation
factAnnotation :: Parser FactAnnotation
factAnnotation = asum
  [ opPlus  *> pure SolveFirst
  , opMinus *> pure SolveLast
  , symbol "no_precomp" *> pure NoSources
  ]

-- | Parse a fact.
fact :: Ord l => Parser (Term l) -> Parser (Fact (Term l))
fact plit = try (
    do multi <- option Linear (opBang *> pure Persistent)
       i     <- identifier
       case i of
         []                -> fail "empty identifier"
         (c:_) | isUpper c -> return ()
               | otherwise -> fail "facts must start with upper-case letters"
       ts    <- parens (commaSep (msetterm plit))
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


------------------------------------------------------------------------------
-- Parsing Rules
------------------------------------------------------------------------------

-- | Parse a "(modulo ..)" information.
modulo :: String -> Parser ()
modulo thy = parens $ symbol_ "modulo" *> symbol_ thy

moduloE, moduloAC :: Parser ()
moduloE  = modulo "E"
moduloAC = modulo "AC"

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
protoRuleInfo = (ProtoRuleEInfo <$> (StandRule <$>
                                        (symbol "rule" *> optional moduloE *> identifier))
                               <*> (option [] $ list ruleAttribute)) <*  colon

-- | Parse a protocol rule. For the special rules 'Reveal_fresh', 'Fresh',
-- 'Knows', and 'Learn' no rule is returned as the default theory already
-- contains them.
protoRule :: Parser (ProtoRuleE)
protoRule = do
    ri@(ProtoRuleEInfo (StandRule name) _)  <- try protoRuleInfo
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst $ letBlock 
    (ps0,as0,cs0) <- genericRule llit
    let (ps,as,cs) = apply subst (ps0,as0,cs0)
    return $ Rule ri ps cs as (newVariables ps cs)

-- | Parse a let block with bottom-up application semantics.
-- genericletBlock :: Parser (Term (Lit c v)) -> Parser (Subst c v)
genericletBlock :: (IsConst c, IsVar v) => Parser (Term (Lit c v)) -> Parser
    v -> Parser (Subst c v)
genericletBlock litp varp = do
    toSubst <$> (symbol "let" *> many1 definition <* symbol "in")
  where
    toSubst = foldr1 compose . map (substFromList . return)
    definition = (,) <$> (varp <* equalSign) <*> msetterm litp


letBlock :: Parser LNSubst
letBlock = genericletBlock llit (sortedLVar [LSortMsg])

-- | Parse an intruder rule.
intrRule :: Parser IntrRuleAC
intrRule = do
    info <- try (symbol "rule" *> moduloAC *> intrInfo <* colon)
    (ps,as,cs) <- genericRule llit
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

genericRule :: Ord l => Parser (Term l) -> Parser ([Fact (Term l)], [Fact (Term l)], [Fact (Term l)])
genericRule lit =
    (,,) <$> list (fact lit)
         <*> ((pure [] <* symbol "-->") <|>
              (symbol "--[" *> commaSep (fact lit) <* symbol "]->"))
         <*> list (fact lit)

newVariables :: [LNFact] -> [LNFact] -> [LNTerm]
newVariables prems concs = map varTerm $ S.toList newvars
  where
    newvars = S.difference concvars premvars
    premvars = S.fromList $ concat $ map getFactVariables prems
    concvars = S.fromList $ concat $ map getFactVariables concs

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
blatom :: Parser BLAtom
blatom = (fmap (fmapTerm (fmap Free))) <$> asum
  [ Last        <$> try (symbol "last" *> parens nodevarTerm)        <?> "last atom"
  , flip Action <$> try (fact llit <* opAt)        <*> nodevarTerm   <?> "action atom"
  , Less        <$> try (nodevarTerm <* opLess)    <*> nodevarTerm   <?> "less atom"
  , EqE         <$> try (msetterm llit <* opEqual) <*> msetterm llit <?> "term equality"
  , EqE         <$>     (nodevarTerm  <* opEqual)  <*> nodevarTerm   <?> "node equality"
  ]
  where
    nodevarTerm = (lit . Var) <$> nodevar

-- | Parse an atom of a formula.
fatom :: Parser LNFormula
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
negation :: Parser LNFormula
negation = opLNot *> (Not <$> fatom) <|> fatom

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser LNFormula
conjuncts = chainl1 negation ((.&&.) <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser LNFormula
disjuncts = chainl1 conjuncts ((.||.) <$ opLOr)

-- | An implication.
imp :: Parser LNFormula
imp = do
  lhs <- disjuncts
  asum [ opImplies *> ((lhs .==>.) <$> imp)
       , pure lhs ]

-- | An logical equivalence.
iff :: Parser LNFormula
iff = do
  lhs <- imp
  asum [opLEquiv *> ((lhs .<=>.) <$> imp), pure lhs ]

-- | Parse a standard formula.
standardFormula :: Parser LNFormula
standardFormula = iff

-- | Parse a guarded formula using the hack of parsing a standard formula and
-- converting it afterwards.
--
-- FIXME: Write a proper parser.
guardedFormula :: Parser LNGuarded
guardedFormula = try $ do
    res <- formulaToGuarded <$> standardFormula
    case res of
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
restriction :: Parser Restriction
restriction = Restriction <$> (symbol "restriction" *> identifier <* colon)
                          <*> doubleQuoted standardFormula

-- | Fail on parsing an old "axiom" keyword.
--legacyAxiom :: Parser Restriction
--legacyAxiom = symbol "axiom" *> fail "Using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'."

-- | Parse a legacy axiom, now called restriction.
legacyAxiom :: Parser Restriction
legacyAxiom = trace ("Deprecation Warning: using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'.") Restriction <$> (symbol "axiom" *> identifier <* colon)
                          <*> doubleQuoted standardFormula

-- | Parse a diff restriction.
diffRestriction :: Parser ParseRestriction
diffRestriction = ParseRestriction <$> (symbol "restriction" *> identifier)
                    <*> (option [] $ list restrictionAttribute)
                    <*> (colon *> doubleQuoted standardFormula)

-- | Fail on parsing an old "axiom" keyword.
--legacyDiffAxiom :: Parser ParseRestriction
--legacyDiffAxiom = symbol "axiom" *> fail "Using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'."

-- | Parse a legacy diff axiom, now called restriction. Emits warning.
legacyDiffAxiom :: Parser ParseRestriction
legacyDiffAxiom = trace ("Deprecation Warning: using 'axiom' is retired notation, replace all uses of 'axiom' by 'restriction'.") ParseRestriction <$> (symbol "axiom" *> identifier)
              <*> (option [] $ list restrictionAttribute)
              <*> (colon *> doubleQuoted standardFormula)

------------------------------------------------------------------------------
-- Parsing Lemmas
------------------------------------------------------------------------------

-- | Parse a 'LemmaAttribute'.
lemmaAttribute :: Bool -> Parser LemmaAttribute
lemmaAttribute isDiff = asum
  [ symbol "typing"        *> trace ("Deprecation Warning: using 'typing' is retired notation, replace all uses of 'typing' by 'sources'.\n") pure SourceLemma -- legacy support, emits deprecation warning
--  , symbol "typing"        *> fail "Using 'typing' is retired notation, replace all uses of 'typing' by 'sources'."
  , symbol "sources"       *> pure SourceLemma
  , symbol "reuse"         *> pure ReuseLemma
  , symbol "use_induction" *> pure InvariantLemma
  , symbol "hide_lemma="   *> (HideLemma <$> identifier)
  , symbol "heuristic="    *> (LemmaHeuristic <$> parseGoalRanking)
  , symbol "left"          *> pure LHSLemma
  , symbol "right"         *> pure RHSLemma
--   , symbol "both"          *> pure BothLemma
  ]
  where
    parseGoalRanking = case isDiff of
        True  -> map charToGoalRankingDiff <$> many1 letter
        False -> map charToGoalRanking     <$> many1 letter

-- | Parse a 'TraceQuantifier'.
traceQuantifier :: Parser TraceQuantifier
traceQuantifier = asum
  [ symbol "all-traces" *> pure AllTraces
  , symbol "exists-trace"  *> pure ExistsTrace
  ]

-- | Parse a lemma.
lemma :: Parser (Lemma ProofSkeleton)
lemma = skeletonLemma <$> (symbol "lemma" *> optional moduloE *> identifier)
                      <*> (option [] $ list (lemmaAttribute False))
                      <*> (colon *> option AllTraces traceQuantifier)
                      <*> doubleQuoted standardFormula
                      <*> (proofSkeleton <|> pure (unproven ()))

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


functions :: Parser ()
functions =
    symbol "functions" *> colon *> commaSep1 functionSymbol *> pure ()
  where
    functionSymbol = do
        f   <- BC.pack <$> identifier <* opSlash
        k   <- fromIntegral <$> natural
        priv <- option Public (symbol "[private]" *> pure Private)
        if (BC.unpack f `elem` ["mun", "one", "exp", "mult", "inv", "pmult", "em", "zero", "xor"])
          then fail $ "`" ++ BC.unpack f ++ "` is a reserved function name for builtins."
          else return ()
        sig <- getState
        case lookup f [ o | o <- (S.toList $ stFunSyms sig)] of
          Just kp' | kp' /= (k,priv) ->
            fail $ "conflicting arities/private " ++
                   show kp' ++ " and " ++ show (k,priv) ++
                   " for `" ++ BC.unpack f
          _ -> setState (addFunSym (f,(k,priv)) sig)

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
           f <- fact llit
           _ <- symbol "<=>"
           form <- standardFormula
           return $ Predicate f form

preddeclaration :: OpenTheory -> Parser OpenTheory
preddeclaration thy = do
                    _          <- symbol "predicates"
                    _          <- colon
                    predicates <- commaSep1 predicate
                    thy'       <-  foldM liftedAddPredicate thy predicates
                    return thy'
                where 
                liftedAddPredicate thy pr  = 
                    case addPredicate pr thy of 
                        (Just thy') -> return (thy'::OpenTheory)
                        Nothing     -> fail $ "duplicate predicate: " ++ (render $ prettyLNFact (get pFact pr))

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
                        s <- sapicvar 
                        return (New s)
                   )
               <|> try (do 
                        _ <- symbol "in"
                        _ <- symbol "("
                        t <- msetterm ltypedlit
                        _ <- symbol ")"
                        return (ChIn Nothing t)
                   )
               <|> try (do 
                        _ <- symbol "in"
                        _ <- symbol "("
                        t <- msetterm ltypedlit
                        _ <- comma
                        t' <- msetterm ltypedlit
                        _ <- symbol ")"
                        return (ChIn (Just t) t')
                   )
               <|> try (do 
                        _ <- symbol "out"
                        _ <- symbol "("
                        t <- msetterm ltypedlit
                        _ <- symbol ")"
                        return (ChOut Nothing t)
                   )
               <|> try (do 
                        _ <- symbol "out"
                        _ <- symbol "("
                        t <- msetterm ltypedlit
                        _ <- comma
                        t' <- msetterm ltypedlit
                        _ <- symbol ")"
                        return (ChOut (Just t) t')
                   )
               <|> try (do 
                        _ <- symbol "insert"
                        t <- msetterm ltypedlit
                        _ <- comma
                        t' <- msetterm ltypedlit
                        return (Insert t t')
                   )
               <|> try (do 
                        _ <- symbol "delete"
                        t <- msetterm ltypedlit
                        return (Delete t)
                   )
               <|> try (do 
                        _ <- symbol "lock"
                        t <- msetterm ltypedlit
                        return (Lock t)
                   )
               <|> try (do 
                        _ <- symbol "unlock"
                        t <- msetterm ltypedlit
                        return (Unlock t)
                   )
               <|> try (do 
                        _ <- symbol "event"
                        f <- fact ltypedlit
                        return (Event f)
                   )
               <|> try (do 
                        r <- genericRule ltypedlit
                        return (MSR r)
                   )
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
                        p <- actionprocess thy
                        _ <- symbol ")"
                        _ <- symbol "@"
                        m <- msetterm ltypedlit
                        case Catch.catch (applyProcess (substFromList [(SapicLVar (LVar "_loc_" LSortMsg 0) defaultSapicType,m)]) p) (fail . prettyLetExceptions) of 
                            (Left err) -> fail $ show err -- Should never occur, we handle everything above
                            (Right p') -> return p'
                        )
            <|>    try  (do -- parens parser
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        return p)
            <|>    try  (do -- let expression parser
                        subst <- genericletBlock ltypedlit sapicvar
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
                        t <- msetterm ltypedlit
                        _ <- symbol "as"
                        v <- sapicvar
                        _ <- symbol "in"
                        p <- process thy
                        _ <- symbol "else"
                        q <- process thy
                        return (ProcessComb (Lookup t v) mempty p q)
                   )
            <|> try (do 
                        _ <- symbol "lookup"
                        t <- msetterm ltypedlit
                        _ <- symbol "as"
                        v <- sapicvar
                        _ <- symbol "in"
                        p <- process thy
                        return (ProcessComb (Lookup t v) mempty p (ProcessNull mempty))
                   )
            <|> try (do 
                        _ <- symbol "if"
                        t1 <- msetterm ltypedlit
                        _ <- opEqual
                        t2 <- msetterm ltypedlit
                        _ <- symbol "then"
                        p <- process thy
                        _ <- symbol "else"
                        q <- process thy
                        return (ProcessComb (CondEq t1 t2  ) mempty p q)
                   )
            <|> try (do 
                        _ <- symbol "if"
                        pr <- fact ltypedlit
                        _ <- symbol "then"
                        p <- process thy
                        _ <- symbol "else"
                        q <- process thy
                        return (ProcessComb (Cond pr) mempty p q)
                   )
            <|> try (do 
                        _ <- symbol "if"
                        t1 <- msetterm ltypedlit
                        _ <- opEqual
                        t2 <- msetterm ltypedlit
                        _ <- symbol "then"
                        p <- process thy
                        return (ProcessComb (CondEq t1 t2  ) mempty p (ProcessNull mempty))
                   )
            <|> try (do 
                        _ <- symbol "if"
                        pr <- fact ltypedlit
                        _ <- symbol "then"
                        p <- process thy
                        return (ProcessComb (Cond pr) mempty p (ProcessNull mempty))
                   )
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
                            (\x -> paddAnn x [BC.unpack i]) <$> p
                        return a 
                        )
            <|>    try  (do -- let expression parser
                        subst <- genericletBlock ltypedlit sapicvar
                        p     <- process thy
                        case Catch.catch (applyProcess subst p) (\ e  -> fail $ prettyLetExceptions e) of 
                            (Left err) -> fail $ show err -- Should never occur, we handle everything above
                            (Right p') -> return p'
                        )
            <|> do        -- parens parser
                        _ <- symbol "("
                        p <- process thy
                        _ <- symbol ")"
                        return p
                        

heuristic :: Bool -> Parser [GoalRanking]
heuristic isDiff = do
      symbol "heuristic" *> colon *> parseGoalRanking
  where
    parseGoalRanking = case isDiff of
        True  -> map charToGoalRankingDiff <$> identifier
        False -> map charToGoalRanking     <$> identifier

------------------------------------------------------------------------------
-- Parsing Theories
------------------------------------------------------------------------------


-- checks if process exists, if not -> error
-- checkProcess :: String -> OpenTheory -> Parser OpenTheory
-- checkProcess i thy= case findProcess i thy of
--     Just thy' -> return thy
--     Nothing -> fail $ "process not defined: " ++ i    
checkProcess :: String -> OpenTheory -> Parser Process
checkProcess i thy = case lookupProcessDef i thy of
    Just p -> return $ get pBody p
    Nothing -> fail $ "process not defined: " ++ i    

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
      , do thy' <- ((liftedAddLemma thy) =<<) lemma
           addItems flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
           addItems flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
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

    define :: S.Set String -> OpenTheory -> Parser OpenTheory
    define flags thy = do
       flag <- try (symbol "#define") *> identifier
       addItems (S.insert flag flags) thy

    ifdef :: S.Set String -> OpenTheory -> Parser OpenTheory
    ifdef flags thy = do
       flag <- symbol_ "#ifdef" *> identifier
       thy' <- addItems flags thy
       symbol_ "#endif"
       if flag `S.member` flags
         then addItems flags thy'
         else addItems flags thy

    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate rule: " ++ render (prettyRuleName ru)

    liftedAddLemma thy lem = case addLemma lem thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate lemma: " ++ get lName lem 

    -- check process defined only once
    -- add process to theoryitems
    liftedAddProcessDef thy pDef = case addProcessDef pDef thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate process: " ++ get pName pDef 

    liftedAddRestriction thy rstr = case addRestriction rstr thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate restriction: " ++ get rstrName rstr

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
      , do thy' <- liftedAddRestriction thy =<< diffRestriction
           addItems flags thy'
      , do thy' <- liftedAddRestriction thy =<< legacyDiffAxiom
           addItems flags thy'
           -- add legacy deprecation warning output
      , do thy' <- liftedAddLemma thy =<< lemma
           addItems flags thy'
      , do thy' <- liftedAddDiffLemma thy =<< diffLemma
           addItems flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
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
       thy' <- addItems flags thy
       symbol_ "#endif"
       if flag `S.member` flags
         then addItems flags thy'
         else addItems flags thy

    liftedAddHeuristic thy h = case addDiffHeuristic h thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "default heuristic already defined"

    liftedAddProtoRule thy ru = case addProtoDiffRule ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate rule: " ++ render (prettyRuleName ru)

    liftedAddDiffLemma thy ru = case addDiffLemma ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate Diff Lemma: " ++ render (prettyDiffLemmaName ru)
        
    liftedAddLemma thy lem = if isLeftLemma lem
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

    liftedAddRestriction thy rstr = if isLeftRestriction rstr
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
