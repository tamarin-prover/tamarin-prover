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
  , theory
  , diffTheory
  , parseLemma
  , parseRestriction
  , parseIntruderRules
  , liftedAddLemma
  , liftedAddProtoRule
  , liftedAddRestriction
  ) where

import           Prelude                    hiding (id, (.))
import           Data.Foldable              (asum)
import           Data.Label
import           Data.Maybe
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           System.FilePath
import           Control.Category
import           Control.Monad
import           Control.Applicative        hiding (empty, many, optional)
import qualified Control.Monad.Catch        as Catch
import System.IO.Unsafe (unsafePerformIO)
import           Text.Parsec                hiding ((<|>))
import           Text.PrettyPrint.Class     (render)
import           Theory
import           Theory.Text.Parser.Token

import           Theory.Text.Parser.Accountability
import           Theory.Text.Parser.Lemma
import           Theory.Text.Parser.Rule
import Theory.Text.Parser.Exceptions
import Theory.Text.Parser.Signature
import Theory.Text.Parser.Restriction
import Theory.Text.Parser.Sapic

------------------------------------------------------------------------------
-- Lexing and parsing theory files and proof methods
------------------------------------------------------------------------------

-- | Parse a security protocol theory file.
parseOpenTheory :: [String] -- ^ Defined flags
                -> FilePath
                -> IO OpenTheory
parseOpenTheory flags0 inFile = parseFile flags0 (theory (Just inFile)) inFile

-- | Parse a security protocol theory file.
parseOpenDiffTheory :: [String] -- ^ Defined flags
                -> FilePath
                -> IO OpenDiffTheory
parseOpenDiffTheory flags0 inFile = parseFile flags0 (diffTheory (Just inFile)) inFile


-- | Parse a security protocol theory from a string.
parseOpenTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> Either ParseError OpenTheory
parseOpenTheoryString flags0 = parseString flags0 "<unknown source>" (theory Nothing)

-- | Parse a security protocol theory from a string.
parseOpenDiffTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> Either ParseError OpenDiffTheory
parseOpenDiffTheoryString flags0 = parseString flags0 "<unknown source>" (diffTheory Nothing)

-- | Parse a lemma for an open theory from a string.
parseLemma :: String -> Either ParseError (SyntacticLemma ProofSkeleton)
parseLemma = parseString [] "<unknown source>" (lemma Nothing)

------------------------------------------------------------------------------
-- Parsing Theories
------------------------------------------------------------------------------

liftedExpandFormula :: Catch.MonadThrow m =>
                       Theory sig c r p s -> SyntacticLNFormula -> m LNFormula
liftedExpandFormula thy = liftEitherToEx UndefinedPredicate . expandFormula (theoryPredicates thy)

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

liftedAddAccLemma :: Catch.MonadThrow m => 
                     Theory sig c r p TranslationElement 
                     -> AccLemma -> m (Theory sig c r p TranslationElement)
liftedAddAccLemma thy lem =
   liftMaybeToEx (DuplicateItem $ TranslationItem $ AccLemmaItem lem) (addAccLemma lem thy)

liftedAddCaseTest :: Catch.MonadThrow m =>
                     Theory sig c r p TranslationElement
                     -> CaseTest -> m (Theory sig c r p TranslationElement)
liftedAddCaseTest thy cTest =
   liftMaybeToEx (DuplicateItem $ TranslationItem $ CaseTestItem cTest) (addCaseTest cTest thy)


-- | Add new protocol rule and introduce restrictions for _restrict contruct
--  1. expand syntactic restrict constructs
--  2. for each, chose fresh action and restriction name
--  3. add action names to rule
--  4. add rule, fail if duplicate
--  5. add restrictions, fail if duplicate
-- FIXME: we only deal we the rule modulo E here, if variants modulo AC are
--        imported we do not check if they have _restrict annotations
--        (but they should not, as they will not be exported)
liftedAddProtoRule :: Catch.MonadThrow m => OpenTheory -> OpenProtoRule -> m OpenTheory
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

-- | Flag formulas

data FlagFormula =
     FAtom String
   | FOr FlagFormula FlagFormula
   | FAnd FlagFormula FlagFormula
   | FNot FlagFormula

flagatom :: Parser FlagFormula
flagatom = FAtom <$> try identifier

-- | Parse a negation.
flagnegation :: Parser FlagFormula
flagnegation = opLNot *> (FNot <$> flagatom) <|> flagatom

-- | Parse a left-associative sequence of conjunctions.
flagconjuncts :: Parser FlagFormula
flagconjuncts = chainl1 flagnegation (FAnd <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
flagdisjuncts :: Parser FlagFormula
flagdisjuncts = chainl1 flagconjuncts (FOr <$ opLOr)

evalformula :: S.Set String -> FlagFormula -> Bool
evalformula flags0 (FAtom t) = S.member t flags0
evalformula flags0 (FNot t) = not (evalformula flags0 t)
evalformula flags0 (FOr t1 t2) = (evalformula flags0 t1) || (evalformula flags0 t2)
evalformula flags0 (FAnd t1 t2) = (evalformula flags0 t1) && (evalformula flags0 t2)

-- | Parse a theory.
theory :: Maybe FilePath
       -> Parser OpenTheory
theory inFile = do
    flags0 <- flags <$> getState
    when ("diff" `S.member` flags0) $ modifyStateSig (`mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    thy' <- symbol_ "begin"
        *> addItems inFile (set thyName thyId (defaultOpenTheory ("diff" `S.member` flags0)))
        <* symbol "end"
    return thy'
  where
    addItems :: Maybe FilePath -> OpenTheory -> Parser OpenTheory
    addItems inFile0 thy = asum
      [ do thy' <- liftedAddHeuristic thy =<< heuristic False workDir
           addItems inFile0 thy'
      , do thy' <- builtins thy
           msig <- sig <$> getState
           addItems inFile0 $ set (sigpMaudeSig . thySignature) msig thy'
      , do thy' <- options thy
           addItems inFile0 thy'      
      , do fs <- functions
           msig <- sig <$> getState
           let thy' = foldl (flip addFunctionTypingInfo) thy fs in           
             addItems inFile0 $ set (sigpMaudeSig . thySignature) msig thy'
      , do equations
           msig <- sig <$> getState
           addItems inFile0 $ set (sigpMaudeSig . thySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems flags thy'
      , do thy' <- liftedAddRestriction thy =<< restriction msgvar nodevar
           addItems inFile0 thy'
      , do thy' <- liftedAddRestriction thy =<< legacyAxiom
           addItems inFile0 thy'
           -- add legacy deprecation warning output
      , do test <- caseTest
           thy' <- liftedAddCaseTest thy test
           addItems inFile0 thy'
      , do accLem <- lemmaAcc workDir
           let tests = mapMaybe (flip lookupCaseTest $ thy) (get aCaseIdentifiers accLem)
           thy' <- liftedAddAccLemma thy (defineCaseTests accLem tests)
           addItems inFile0 thy'
      , do thy' <- liftedAddLemma thy =<< lemma workDir
           addItems inFile0 thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
           -- thy'' <- foldM liftedAddRestriction thy' $
           --  map (Restriction "name") [get (preRestriction . rInfo) ru]
           addItems inFile0 thy'
      , do r <- intrRule
           addItems inFile0 (addIntrRuleACs [r] thy)
      , do c <- formalComment
           addItems inFile0 (addFormalComment c thy)      
      , do procc <- toplevelprocess thy                          -- try parsing a process
           addItems inFile0 (addProcess procc thy)         -- add process to theoryitems and proceed parsing (recursive addItems call)
      , do thy' <- ((liftedAddProcessDef thy) =<<) (processDef thy)     -- similar to process parsing but in addition check that process with this name is only defined once (checked via liftedAddProcessDef)
           addItems inFile0 thy'
      , do
           lem <- equivLemma thy
           addItems inFile0 (modify thyItems (++ [TranslationItem lem]) thy)
      , do
           lem <- diffEquivLemma thy
           addItems inFile0 (modify thyItems (++ [TranslationItem lem]) thy)
      , do thy' <- preddeclaration thy
           addItems inFile0 (thy')
      , do thy'  <- export thy
           addItems inFile0 (thy')
      , do ifdef inFile0 thy
      , do define inFile0 thy
      , do include inFile0 thy      
      , do return thy
      ]
      where workDir = (takeDirectory <$> inFile0)
    define inFile0 thy = do
       flag <- try (symbol "#define") *> identifier
       modifyStateFlag (S.insert flag)
       addItems inFile0 thy


    include :: Maybe FilePath -> OpenTheory -> Parser OpenTheory
    include inFile0 thy = do
         filepath <- try (symbol "#include") *> filePathParser
         st <- getState
         let (thy', st') = unsafePerformIO (parseFileWState st (addItems' (Just filepath) thy) filepath)
         _ <- putState st'
         addItems inFile0 $ set (sigpMaudeSig . thySignature) (sig st') thy'
      where
        addItems' :: Maybe FilePath -> OpenTheory -> Parser (OpenTheory, ParserState)
        addItems' inFile1 thy1 = do
             thy' <- addItems inFile1 thy1
             st <- getState
             return (thy', st)

        filePathParser = case takeDirectory <$> inFile0 of
              Nothing -> do
                x <- doubleQuoted filePath
                return (x <> [pathSeparator])
              Just s ->  do
                x <- doubleQuoted filePath
                return (s </> x)

    ifdef :: Maybe FilePath -> OpenTheory ->  Parser OpenTheory
    ifdef inFile0 thy = do
       flagf <- symbol_ "#ifdef" *> flagdisjuncts
       flags0 <- flags <$> getState
       if evalformula flags0 flagf
         then do thy' <- addItems inFile0 thy
                 asum [do symbol_ "#else"
                          _ <- manyTill anyChar (try (symbol_ "#endif"))
                          addItems inFile0 thy'
                       ,do symbol_ "#endif"
                           addItems inFile0 thy'
                      ]

         else parseelse
         where
           parseelse =
             do _ <- manyTill anyChar (try (symbol_ "#"))
                asum
                 [do (symbol_ "else")
                     thy' <- addItems inFile0 thy
                     symbol_ "#endif"
                     addItems inFile0 thy'
                 ,do _ <- symbol_ "endif"
                     addItems inFile0 thy
                 , parseelse
                 ]

    -- check process defined only once
    -- add process to theoryitems
    liftedAddProcessDef thy pDef = case addProcessDef pDef thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate process: " ++ get pName pDef

    liftedAddHeuristic thy h = case addHeuristic h thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "default heuristic already defined"

-- | Parse a diff theory.
diffTheory :: Maybe FilePath
       -> Parser OpenDiffTheory
diffTheory inFile = do
    flags0 <- flags <$> getState
    modifyStateSig (`mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    thy' <- symbol_ "begin"
        *> addItems inFile (set diffThyName thyId (defaultOpenDiffTheory ("diff" `S.member` flags0)))
        <* symbol "end"
    return thy'
  where
    addItems :: Maybe FilePath -> OpenDiffTheory -> Parser OpenDiffTheory
    addItems inFile0 thy = asum
      [ do thy' <- liftedAddHeuristic thy =<< heuristic True workDir
           addItems inFile0 thy'
      , do
           diffbuiltins
           msig <- sig <$> getState
           addItems inFile0 $ set (sigpMaudeSig . diffThySignature) msig thy           
      , do _ <- functions -- typing affects only SAPIC translation, hence functions
                          -- are only added to maude signature, but not to theory.
           msig <- sig <$> getState
           addItems inFile0 $ set (sigpMaudeSig . diffThySignature) msig thy
      , do equations
           msig <- sig <$> getState
           addItems inFile0 $ set (sigpMaudeSig . diffThySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems inFile0 thy'
      , do thy' <- liftedAddRestriction' thy =<< diffRestriction
           addItems inFile0 thy'
      , do thy' <- liftedAddRestriction' thy =<< legacyDiffAxiom
           addItems inFile0 thy'
           -- add legacy deprecation warning output
      , do thy' <- liftedAddLemma' thy =<< plainLemma workDir
           addItems inFile0 thy'
      , do thy' <- liftedAddDiffLemma thy =<< diffLemma workDir
           addItems inFile0 thy'
      , do ru <- diffRule
           thy' <- liftedAddDiffRule thy ru
           addItems inFile0 thy'
      , do r <- intrRule
           addItems inFile0 (addIntrRuleACsDiffAll [r] thy)
      , do c <- formalComment
           addItems inFile0 (addFormalCommentDiff c thy)
      , do ifdef inFile0 thy
      , do define inFile0 thy
      , do include inFile0 thy
      , do return thy
      ]
      where  workDir = takeDirectory <$> inFile

    define :: Maybe FilePath -> OpenDiffTheory -> Parser OpenDiffTheory
    define inFile0 thy = do
       flag <- try (symbol "#define") *> identifier
       modifyStateFlag (S.insert flag)
       addItems inFile0 thy

    ifdef :: Maybe FilePath -> OpenDiffTheory ->  Parser OpenDiffTheory
    ifdef inFile0 thy = do
       flagf <- symbol_ "#ifdef" *> flagdisjuncts
       flags0 <- flags <$> getState
       if evalformula flags0 flagf
         then do thy' <- addItems inFile0 thy
                 asum [do symbol_ "#else"
                          _ <- manyTill anyChar (try (symbol_ "#endif"))
                          addItems inFile0 thy'
                       ,do symbol_ "#endif"
                           addItems inFile0 thy'
                      ]

         else parseelse
         where
           parseelse =
             do _ <- manyTill anyChar (try (symbol_ "#"))
                asum
                 [do (symbol_ "else")
                     thy' <- addItems inFile0 thy
                     symbol_ "#endif"
                     addItems inFile0 thy'
                 ,do _ <- symbol_ "endif"
                     addItems inFile0 thy
                 , parseelse
                 ]

    include :: Maybe FilePath -> OpenDiffTheory -> Parser OpenDiffTheory
    include inFile0 thy = do
         filepath <- try (symbol "#include") *> filePathParser
         st <- getState
         let (thy', st') = unsafePerformIO (parseFileWState st (addItems' (Just filepath) thy) filepath)
         _ <- putState st'
         addItems inFile0 $ set (sigpMaudeSig . diffThySignature) (sig st') thy'
      where
        addItems' :: Maybe FilePath -> OpenDiffTheory -> Parser (OpenDiffTheory, ParserState)
        addItems' inFile1 thy1 = do
             thy' <- addItems inFile1 thy1
             st' <- getState
             return (thy', st')

        filePathParser = case takeDirectory <$> inFile0 of
              Nothing -> do
                x <- doubleQuoted filePath
                return (x <> [pathSeparator])
              Just s ->  do
                x <- doubleQuoted filePath
                return (s </> x)


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
