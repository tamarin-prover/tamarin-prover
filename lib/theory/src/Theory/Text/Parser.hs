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
  , liftedAddProtoRule
  , liftedAddRestriction
  ) where

import           Prelude                    hiding (id, (.))
import           Data.Foldable              (asum)
import           Data.Label
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           System.FilePath
import           Control.Category
import           Control.Monad
import qualified Control.Monad.Catch        as Catch
import System.IO.Unsafe (unsafePerformIO)
import           Text.Parsec                hiding ((<|>))
import           Text.PrettyPrint.Class     (render)
import           Theory
import           Theory.Text.Parser.Token

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
parseOpenTheory flags inFile = parseFile (theory flags (Just inFile)) inFile

-- | Parse a security protocol theory file.
parseOpenDiffTheory :: [String] -- ^ Defined flags
                -> FilePath
                -> IO OpenDiffTheory
parseOpenDiffTheory flags inFile = parseFile (diffTheory flags (Just inFile)) inFile


-- | Parse a security protocol theory from a string.
parseOpenTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> Either ParseError OpenTheory
parseOpenTheoryString flags = parseString "<unknown source>" (theory flags Nothing)

-- | Parse a security protocol theory from a string.
parseOpenDiffTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> Either ParseError OpenDiffTheory
parseOpenDiffTheoryString flags = parseString "<unknown source>" (diffTheory flags Nothing)

-- | Parse a lemma for an open theory from a string.
parseLemma :: String -> Either ParseError (SyntacticLemma ProofSkeleton)
parseLemma = parseString "<unknown source>" (lemma Nothing)

------------------------------------------------------------------------------
-- Parsing Theories
------------------------------------------------------------------------------


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

-- | Parse a theory.
theory :: [String]   -- ^ Defined flags.
       -> Maybe FilePath
       -> Parser OpenTheory
theory flags0 inFile = do
    msig <- getState
    when ("diff" `S.member` (S.fromList flags0)) $ putState (msig `mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    (thy', _) <- symbol_ "begin"
        *> addItems inFile (S.fromList flags0) (set thyName thyId (defaultOpenTheory ("diff" `S.member` (S.fromList flags0))))
        <* symbol "end"
    return thy'
  where
    addItems :: Maybe FilePath -> S.Set String -> OpenTheory -> Parser (OpenTheory, S.Set String)
    addItems inFile0 flags thy = asum
      [ do thy' <- liftedAddHeuristic thy =<< heuristic False workDir
           addItems inFile0 flags thy'
      , do thy' <- builtins thy
           msig <- getState
           addItems inFile0 flags $ set (sigpMaudeSig . thySignature) msig thy'
      , do thy' <- options thy
           addItems inFile0 flags thy'
      , do functions
           msig <- getState
           addItems inFile0 flags $ set (sigpMaudeSig . thySignature) msig thy
      , do equations
           msig <- getState
           addItems inFile0 flags $ set (sigpMaudeSig . thySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems inFile0 flags thy'
      , do thy' <- liftedAddRestriction thy =<< restriction
           addItems inFile0 flags thy'
      , do thy' <- liftedAddRestriction thy =<< legacyAxiom
           addItems inFile0 flags thy'
           -- add legacy deprecation warning output
      , do thy' <- liftedAddLemma thy =<< lemma workDir
           addItems inFile0 flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
           -- thy'' <- foldM liftedAddRestriction thy' $
           --  map (Restriction "name") [get (preRestriction . rInfo) ru]
           addItems inFile0 flags thy'
      , do r <- intrRule
           addItems inFile0 flags (addIntrRuleACs [r] thy)
      , do c <- formalComment
           addItems inFile0 flags (addFormalComment c thy)
      , do procc <- process thy                          -- try parsing a process
           addItems inFile0 flags (addProcess procc thy)         -- add process to theoryitems and proceed parsing (recursive addItems inFile0 call)
      , do thy' <- ((liftedAddProcessDef thy) =<<) (processDef thy)     -- similar to process parsing but in addition check that process with this name is only defined once (checked via liftedAddProcessDef)
           addItems inFile0 flags thy'
      , do thy' <- preddeclaration thy
           addItems inFile0 flags (thy')
      , do ifdef inFile0 flags thy
      , do define inFile0 flags thy
      , do include inFile0 flags thy
      , do return (thy, flags)
      ]
      where workDir = (takeDirectory <$> inFile0)
    define inFile0 flags thy = do
       flag <- try (symbol "#define") *> identifier
       addItems inFile0 (S.insert flag flags) thy


    include :: Maybe FilePath -> S.Set String -> OpenTheory -> Parser  (OpenTheory, S.Set String)
    include inFile0 flags thy = do
         filepath <- try (symbol "#include") *> filePathParser
         msig <- getState
         let (thy', flags', sig') = unsafePerformIO (parseFileWState msig (addItems' (Just filepath) flags thy) filepath)
         _ <- putState sig'
         addItems inFile0 flags' $ set (sigpMaudeSig . thySignature) sig' thy'
      where
        addItems' :: Maybe FilePath -> S.Set String -> OpenTheory -> Parser (OpenTheory, S.Set String, MaudeSig)
        addItems' inFile1 flags1 thy1 = do
             (thy',fl') <- addItems inFile1 flags1 thy1
             msig <- getState
             return (thy', fl', msig)

        filePathParser = case takeDirectory <$> inFile0 of
              Nothing -> do
                x <- doubleQuoted filePath
                return (x <> [pathSeparator])
              Just s ->  do
                x <- doubleQuoted filePath
                return (s </> x)

    ifdef :: Maybe FilePath -> S.Set String -> OpenTheory ->  Parser (OpenTheory, S.Set String)
    ifdef inFile0 flags thy = do
       flag <- symbol_ "#ifdef" *> identifier
       if flag `S.member` flags
         then do (thy', flags') <- addItems inFile0 flags thy
                 symbol_ "#endif"
                 addItems inFile0 flags' thy'
         else do _ <- manyTill anyChar (try (symbol_ "#endif"))
                 addItems inFile0 flags thy

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
       -> Maybe FilePath
       -> Parser OpenDiffTheory
diffTheory flags0 inFile = do
    msig <- getState
    putState (msig `mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    (thy', _) <- symbol_ "begin"
        *> addItems inFile (S.fromList flags0) (set diffThyName thyId (defaultOpenDiffTheory ("diff" `S.member` (S.fromList flags0))))
        <* symbol "end"
    return thy'
  where
    addItems :: Maybe FilePath -> S.Set String -> OpenDiffTheory -> Parser (OpenDiffTheory, S.Set String)
    addItems inFile0 flags thy = asum
      [ do thy' <- liftedAddHeuristic thy =<< heuristic True workDir
           addItems inFile0 flags thy'
      , do
           diffbuiltins
           msig <- getState
           addItems inFile0 flags $ set (sigpMaudeSig . diffThySignature) msig thy
      , do functions
           msig <- getState
           addItems inFile0 flags $ set (sigpMaudeSig . diffThySignature) msig thy
      , do equations
           msig <- getState
           addItems inFile0 flags $ set (sigpMaudeSig . diffThySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems inFile0 flags thy'
      , do thy' <- liftedAddRestriction' thy =<< diffRestriction
           addItems inFile0 flags thy'
      , do thy' <- liftedAddRestriction' thy =<< legacyDiffAxiom
           addItems inFile0 flags thy'
           -- add legacy deprecation warning output
      , do thy' <- liftedAddLemma' thy =<< plainLemma workDir
           addItems inFile0 flags thy'
      , do thy' <- liftedAddDiffLemma thy =<< diffLemma workDir
           addItems inFile0 flags thy'
      , do ru <- diffRule
           thy' <- liftedAddDiffRule thy ru
           addItems inFile0 flags thy'
      , do r <- intrRule
           addItems inFile0 flags (addIntrRuleACsDiffAll [r] thy)
      , do c <- formalComment
           addItems inFile0 flags (addFormalCommentDiff c thy)
      , do ifdef inFile0 flags thy
      , do define inFile0 flags thy
      , do include inFile0 flags thy
      , do return (thy, flags)
      ]
      where  workDir = takeDirectory <$> inFile

    define :: Maybe FilePath -> S.Set String -> OpenDiffTheory -> Parser (OpenDiffTheory, S.Set String)
    define inFile0 flags thy = do
       flag <- try (symbol "#define") *> identifier
       addItems inFile0 (S.insert flag flags) thy

    ifdef :: Maybe FilePath -> S.Set String -> OpenDiffTheory -> Parser (OpenDiffTheory, S.Set String)
    ifdef inFile0 flags thy = do
       flag <- symbol_ "#ifdef" *> identifier
       if flag `S.member` flags
         then do (thy', flags') <- addItems inFile0 flags thy
                 symbol_ "#endif"
                 addItems inFile0 flags' thy'
         else do _ <- manyTill anyChar (try (string "#"))
                 symbol_ "endif"
                 addItems inFile0 flags thy

    include :: Maybe FilePath -> S.Set String -> OpenDiffTheory -> Parser  (OpenDiffTheory, S.Set String)
    include inFile0 flags thy = do
         filepath <- try (symbol "#include") *> filePathParser
         msig <- getState
         let (thy', flags', sig') = unsafePerformIO (parseFileWState msig (addItems' (Just filepath) flags thy) filepath)
         _ <- putState sig'
         addItems inFile0 flags' $ set (sigpMaudeSig . diffThySignature) sig' thy'
      where
        addItems' :: Maybe FilePath -> S.Set String -> OpenDiffTheory -> Parser (OpenDiffTheory, S.Set String, MaudeSig)
        addItems' inFile1 flags1 thy1 = do
             (thy',fl') <- addItems inFile1 flags1 thy1
             msig <- getState
             return (thy', fl', msig)

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
