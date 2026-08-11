-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Parsing Signatures
------------------------------------------------------------------------------

module Theory.Text.Parser.Signature (
    heuristic
    , builtins
    , options
    , functions
    , equations
    , liftedAddPredicate
    , preddeclaration
    , goalRanking
    , diffbuiltins
    , export
)
where

import Term.Maude.Signature
import           Prelude
import qualified Data.ByteString.Char8      as BC
import           Data.Either()
-- import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           Data.Maybe                 (fromMaybe)
--import           Data.Char
--import qualified Data.Map                   as M
import           Control.Applicative        hiding (empty, many, optional)
import           Control.Monad
import qualified Control.Monad.Catch        as Catch
import           Text.Parsec                hiding ((<|>))

import           Term.Substitution
import           Term.SubtermRule
import           Theory
import           Theory.Text.Parser.Token
import Theory.Text.Parser.Fact
import Theory.Text.Parser.Term
import Theory.Text.Parser.Formula
import Theory.Text.Parser.Exceptions
import Debug.Trace (traceM)

import Data.Label.Total
import Data.Label.Mono (Lens)
import Theory.Sapic
import qualified Data.Functor

data FunctionAttribute
  = StandardFunctionAttribute FctAttr
  | FunctionData
  deriving (Eq, Show)


 -- Describes the mapping between Maude Signatures and the builtin Name
builtinsDiffNames :: [(String,
                       MaudeSig)]
builtinsDiffNames = [
  ("diffie-hellman", dhMaudeSig),
  ("bilinear-pairing", bpMaudeSig),
  ("multiset", msetMaudeSig),
  ("xor", xorMaudeSig),
  ("symmetric-encryption", symEncMaudeSig),
  ("asymmetric-encryption", asymEncMaudeSig),
  ("signing", signatureMaudeSig),
  ("dest-pairing", pairDestMaudeSig),  
  ("dest-symmetric-encryption", symEncDestMaudeSig),
  ("dest-asymmetric-encryption", asymEncDestMaudeSig),
  ("dest-signing", signatureDestMaudeSig),  
  ("revealing-signing", revealSignatureMaudeSig),
  ("hashing", hashMaudeSig),
  ("natural-numbers", natMaudeSig)
              ]

-- | Describes the mapping between a builtin name, its potential Maude Signatures
-- and its potential option
builtinsNames :: [([Char], Maybe MaudeSig, Maybe (Lens Total Option Bool))]
builtinsNames =
  [
  ("locations-report",  Just locationReportMaudeSig, Just transReport),
  ("reliable-channel",  Nothing, Just transReliable)
  ]
  ++ map (\(x,y) -> (x, Just y, Nothing)) builtinsDiffNames

-- | Builtin signatures.
builtins :: OpenTheory -> Parser OpenTheory
builtins thy0 =do
            _  <- symbol "builtins"
            _  <- colon
            l <- commaSep1 builtinTheory -- l is list of lenses to set options to true with
                                         -- builtinTheory modifies signature in state.
            return $ foldl setOption' thy0 l
  where
    setName thy name = modify thyItems (++ [TranslationItem (SignatureBuiltin name)]) thy
    setOption' thy (Nothing, name)  = setName thy name
    setOption' thy (Just l, name) = setOption l (setName thy name)
    -- Check for conflicts between builtin functions and user defined functions, and fail with a helpful error message if any are found.
    -- Otherwise, add the builtin signature to the state and add the reserved function names to the state.
    extendSig (name, Just msig, opt) = do
        _ <- symbol name
        st <- getState
        let builtinFuncs = S.toList $ stFunSyms msig
        let macroSyms    = S.toList $ macroNames (sig st)
        let macroFuncs   = S.fromList $ map (BC.unpack . fst) macroSyms
        let currFuncs    = S.toList $ stFunSyms (sig st)

        let functionConflicts = [ (BC.unpack fname, builtinArity, userArity)
                                | (fname, builtinArity) <- builtinFuncs
                                , (fname', userArity)   <- currFuncs
                                , fname == fname'
                                , userArity /= builtinArity
                                ]

        let macroConflicts = [ (BC.unpack fname, builtinArity, macroArity)
                      | (fname, builtinArity) <- builtinFuncs
                      , BC.unpack fname `S.member` macroFuncs
                      , Just macroArity <- [lookup fname macroSyms]
                      , macroArity /= builtinArity
                      ]

        unless (null functionConflicts || name == "dest-pairing") $ do
            fail $ "Builtin '" ++ name ++ "' conflicts with existing function(s) (same name, different arity or function options): " ++ 
                  show [fname | (fname, _, _) <- functionConflicts] ++ ". Please remove these function definitions or use different names."

        unless (null macroConflicts) $ do
            fail $ "Builtin '" ++ name ++ "' conflicts with existing macro '" ++ show [fname | (fname, _, _) <- macroConflicts] ++ "'"
        
        modifyStateSig (`mappend` msig)
        modifyState (\st -> st { reservedBuiltinNames = 
                                reservedBuiltinNames st ++ 
                                fromMaybe [] (lookup name builtinReservedNames) })
        return (opt, name)
    extendSig (name, Nothing, opt) = do
        _ <- symbol name
        return (opt, name)
    builtinTheory = asum $ map (try . extendSig) builtinsNames

diffbuiltins :: Parser ()
diffbuiltins =
    (symbol "builtins" *> colon *> commaSep1 builtinTheory) Data.Functor.$> ()
  where
    extendSig (name, msig) =
        symbol name *>
        modifyStateSig (`mappend` msig)
    builtinTheory = asum $ map (try . extendSig) builtinsDiffNames


functionType :: Parser ([SapicType], SapicType)
functionType = try (do
                    _  <- opSlash
                    k  <- fromIntegral <$> natural
                    return (replicate k defaultSapicType, defaultSapicType)
                   )
                <|>(do
                    argTypes  <- parens (commaSep typep)
                    _         <- colon
                    outType   <- typep
                    return (argTypes, outType)
                    )

-- | Parse a 'FunctionAttribute'.
functionAttribute :: Parser FunctionAttribute
functionAttribute = asum
  [ symbol "private" Data.Functor.$> StandardFunctionAttribute (Privacy Private)
  , symbol "constructor" Data.Functor.$> StandardFunctionAttribute (Constructability Constructor)
  , symbol "destructor" Data.Functor.$> StandardFunctionAttribute (Constructability Destructor)
  , symbol "AC" Data.Functor.$> StandardFunctionAttribute (ACstate IsAC)
  , try (symbol "NDC-diff") Data.Functor.$> StandardFunctionAttribute (NDCstate IsNDCDiff)
  , symbol "NDC" Data.Functor.$> StandardFunctionAttribute (NDCstate IsNDC)
  , symbol "data" Data.Functor.$> FunctionData
  ]

getReservedNames :: MaudeSig -> [String]
getReservedNames msig = 
  map (BC.unpack . fst) (S.toList $ stFunSyms msig)

-- Map builtin names to their reserved function names
builtinReservedNames :: [(String, [String])]
builtinReservedNames = 
  [(name, getReservedNames msig) | (name, Just msig, _) <- builtinsNames]

functionDecls :: Parser [SapicFunSym]
functionDecls = do
        f <- BC.pack <$> identifier
        (argTypes,outType) <- functionType
        atts <- option [] $ list functionAttribute
        st <- getState
        sign <- sig <$> getState
        let k = length argTypes
        let priv = if hasStandardAttribute (Privacy Private) atts then Private else Public
        let destr = if hasStandardAttribute (Constructability Destructor) atts then Destructor else Constructor
        let ac = if hasStandardAttribute (ACstate IsAC) atts then IsAC else NotAC
        -- The NDC attribute states the NDC property for the trace intruder rules, the NDC-diff
        -- attribute for the diff intruder rules.
        let ndc = joinNDC (if hasStandardAttribute (NDCstate IsNDC) atts then IsNDC else NotNDC)
                          (if hasStandardAttribute (NDCstate IsNDCDiff) atts then IsNDCDiff else NotNDC)
        let isData = FunctionData `elem` atts
        let requested = case ac of
              IsAC -> ACfctUser (f, (priv, destr, ndc))
              NotAC -> NoEqUser (f, (k, priv, destr, ndc))
        validateFunctionAttributes f atts
        when (ac == IsAC && k /= 2) $
          fail "conflicting arity : AC function must be binary"
        ensureNameAllowed st sign f requested
        baseSym <- addOrLookupDeclaredFunction sign f requested
        if isData
          then do
            let accessorInfos = mkDataAccessorInfos baseSym argTypes outType
            mapM_ (ensureGeneratedAccessorNameAvailable sign . accessorName) accessorInfos
            modifyStateSig $ \sig0 ->
              let sig1 = foldl (flip addFunSym) sig0 (map fst3 accessorInfos)
              in foldl (flip addCtxtStRule) sig1 (mkDataAccessorRules baseSym (map fst3 accessorInfos))
            return ((baseSym, argTypes, outType) : accessorInfos)
          else
            return [(baseSym, argTypes, outType)]
  where
    fst3 (x, _, _) = x
    accessorName (sym, _, _) = functionSymbolName sym

    validateFunctionAttributes name attrs = do
      when (countAttr FunctionData attrs > 1) $
        fail $ "duplicate `data` attribute for `" ++ BC.unpack name ++ "`"
      when (FunctionData `elem` attrs
            && hasStandardAttribute (Constructability Destructor) attrs) $
        fail $ "`" ++ BC.unpack name ++ "` cannot be both `[data]` and `[destructor]`"
      when (FunctionData `elem` attrs
            && hasStandardAttribute (Privacy Private) attrs) $
        fail $ "`" ++ BC.unpack name ++ "` cannot be both `[data]` and `[private]`"
      when (FunctionData `elem` attrs
            && hasStandardAttribute (ACstate IsAC) attrs) $
        fail $ "`" ++ BC.unpack name ++ "` cannot be both `[data]` and `[AC]`"
      let conflictingBuiltins =
            [ builtin
            | (builtin, names) <- builtinReservedNames
            , BC.unpack name `elem` names
            ]
      when (FunctionData `elem` attrs && not (null conflictingBuiltins)) $
        fail $ "`" ++ BC.unpack name ++ "` cannot use `[data]` because it is "
            ++ "reserved by the following builtins: " ++ show conflictingBuiltins

    countAttr attr = length . filter (== attr)

    hasStandardAttribute attr = elem (StandardFunctionAttribute attr)

    ensureNameAllowed st' sign' name requested = do
      let allReservedNames = reservedBuiltinNames st'
      when (BC.unpack name `elem` allReservedNames) $ do
        let conflictingBuiltins =
              [ builtin
              | (builtin, names) <- builtinReservedNames
              , BC.unpack name `elem` names
              ]
        case namedFunctionSymbols sign' name of
          builtinSyms | not (null builtinSyms) && requested `notElem` builtinSyms ->
            fail $ "`" ++ BC.unpack name ++ "` conflicts with builtin(s) "
                ++ show conflictingBuiltins
                ++ " (builtin: " ++ show builtinSyms
                ++ ", requested: " ++ show requested ++ ")"
          _ -> pure ()
      case lookup name (S.toList (macroNames sign')) of
        Just _ ->
          fail $ "conflicting definition for `" ++ BC.unpack name ++ "`: this name is already used by a macro"
        Nothing ->
          pure ()

    addOrLookupDeclaredFunction sign' name desired = do
      case namedFunctionSymbols sign' name of
        [] -> do
          modifyStateSig $ addFunSym desired
          return desired
        [existing]
          | existing == desired || pairProjectionCompatible name desired ->
              return existing
          | otherwise ->
              fail $ "conflicting arities/options "
                  ++ show existing ++ " and " ++ show desired
                  ++ " for `" ++ BC.unpack name
                  ++ "`. Please choose a different name for this function."
        existing ->
          fail $ "conflicting arities/options "
              ++ show existing ++ " and " ++ show desired
              ++ " for `" ++ BC.unpack name
              ++ "`. Please choose a different name for this function."

    ensureGeneratedAccessorNameAvailable sign' name = do
      st' <- getState
      let allReservedNames = reservedBuiltinNames st'
      when (BC.unpack name `elem` allReservedNames) $ do
        let conflictingBuiltins =
              [ builtin
              | (builtin, names) <- builtinReservedNames
              , BC.unpack name `elem` names
              ]
        fail $ "generated accessor `" ++ BC.unpack name
            ++ "` conflicts with builtin(s) " ++ show conflictingBuiltins
      when (BC.unpack name `elem` reservedBuiltins) $
        fail $ "generated accessor `" ++ BC.unpack name
            ++ "` is a reserved function name for builtins"
      unless (null (namedFunctionSymbols sign' name)
              && lookup name (S.toList $ macroNames sign') == Nothing) $
        fail $ "generated accessor `" ++ BC.unpack name
            ++ "` conflicts with an existing function or macro"

    mkDataAccessorInfos (NoEqUser (base, (arity, _, _, _))) argTypes outType =
      [ ( accessorSym i
        , [outType]
        , argTypes !! (i - 1)
        )
      | i <- [1 .. arity]
      ]
      where
        accessorSym i =
          NoEqUser (mkAccessorName base i, (1, Public, Destructor, NotNDC))
    mkDataAccessorInfos _ _ _ =
      error "data constructors must be non-AC function symbols"

    mkDataAccessorRules (NoEqUser funSym@(_, (arity, _, _, _))) accessorSyms =
      [ accessorRule i accessorSym
      | (i, accessorSym) <- zip [1 .. arity] accessorSyms
      ]
      where
        vars =
          [ varTerm $ LVar "x" LSortMsg (fromIntegral i)
          | i <- [1 .. arity]
          ]
        funTerm = fAppNoEq funSym vars
        accessorRule i (NoEqUser accessorSym) =
          fAppNoEq accessorSym [funTerm] `CtxtStRule`
            StRhs [[0, i - 1]] (vars !! (i - 1))
        accessorRule _ _ =
          error "data accessors must be non-AC function symbols"
    mkDataAccessorRules _ _ =
      error "data constructors must be non-AC function symbols"

    mkAccessorName base idx = base <> BC.pack ('_' : show idx)

    functionSymbolName (NoEqUser (name, _)) = name
    functionSymbolName (ACfctUser (name, _)) = name

    namedFunctionSymbols sign' name =
      filter ((== name) . functionSymbolName) (S.toList $ userDefinedFunSyms sign')

    pairProjectionCompatible name (NoEqUser (_, (arity, privacy, _, _))) =
      BC.unpack name `elem` ["fst", "snd"] && arity == 1 && privacy == Public
    pairProjectionCompatible _ _ = False


functions :: Parser [SapicFunSym]
functions =
    (try (symbol "functions") <|> symbol "function") *> colon *> fmap concat (commaSep1 functionDecls)

equations :: Parser ()
equations = do
    convergent <- option False (try $ do
        _ <- symbol "equations"
        _ <- brackets (symbol "convergent")
        colon
        return True)
    unless convergent $ symbol "equations" *> colon
    eqs <- commaSep1 equation
    modifyStateSig (\sig -> foldl (flip addCtxtStRule) sig eqs)
    modifyState (\st -> st { sig = (sig st) { eqConvergent = convergent } })  -- Explicit state update
    return ()
  where
    equation = do
        rrule <- RRule <$> acterm True llitNoPub <*> (equalSign *> acterm True llitNoPub)
        case rRuleToCtxtStRule rrule of
          Just str -> return str
          Nothing  -> fail $ "Not a correct equation: " ++ show rrule

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
      [  try 
         (symbol "translation-progress") Data.Functor.$> Just transProgress
        , symbol "translation-allow-pattern-lookups" Data.Functor.$> Just transAllowPatternMatchinginLookup
        , symbol "translation-state-optimisation" Data.Functor.$> Just stateChannelOpt
        , symbol "translation-asynchronous-channels" Data.Functor.$> Just asynchronousChannels
        , symbol "translation-compress-events" Data.Functor.$> Just compressEvents
      ]

predicate :: Parser Predicate
predicate = do
           f <- fact' lvar
           _ <- symbol "<=>"
           Predicate f <$> plainFormula
           <?> "predicate declaration"

preddeclaration :: OpenTheory -> Parser OpenTheory
preddeclaration thy = do
                    _          <- try (symbol "predicates" <|> symbol "predicate")
                    _          <- colon
                    predicates <- commaSep1 predicate
                    foldM liftedAddPredicate thy predicates
                    <?> "predicate block"

-- | parse an export declaration
export :: OpenTheory -> Parser OpenTheory
export thy = do
                    _          <- try (symbol "export")
                    tag          <- identifier
                    _          <- colon
                    text       <- doubleQuoted $ many bodyChar -- TODO Gotta use some kind of text.
                    let ei = ExportInfo tag text
                    return (addExportInfo ei thy)
                    <?> "export block"
              where
                bodyChar = try $ do
                  c <- anyChar
                  case c of
                    '\\' -> char '\\' <|> char '"'
                    '"'  -> mzero
                    _    -> return c


heuristic :: Bool -> Maybe FilePath -> Parser [GoalRanking ProofContext]
heuristic diff workDir = symbol "heuristic" *> char ':' *> skipMany (char ' ') *> (concat <$> many1 (goalRanking diff workDir)) <* lexeme spaces

goalRanking :: Bool -> Maybe FilePath -> Parser [GoalRanking ProofContext]
goalRanking diff workDir = try oracleRanking <|> internalTacticRanking <|> regularRanking <?> "proof method ranking"
   where
       regularRanking = filterHeuristic diff <$> many1 letter <* skipMany (char ' ')

       internalTacticRanking = do
            _ <- string "{" <* skipMany (char ' ')
            goal <- toGoalRanking <$> pure ("{.}")
            tacticName <- optionMaybe (many1 (noneOf "\"\n\r{}") <* char '}' <* skipMany (char ' '))

            return $ [mapInternalTacticRanking (maybeSetInternalTacticName tacticName) goal]

       oracleRanking = do
           goal <- toGoalRanking <$> (string "o" <|> string "O") <* skipMany (char ' ')
           relPath <- optionMaybe (char '"' *> many1 (noneOf "\"\n\r") <* char '"' <* skipMany (char ' '))

           return [mapOracleRanking (maybeSetOracleRelPath relPath . maybeSetOracleWorkDir workDir) goal]

       toGoalRanking = if diff then stringToGoalRankingDiff False else stringToGoalRanking False

liftedAddPredicate :: Catch.MonadThrow m =>
                      Theory sig c r p TranslationElement
                      -> Predicate -> m (Theory sig c r p TranslationElement)
liftedAddPredicate thy prd = liftMaybeToEx (DuplicateItem (PredicateItem prd)) (addPredicate prd thy)
