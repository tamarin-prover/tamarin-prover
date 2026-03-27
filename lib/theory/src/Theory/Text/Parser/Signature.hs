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
import           Data.Either
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
functionAttribute :: Parser (Either Privacy Constructability)
functionAttribute = asum
  [ symbol "private" Data.Functor.$> Left Private
  , symbol "constructor" Data.Functor.$> Right Constructor
  , symbol "destructor" Data.Functor.$> Right Destructor
  ]

getReservedNames :: MaudeSig -> [String]
getReservedNames msig = 
  map (BC.unpack . fst) (S.toList $ stFunSyms msig)

-- Map builtin names to their reserved function names
builtinReservedNames :: [(String, [String])]
builtinReservedNames = 
  [(name, getReservedNames msig) | (name, Just msig, _) <- builtinsNames]

function :: Parser SapicFunSym
function = do
        f <- BC.pack <$> identifier
        (argTypes,outType) <- functionType
        atts <- option [] $ list functionAttribute
        st <- getState
        sign <- sig <$> getState
        let k = length argTypes
        let priv = if Private `elem` lefts atts then Private else Public
        let destr = if Destructor `elem` rights atts then Destructor else Constructor
        let requested = (k, priv, destr)

        -- Check specifically for conflicts with builtins to give a precise error message.
        let allReservedNames = reservedBuiltinNames st
        when (BC.unpack f `elem` allReservedNames) $ do
          let conflictingBuiltins = [b | (b, names) <- builtinReservedNames, BC.unpack f `elem` names]
          case lookup f (S.toList $ stFunSyms sign) of
            Just builtinSig | builtinSig /= requested ->
              fail $ "`" ++ BC.unpack f ++ "` conflicts with builtin(s) "
                  ++ show conflictingBuiltins
                  ++ " (builtin: " ++ show builtinSig ++ ", requested: " ++ show requested ++ ")"
            _ -> return ()

        -- Check for any conflict with existing functions.
        case lookup f (S.toList (stFunSyms sign) ++ S.toList(macroNames sign)) of
          Just kp' | kp' /= (k,priv,destr) && (BC.unpack f /= "fst" || k /= 1 || priv == Private) && (BC.unpack f /= "snd" || k /= 1 || priv == Private) ->
            fail $ "conflicting arities/options " ++
                   show kp' ++ " and " ++ show (k,priv,destr) ++
                   " for `" ++ BC.unpack f ++ "`. Please choose a different name for this function."
          _ -> do
                modifyStateSig $ addFunSym (f,(k,priv,destr))
                return ((f,(k,priv,destr)),argTypes,outType)


functions :: Parser [SapicFunSym]
functions =
    (try (symbol "functions") <|> symbol "function") *> colon *> commaSep1 function

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
        rrule <- RRule <$> term llitNoPub True <*> (equalSign *> term llitNoPub True)
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
