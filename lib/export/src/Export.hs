{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Sapic processes to ProVerif
module Export
  ( prettyProVerifTheory,
    prettyProVerifEquivTheory,
    prettyDeepSecTheory,
  )
where

import Control.Monad.Fresh
import Control.Monad.Trans.PreciseFresh qualified as Precise
import Data.ByteString.Char8 qualified as BC
import Data.Char
import Data.Data
import Data.Functor.Identity qualified
import Data.List as List
import Data.Map qualified as M
import Data.Maybe
import Data.Set qualified as S
import Debug.Trace (trace)
import ProVerifHeader
import RuleTranslation
import Sapic.Annotation
import Sapic.Report
import Sapic.States
import Sapic.Typing
import System.IO
import System.IO.Unsafe
import Term.Builtin.Rules
import Term.SubtermRule
import Text.PrettyPrint.Class
import Theory
import Theory.Module
import Theory.Sapic
import Theory.Text.Pretty
import Theory.Tools.Wellformedness (formulaFacts)

-- | Types of translation the export module covers (others are covered by sapic module).
data Translation
  = ProVerif
  | DeepSec
  deriving (Ord, Eq, Typeable, Data)

-- | Types of translations covered here map to other modules, but not vice versa (for instance, Sapic to MSR).
exportModule :: Translation -> ModuleType
exportModule ProVerif = ModuleProVerif
exportModule DeepSec = ModuleDeepSec

-- | Information needed during translation.
data TranslationContext = TranslationContext
  { trans :: Translation,
    attackerChannel :: Maybe LVar,
    hasBoundStates :: Bool,
    hasUnboundStates :: Bool,
    predicates :: [Predicate],
    replicationBound :: Int,
    skipReuseOrSrc :: Bool,
    skipRestrictions :: Bool
  }
  deriving (Eq, Ord)

-- | Default translation context.
emptyTC :: TranslationContext
emptyTC =
  TranslationContext
    { trans = ProVerif,
      attackerChannel = Nothing,
      hasBoundStates = False,
      hasUnboundStates = False,
      predicates = [],
      replicationBound = 3, -- TODO: allow modifying this parameter
      skipReuseOrSrc = False,
      skipRestrictions = False
    }

-- | Failure function performing an unsafe IO failure
translationFail :: String -> a
translationFail s = unsafePerformIO (fail s)

-- | Warning function performing an unsafe IO failure
translationWarning :: String -> a -> a
translationWarning s cont = unsafePerformIO printWarning
  where
    printWarning = do
      hPutStr stderr $ "WARNING: " ++ s
      pure cont

------------------------------------------------------------------------------
-- Core ProVerif Export
------------------------------------------------------------------------------

proverifTemplate :: (Document d) => [d] -> [d] -> d -> [d] -> [d] -> [d] -> [d] -> [d] -> d
proverifTemplate headers queries process macroproc ruleproc restrictions lemmas comments =
  vcat headers
    $$ vcat queries
    $$ vcat lemmas
    $$ vcat restrictions
    $$ vcat macroproc
    $$ vcat ruleproc
    $$ text "process"
    $$ nest 4 process
    $--$ vcat (intersperse (text "") comments)

prettyProVerifTheory ::
  ModuleType ->
  Bool -> -- noReuse
  Bool -> -- noRestrictions
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  (OpenTheory, TypingEnvironment) ->
  IO Doc
prettyProVerifTheory m noReuse noRestrictions lemSel (thy, typEnv) = do
  headersTheory <- loadHeaders tc thy typEnv -- load headers from theory
  let headersTranslation =
        [ baseHeaders, -- base headers for translation
          prochd, -- headers from the process
          macroprochd, -- headers from the macroprocess
          ruleHeaders -- headers from the rules
        ]
  headers <- checkDuplicates' $ filterHeaders $ S.unions $ headersTheory : headersTranslation
  let hd = attribHeaders tc headers
  pure $ proverifTemplate hd queries proc' macroproc ruleproc restrictions lemmas comments
  where
    tc =
      emptyTC
        { predicates = theoryPredicates thy,
          skipReuseOrSrc = noReuse,
          skipRestrictions = noRestrictions
        }
    (proc, prochd, hasBoundState, hasUnboundState) = loadProc tc thy
    (ruleproc, ruleComb, ruleHeaders) = loadRules thy m
    proc'
      | null (theoryProcesses thy) = ruleComb
      | null (theoryRules thy) = proc
      | otherwise = proc <-> text "|" <-> ruleComb
    baseHeaders = if hasUnboundState then stateHeaders else S.empty
    restrictions =
      if skipRestrictions tc
        then []
        else loadRestrictions tc typEnv thy
    queries = loadQueries thy
    lemmas = loadLemmas lemSel tc typEnv thy
    (macroproc, macroprochd) =
      -- if stateM is not empty, we have inlined the process calls, so we don't reoutput them
      if hasBoundState then ([text ""], S.empty) else loadMacroProc tc thy
    comments = [text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy]

stateHeaders :: S.Set ProVerifHeader
stateHeaders =
  S.fromList
    [ Table "tbl_states_handle" "(bitstring,channel)", -- the table for linking states identifiers and channels
      Table "tbl_locks_handle" "(bitstring,channel)" -- the table for linking locks identifiers and channels
    ]

data BuiltinTranslation
  = NotSupportedBuiltin String
  | AccurateBuiltin [ProVerifHeader]
  | BestEffortBuiltin [ProVerifHeader]

builtins :: String -> BuiltinTranslation
builtins "diffie-hellman" =
  BestEffortBuiltin
    [ Sym "const" "g" ":bitstring" [],
      Fun "fun" "exp" 2 "(bitstring,bitstring):bitstring" [],
      Eq "equation" "forall a:bitstring,b:bitstring;" "exp( exp(g,a),b) = exp(exp(g,b),a)" ""
    ]
builtins "locations-report" =
  AccurateBuiltin
    [ Fun "fun" "rep" 2 "(bitstring,bitstring):bitstring" ["private"]
    ]
builtins "xor" =
  BestEffortBuiltin
    [ Fun "fun" "xor" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "zero" 0 "():bitstring" []
    ]
builtins "hashing" =
  AccurateBuiltin
    [ Fun "fun" "h" 1 "(bitstring):bitstring" []
    ]
builtins "asymmetric-encryption" =
  AccurateBuiltin
    [ Fun "fun" "aenc" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "pk" 1 "(bitstring):bitstring" []
    ] -- Don't need to define the reduc equations here because they are already read from the theory
builtins "signing" =
  AccurateBuiltin
    [ Fun "fun" "sign" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "pk" 1 "(bitstring):bitstring" [],
      Fun "fun" "okay" 0 "():bitstring" []
    ]
builtins "revealing-signing" =
  AccurateBuiltin
    [ Fun "fun" "revealSign" 2 "(bitstring,bitstring):bitstring" [],
      Fun "fun" "revealVerify" 3 "(bitstring,bitstring,bitstring):bitstring" [],
      Fun "fun" "getMessage" 1 "(bitstring):bitstring" [],
      Fun "fun" "pk" 1 "(bitstring):bitstring" [],
      Fun "fun" "okay" 0 "():bitstring" []
    ]
builtins "symmetric-encryption" =
  AccurateBuiltin
    [ Fun "fun" "senc" 2 "(bitstring,bitstring):bitstring" []
    ]
builtins "multiset" =
  NotSupportedBuiltin
    "Multiset is not supported in ProVerif. If you want to model natural numbers, you can use the dedicated Tamarin builtin."
builtins "bilinear-pairing" =
  NotSupportedBuiltin
    "Bilinear pairings are not supported in ProVerif."

-- We filter out some predefined headers that we don't want to redefine.
filterHeaders :: S.Set ProVerifHeader -> S.Set ProVerifHeader
filterHeaders = S.filter (not . isForbidden)
  where
    isForbidden (Fun "fun" "true" _ _ _) = True
    isForbidden (Type "bitstring") = True
    isForbidden (Type "channel") = True
    isForbidden (Type "nat") = True
    isForbidden _ = False

-- | Extract the “name” of any header that should be unique.
getProVerifHeaderIdentifier :: ProVerifHeader -> Maybe String
getProVerifHeaderIdentifier (Fun _ n _ _ _)   = Just n
getProVerifHeaderIdentifier (Sym _ n _ _)     = Just n
getProVerifHeaderIdentifier (HEvent n _)      = Just n
getProVerifHeaderIdentifier (Table n _)       = Just n
getProVerifHeaderIdentifier _                 = Nothing

-- | Fail if any identifier occurs more than once; otherwise return all headers
checkDuplicates :: MonadFail m => [ProVerifHeader] -> m [ProVerifHeader]
checkDuplicates headers = do
    let identMap :: M.Map String [ProVerifHeader]
        identMap = M.fromListWith (<>)
                  [ (n, [h])
                  | h <- headers
                  , Just n <- [getProVerifHeaderIdentifier h]
                  ]
        conflicts = filter ((>1) . length) (M.toList identMap)

    -- if there are conflicts, bail; otherwise return the whole input
    unless (null conflicts) $
      fail $ unlines
        ( "ProVerif constructs (functions, constants, events, tables) must be distinct.\
          \ Please rename these duplicates:"
        : [ intercalate ", " (map show defs)
          | (_, defs) <- conflicts
          ]
        )

    return headers

checkDuplicates' :: S.Set ProVerifHeader -> IO [ProVerifHeader]
checkDuplicates' = checkDuplicates . S.toList

ppPubName :: NameId -> Doc
ppPubName (NameId n) = text $ case n of
  "zero" -> "0"
  "one" -> "1"
  "g" -> "g"
  _ -> "s" ++ n

-- Loader of the export functions
------------------------------------------------------------------------------
loadQueries :: Theory sig c b p TranslationElement -> [Doc]
loadQueries thy =
  map (text . (._eText)) (lookupExportInfo "queries" thy)

------------------------------------------------------------------------------
-- Core ProVerif Equivalence Export
------------------------------------------------------------------------------

proverifEquivTemplate :: (Document d) => [d] -> [d] -> [d] -> [d] -> [d] -> d
proverifEquivTemplate headers queries equivlemmas macroproc comments =
  vcat headers
    $$ vcat queries
    $$ vcat macroproc
    $$ vcat equivlemmas
    $--$ vcat (intersperse (text "") comments)

prettyProVerifEquivTheory :: (OpenTheory, TypingEnvironment) -> IO Doc
prettyProVerifEquivTheory (thy, typEnv) = do
  headersTheory <- loadHeaders tc thy typEnv
  let headersTranslation =
        [ baseHeaders,
          equivhd,
          diffEquivhd,
          macroprochd
        ]
  headers <- checkDuplicates' $ filterHeaders $ S.unions $ headersTheory : headersTranslation
  let hd = attribHeaders tc headers
  fproc <- finalproc
  pure $ proverifEquivTemplate hd queries fproc macroproc comments
  where
    tc = emptyTC {predicates = theoryPredicates thy}
    (equivlemmas, equivhd, hasBoundState, hasUnboundState) = loadEquivProc tc thy
    (diffEquivlemmas, diffEquivhd, _, diffHasUnboundState) = loadDiffProc tc thy
    baseHeaders = if hasUnboundState || diffHasUnboundState then stateHeaders else S.empty
    finalproc =
      if length equivlemmas + length diffEquivlemmas > 1
        then fail "Error: ProVerif can only support at most one equivalence or diff equivalence query."
        else pure $ equivlemmas ++ diffEquivlemmas
    queries = loadQueries thy
    (macroproc, macroprochd) =
      -- if stateM is not empty, we have inlined the process calls, so we don't reoutput them
      if hasBoundState then ([text ""], S.empty) else loadMacroProc tc thy
    comments = [text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy]

------------------------------------------------------------------------------
-- Core DeepSec Export
------------------------------------------------------------------------------

deepsecTemplate :: (Document d) => [d] -> [d] -> [d] -> [d] -> [d] -> d
deepsecTemplate headers macroproc requests equivlemmas comments =
  vcat headers
    $$ vcat macroproc
    $$ vcat requests
    $$ vcat equivlemmas
    $--$ vcat (intersperse (text "") comments)

emptyTypeEnv :: TypingEnvironment
emptyTypeEnv = TypingEnvironment {vars = M.empty, events = M.empty, funs = M.empty}

prettyDeepSecTheory :: Int -> OpenTheory -> IO Doc
prettyDeepSecTheory repBound thy = do
  headers <- loadHeaders tc thy emptyTypeEnv
  let hd = attribHeaders tc $ S.toList (S.unions [headers, macroprochd, equivhd])
  pure $ deepsecTemplate hd macroproc requests equivlemmas comments
  where
    tc = emptyTC {trans = DeepSec, replicationBound = repBound}
    requests = loadRequests thy
    (macroproc, macroprochd) = loadMacroProc tc thy
    (equivlemmas, equivhd, _, _) = loadEquivProc tc thy
    comments = [text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy]

-- Loader of the export functions
------------------------------------------------------------------------------
loadRequests :: Theory sig c b p TranslationElement -> [Doc]
loadRequests thy =
  map (text . (._eText)) (lookupExportInfo "requests" thy)

------------------------------------------------------------------------------
-- Term Printers
------------------------------------------------------------------------------

ppLVar :: LVar -> Doc
ppLVar (LVar n _ 0) = text $ sanitizeSymbol 'a' n
ppLVar (LVar n _ i) = text . sanitizeSymbol 'a' $ n <> "_" <> show i

ppUnTypeVar :: SapicLVar -> Doc
ppUnTypeVar (SapicLVar lvar _) = ppLVar lvar

ppType :: Maybe String -> String
ppType Nothing = "bitstring"
ppType (Just s) = s

ppTypeVar :: TranslationContext -> SapicLVar -> Doc
ppTypeVar tc v@(SapicLVar lvar ty) = case trans tc of
  ProVerif -> ppLVar lvar <> text ":" <> text (ppType ty)
  DeepSec -> ppUnTypeVar v

ppTypeLit :: (Show c) => TranslationContext -> Lit c SapicLVar -> Doc
ppTypeLit tc (Var v) = ppTypeVar tc v
ppTypeLit _ (Con c) = text . sanitizeSymbol 'a' $ show c

auxppTerm :: (Show v) => (Lit Name v -> Doc) -> VTerm Name v -> (Doc, S.Set ProVerifHeader)
auxppTerm ppLit t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
      Lit v -> ppLit v
      FApp (AC Xor) ts -> ppXor ts
      FApp (AC o) ts -> ppTerms (ppACOp o) 1 "(" ")" ts
      FApp (NoEq s) [] | s == natOneSym -> text "1"
      FApp (NoEq s) [t1, t2] | s == expSym -> text "exp(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
      FApp (NoEq s) [t1, t2] | s == diffSym -> text "choice" <> text "[" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text "]"
      FApp (NoEq _) [t1, t2] | isPair tm -> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
      FApp (NoEq (f, _)) [] -> text $ ppFunSym f
      FApp (NoEq (f, _)) ts -> ppFun f ts
      FApp (C EMap) ts -> ppFun emapSymString ts
      FApp List ts -> ppFun (BC.pack "LIST") ts

    ppACOp Mult = "*"
    ppACOp NatPlus = "+"
    ppACOp Xor = "⊕"
    ppACOp u = translationFail $ "Unsupported operator " ++ show u

    ppXor [] = text "one"
    ppXor [t1, t2] = text "xor(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
    ppXor (t1 : ts) = text "xor(" <> ppTerm t1 <> text ", " <> ppXor ts <> text ")"
    ppTerms sepa n lead finish =
      fcat
        . (text lead :)
        . (++ [text finish])
        . map (nest n)
        . punctuate (text sepa)
        . map ppTerm
    ppFun f ts =
      text (ppFunSym f ++ "(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm tm = case viewTerm tm of
      Lit (Con (Name PubName n)) ->
        if show n `elem` ["g", "one", "zero"]
          then S.empty
          else -- The 's' is just prepended here instead of using sanitizeSymbol, because that function
          -- only does the prepending for reserved keywords and symbols starting with a digit. For
          -- free bitstrings however, we ALWAYS want the leading 's', to also avoid clashes with
          -- function names, rule names, event names etc. We could also do it like that for variables
          -- and function names (where we use sanitizeSymbol now), but I thought if we did it in all
          -- other places it might not be needed there, and I thought it would be better to leave as
          -- much as possible of the original naming as it is
            S.singleton (Sym "free" ("s" ++ show n) ":bitstring" [])
      Lit _ -> S.empty
      FApp _ ts -> foldl (\x y -> x `S.union` getHdTerm y) S.empty ts

-- | pretty print a SapicTerm, collecting the constants that need to be declared
-- matchVars is the set of vars that correspond to pattern matching
-- isPattern enables the pattern match printing, which adds types to variables, and = to constants.
auxppSapicTerm :: TranslationContext -> S.Set LVar -> Bool -> SapicTerm -> (Doc, S.Set ProVerifHeader)
auxppSapicTerm tc mVars isPattern = auxppTerm ppLit
  where
    ppLit v = case v of
      Con (Name FreshName n) -> text . sanitizeSymbol 'a' $ show n
      Con (Name PubName n) | isPattern -> text "=" <> text ("s" ++ show n)
      Con (Name PubName n) -> ppPubName n
      Var (SapicLVar lvar@(LVar n lsort _) _)
        | lsort `elem` [LSortPub, LSortFresh, LSortNat] ->
            translationWarning
              ( "Encountered a variable "
                  ++ n
                  ++ " of non-message sort "
                  ++ show lsort
                  ++ ". Used in pattern matching, this may produces different behaviour in Tamarin and ProVerif.  Used elsewhere, we simply ignore the sort and translate to to ProVerif's default: bitstring"
              )
              $ text "=" <> ppLVar lvar
      Var (SapicLVar lvar _)
        | S.member lvar mVars -> text "=" <> ppLVar lvar
      l | isPattern -> ppTypeLit tc l
      Var (SapicLVar lvar _) -> ppLVar lvar
      l -> text . sanitizeSymbol 'a' $ show l

ppSapicTerm :: TranslationContext -> SapicTerm -> (Doc, S.Set ProVerifHeader)
ppSapicTerm tc = auxppSapicTerm tc S.empty False

-- pretty print an LNTerm, collecting the constant that need to be declared
-- the boolean b enables types printout
pppLNTerm :: TranslationContext -> Bool -> LNTerm -> (Doc, S.Set ProVerifHeader)
pppLNTerm _ b = auxppTerm ppLit
  where
    ppLit v = case v of
      Con (Name FreshName n) -> text . sanitizeSymbol 'a' $ show n
      Con (Name PubName n) -> ppPubName n
      tm2 | b -> text $ sanitizeSymbol 'a' (show tm2) <> ":bitstring"
      Var lvar -> ppLVar lvar
      tm2 -> text . sanitizeSymbol 'a' $ show tm2

ppLNTerm :: TranslationContext -> LNTerm -> (Doc, S.Set ProVerifHeader)
ppLNTerm tc = pppLNTerm tc False

-- pretty print a Fact, collecting the constant that need to be declared
ppFact :: TranslationContext -> Fact SapicTerm -> (Doc, S.Set ProVerifHeader)
ppFact tc (Fact tag _ ts)
  | factTagArity tag /= length ts = sppFact ("MALFORMED-" ++ show tag) ts
  | otherwise = sppFact ('e' : factTagName tag) ts
  where
    sppFact name ts2 =
      (nestShort' (name ++ "(") ")" . fsep . punctuate comma $ pts, sh)
      where
        (pts, shs) = unzip $ map (ppSapicTerm tc) ts2
        sh = S.unions shs

-- Pretty print an Action, collecting the constant and events that need to be declared.
-- It also returns a boolean, specifying if the printout can serve as the end of a process or not.
ppAction ::
  ProcessAnnotation LVar ->
  TranslationContext ->
  LSapicAction ->
  (Doc, S.Set ProVerifHeader, Bool)
ppAction ProcessAnnotation {isStateChannel = Nothing} tc (New v) =
  (text "new " <> ppTypeVar tc v, S.empty, True)
ppAction ProcessAnnotation {pureState = False, isStateChannel = Just t} tc (New v@(SapicLVar lvar _)) =
  ( extras $
      text "new "
        <> channel
        <> text "[assumeCell];"
        $$ text "new lock_"
        <> channel
        <> text "[assumeCell];"
        -- we also declare the corresponding lock channel, and initialize it
        $$ text "out(lock_"
        <> ppLVar lvar
        <> text ",0) |",
    if hasUnboundStates tc then sht else S.empty,
    False
  )
  where
    channel = ppTypeVar tc v
    (pt, sht) = ppSapicTerm tc t
    extras x =
      if hasUnboundStates tc
        then
          x
            $$ text "insert tbl_states_handle("
            <> pt
            <> text ", "
            <> ppLVar lvar
            <> text ");"
            $$ text "insert tbl_locks_handle("
            <> pt
            <> text ", lock_"
            <> ppLVar lvar
            <> text ");"
        else x
ppAction ProcessAnnotation {pureState = True, isStateChannel = Just _} tc (New v) =
  ( text "new " <> ppTypeVar tc v <> text "[assumeCell]",
    S.empty,
    True
  )
ppAction _ TranslationContext {trans} Rep | trans == ProVerif = (text "!", S.empty, False)
ppAction _ TranslationContext {trans = DeepSec} Rep = (text "", S.empty, False)
ppAction _ tc@TranslationContext {trans = ProVerif} (ChIn t1 t2 mvars) =
  ( text "in(" <> pt1 <> text "," <> pt2 <> text ")",
    sh1 `S.union` sh2,
    True
  )
  where
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = auxppSapicTerm tc (S.map toLVar mvars) True t2
ppAction _ tc@TranslationContext {trans = DeepSec} (ChIn t1 t2@(LIT (Var (SapicLVar _ _))) mvars) =
  ( text "in(" <> pt1 <> text "," <> pt2 <> text ")",
    sh1 `S.union` sh2,
    True
  )
  where
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = auxppSapicTerm tc (S.map toLVar mvars) True t2

-- pattern matching on input for deepsec is not supported
ppAction _ tc@TranslationContext {trans = DeepSec} (ChIn t1 t2 mvars) =
  ( text "in("
      <> pt1
      <> text ","
      <> text pt2var
      <> text ");"
      $$ text "let ("
      <> pt2
      <> text ")="
      <> text pt2var
      <> text " in",
    sh1 `S.union` sh2,
    False
  )
  where
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = auxppSapicTerm tc (S.map toLVar mvars) True t2
    pt2var = "fresh" ++ stripNonAlphanumerical (render pt2)
ppAction _ tc (ChOut t1 t2) = (text "out(" <> pt1 <> text "," <> pt2 <> text ")", sh1 `S.union` sh2, True)
  where
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = ppSapicTerm tc t2
ppAction _ tc@TranslationContext {trans} (Event (Fact tag m ts)) | trans == ProVerif = (text "event " <> pa, sh, True) -- event Headers are definde globally inside loadHeaders
  where
    (pa, sh) = ppFact tc (Fact tag m ts)
ppAction _ TranslationContext {trans = DeepSec} (Event _) = (text "", S.empty, False)
-- For pure states, we do not put locks and unlocks
ppAction ProcessAnnotation {pureState = True} TranslationContext {trans} (Lock _)
  | trans == ProVerif =
      (text "", S.empty, False)
-- If there is a state channel, we simply use it
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} TranslationContext {trans} (Lock _)
  | trans == ProVerif =
      ( text "in(lock_" <> ppLVar lvar <> text "," <> text "counterlock" <> ppLVar lvar <> text ":nat)",
        S.empty,
        True
      )
-- If there is no state channel, we must use the table
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans} (Lock t)
  | trans == ProVerif =
      ( text "get tbl_locks_handle("
          <> pt
          <> text ","
          <> text ptvar
          <> text ") in"
          $$ text "in("
          <> text ptvar
          <> text " , counter"
          <> text ptvar
          <> text ":nat)",
        sh,
        True
      )
  where
    freevars = S.fromList $ map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = auxppSapicTerm tc freevars True t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)
ppAction ProcessAnnotation {pureState = True} TranslationContext {trans} (Unlock _)
  | trans == ProVerif =
      (text "", S.empty, False)
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} TranslationContext {trans} (Unlock _)
  | trans == ProVerif =
      ( text "out(lock_" <> ppLVar lvar <> text "," <> text "counterlock" <> ppLVar lvar <> text "+1" <> text ") | ",
        S.empty,
        False
      )
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans} (Unlock t)
  | trans == ProVerif =
      (text "out(" <> text ptvar <> text " , counter" <> text ptvar <> text "+1) | ", sh, False)
  where
    (pt, sh) = ppSapicTerm tc t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = _} tc@TranslationContext {trans} (Insert _ c)
  | trans == ProVerif =
      ( text "out(" <> ppLVar lvar <> text ", " <> pc <> text ") |",
        shc,
        False
      )
  where
    (pc, shc) = ppSapicTerm tc c

-- Should never happen
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = True} TranslationContext {trans} (Insert _ _)
  | trans == ProVerif =
      (text "TRANSLATIONERROR", S.empty, True)
-- ppAction ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=False} tc@TranslationContext{trans=ProVerif} (Insert _ c) =
--       (text "in(" <> pt <> text ", " <> pt <> text "_dump:bitstring);"
--        $$ text "out(" <> pt <> text ", " <> pc <> text ") |"
--       , shc, False)
--   where
--     pt = ppLVar lvar
--     (pc, shc) = ppSapicTerm tc c

-- must rely on the table
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans} (Insert t t2)
  | trans == ProVerif =
      ( text "in("
          <> text ptvar
          <> text ", "
          <> text dumpvar
          <> text ":bitstring);"
          $$ text "out("
          <> text ptvar
          <> text " , "
          <> pt2
          <> text ") | ",
        S.insert hd $ sh `S.union` sh2,
        False
      )
  where
    (pt, sh) = ppSapicTerm tc t
    (pt2, sh2) = ppSapicTerm tc t2
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    dumpvar = "dumpvar" ++ stripNonAlphanumerical (render pt)
    hd = Sym "free" ptvar ":channel" []
ppAction _ _ _ = translationFail "Action not supported for translation"

ppSapic :: TranslationContext -> LProcess (ProcessAnnotation LVar) -> (Doc, S.Set ProVerifHeader)
ppSapic _ (ProcessNull _) = (text "0", S.empty) -- remove zeros when not needed
ppSapic tc (ProcessComb Parallel _ pl pr) = (parens $ nest 2 (parens ppl) $$ text "|" $$ nest 2 (parens ppr), pshl `S.union` pshr)
  where
    (ppl, pshl) = ppSapic tc pl
    (ppr, pshr) = ppSapic tc pr
ppSapic tc (ProcessComb NDC _ pl pr) = (nest 4 (parens ppl) $$ text "+" <> nest 4 (parens ppr), pshl `S.union` pshr)
  where
    (ppl, pshl) = ppSapic tc pl
    (ppr, pshr) = ppSapic tc pr
ppSapic tc (ProcessComb (Let t1 t2 mvars) _ pl (ProcessNull _)) =
  ( text "let "
      <> pt1
      <> text "="
      <> pt2
      <> text " in"
      $$ ppl,
    S.unions [sh1, sh2, pshl]
  )
  where
    (ppl, pshl) = ppSapic tc pl
    (pt1, sh1) = auxppSapicTerm tc (S.map toLVar mvars) True t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic tc (ProcessComb (Let t1 t2 mvars) _ pl pr) =
  ( text "let "
      <> pt1
      <> text "="
      <> pt2
      <> text " in"
      $$ ppl
      $$ text "else "
      <> ppr,
    S.unions [sh1, sh2, pshl, pshr]
  )
  where
    (ppl, pshl) = ppSapic tc pl
    (ppr, pshr) = ppSapic tc pr
    (pt1, sh1) = auxppSapicTerm tc (S.map toLVar mvars) True t1
    (pt2, sh2) = ppSapicTerm tc t2

-- if the process call does not have any argument, we just inline
ppSapic tc (ProcessComb (ProcessCall _ []) _ pl _) = (ppl, pshl)
  where
    (ppl, pshl) = ppSapic tc pl

-- if there are state or lock channels created by addStateChannels, we must inline
ppSapic tc@TranslationContext {hasBoundStates = True} (ProcessComb (ProcessCall {}) _ pl _) =
  (ppl, pshl)
  where
    (ppl, pshl) = ppSapic tc pl
ppSapic tc (ProcessComb (ProcessCall name ts) _ _ _) =
  ( text name <> parens (fsep (punctuate comma ppts)),
    S.unions shs
  )
  where
    pts = map (ppSapicTerm tc) ts
    (ppts, shs) = unzip pts
ppSapic tc (ProcessComb (Cond a) _ pl pr) =
  addElseBranch (text "if " <> pa <> text " then" $$ nest 4 (parens ppl), sh `S.union` pshl)
  where
    (ppl, pshl) = ppSapic tc pl
    (pa, sh) = ppFact' a
    ppFact' (Ato (Syntactic (Pred (Fact (ProtoFact _ "Smaller" _) _ [v1, v2]))))
      | Lit (Var (Free vn1)) <- viewTerm v1,
        Lit (Var (Free vn2)) <- viewTerm v2 =
          (ppUnTypeVar vn1 <> text "<" <> ppUnTypeVar vn2, S.empty)
    ppFact' p =
      case expandFormula (predicates tc) (toLFormula p) of
        Left _ -> translationFail "Export does not support tamarin predicates in conditionnals."
        Right form -> (fst . snd $ Precise.evalFresh (ppLFormula emptyTypeEnv ppNAtom form) (avoidPrecise form), S.empty)
    addElseBranch (d, s) = case pr of
      ProcessNull _ -> (d, s)
      _ ->
        let (ppr, pshr) = ppSapic tc pr
         in (d $$ text "else" $$ nest 4 (parens ppr), s `S.union` pshr)
ppSapic tc (ProcessComb (CondEq t1 t2) _ pl (ProcessNull _)) =
  ( text "let (=" <> pt1 <> text ")=" <> pt2 <> text " in " $$ nest 4 (parens ppl),
    S.unions [sh1, sh2, pshl]
  )
  where
    (ppl, pshl) = ppSapic tc pl
    (pt1, sh1) = ppSapicTerm tc t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic tc (ProcessComb (CondEq t1 t2) _ pl pr) =
  ( text "let (=" <> pt1 <> text ")=" <> pt2 <> text " in " $$ nest 4 (parens ppl) $$ text "else" <> nest 4 (parens ppr),
    S.unions [sh1, sh2, pshl, pshr]
  )
  where
    (ppl, pshl) = ppSapic tc pl
    (ppr, pshr) = ppSapic tc pr
    (pt1, sh1) = ppSapicTerm tc t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic tc (ProcessComb (Lookup _ c) ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = True} pl (ProcessNull _)) =
  ( text "in(" <> pt <> text ", " <> pc <> text ");" $$ ppl,
    pshl
  )
  where
    pt = ppLVar lvar
    pc = ppTypeVar tc c
    (ppl, pshl) = ppSapic tc pl

-- Should never happen
ppSapic _ (ProcessComb (Lookup _ _) ProcessAnnotation {stateChannel = Nothing, pureState = True} _ (ProcessNull _)) =
  translationFail "Unexpected error -> please report with an issue on the github."
ppSapic tc (ProcessComb (Lookup _ c) ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} pl (ProcessNull _)) =
  ( text "in("
      <> pt
      <> text ", "
      <> pc
      <> text ");"
      $$ text "out("
      <> pt
      <> text ", "
      <> pc2
      <> text ") |"
      $$ ppl,
    pshl
  )
  where
    pt = ppLVar lvar
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    (ppl, pshl) = ppSapic tc pl
ppSapic tc (ProcessComb (Lookup t c) ProcessAnnotation {stateChannel = Nothing, pureState = False} pl (ProcessNull _)) =
  ( text "get tbl_states_handle("
      <> pt
      <> text ","
      <> text ptvar
      <> text ") in"
      $$ text "in("
      <> text ptvar
      <> text " , "
      <> pc
      <> text ");"
      $$ text "out("
      <> text ptvar
      <> text " , "
      <> pc2
      <> text ") |"
      $$ ppl,
    sh `S.union` pshl
  )
  where
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    freevars = S.fromList $ map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = auxppSapicTerm tc freevars True t
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    (ppl, pshl) = ppSapic tc pl
ppSapic tc (ProcessComb (Lookup t c) ProcessAnnotation {stateChannel = Nothing, pureState = False} pl pr) =
  ( text "get tbl_states_handle("
      <> pt
      <> text ","
      <> text ptvar
      <> text ") in"
      $$ nest
        4
        ( parens
            ( text "in("
                <> text ptvar
                <> text " , "
                <> pc
                <> text ");"
                $$ text "out("
                <> text ptvar
                <> text " , "
                <> pc2
                <> text ") | "
                $$ ppl
            )
        )
      $$ text "else"
      $$ nest
        4
        ( parens
            ( text "new "
                <> text ptvar
                <> text ":channel [assumeCell];" -- the cell did not exists, we create it !
                $$ text "insert tbl_states_handle("
                <> pt'
                <> text ", "
                <> text ptvar
                <> text ");"
                $$ text "out("
                <> text ptvar
                <> text ",0) |"
                $$ ppr
            )
        ),
    S.unions [sh, pshl, pshr]
  )
  where
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    freevars = S.fromList $ map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = auxppSapicTerm tc freevars True t
    (pt', _) = ppSapicTerm tc t
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    (ppl, pshl) = ppSapic tc pl
    (ppr, pshr) = ppSapic tc pr
ppSapic _ (ProcessComb (Lookup _ _) _ _ _) =
  translationFail "The export does not support a lookup with an else branch."
ppSapic tc@TranslationContext {trans} (ProcessAction Rep _ p) | trans == ProVerif = (text "!" $$ parens pp, psh)
  where
    (pp, psh) = ppSapic tc p
ppSapic tc@TranslationContext {trans = DeepSec} (ProcessAction Rep _ p) =
  ( text ("!^" ++ show (replicationBound tc)) <> parens pp,
    psh
  )
  where
    (pp, psh) = ppSapic tc p
ppSapic tc (ProcessAction a an (ProcessNull _)) =
  if unNeedZero
    then (pa, sh)
    else (pa <> text "0", sh)
  where
    (pa, sh, unNeedZero) = ppAction an tc a
ppSapic tc (ProcessAction a an p) =
  if needSep
    then (pa <> text ";" $$ pp, sh `S.union` psh)
    else (pa $$ pp, sh `S.union` psh)
  where
    (pa, sh, needSep) = ppAction an tc a
    (pp, psh) = ppSapic tc p

addAttackerReportProc :: TranslationContext -> OpenTheory -> Doc -> Doc
addAttackerReportProc tc thy p =
  text "(" $$ p $$ text ")| in(" <> att <> text ",(x:bitstring,y:bitstring)); if " <> formula <> text " then out(" <> att <> text ", rep(x,y))"
  where
    att = fst $ getAttackerChannel tc Nothing
    reportPreds =
      List.find (\(Predicate (Fact tag _ _) _) -> showFactTag tag == "Report") $
        theoryPredicates thy
    (_, (formula, _)) = case reportPreds of
      Nothing -> translationFail "Translation Error, the Report predicate must be defined."
      Just (Predicate _ form) -> Precise.evalFresh (ppLFormula emptyTypeEnv ppNAtom form) (avoidPrecise form)

------------------------------------------------------------------------------
-- Main printer for processes
------------------------------------------------------------------------------

loadProc :: TranslationContext -> OpenTheory -> (Doc, S.Set ProVerifHeader, Bool, Bool)
loadProc tc thy = case theoryProcesses thy of
  [] -> (text "", S.empty, False, False)
  [pr] ->
    let (d, headers) = ppSapic tc2 p
        finald =
          if isNothing (List.find (== "locations-report") (theoryBuiltins thy))
            then d
            else addAttackerReportProc tc2 thy d
     in (finald, S.union hd headers, fst hasStates, snd hasStates)
    where
      p = makeAnnotations thy pr
      hasStates = hasBoundUnboundStates p
      (tc2, hd) = mkAttackerContext tc {hasBoundStates = fst hasStates, hasUnboundStates = snd hasStates} p
  _ -> translationFail "Multiple sapic processes were defined."

loadMacroProc :: TranslationContext -> OpenTheory -> ([Doc], S.Set ProVerifHeader)
loadMacroProc tc thy = loadMacroProcs tc thy (theoryProcessDefs thy)

loadMacroProcs :: TranslationContext -> OpenTheory -> [ProcessDef] -> ([Doc], S.Set ProVerifHeader)
loadMacroProcs _ _ [] = ([text ""], S.empty)
loadMacroProcs tc thy (p : q) =
  let (docs, heads) = loadMacroProcs tc3 thy q
   in case p._pVars of
        -- TODO bugfix, this is probably wrong when the macro does not have any parameter
        Nothing -> (docs, hd `S.union` heads)
        Just pvars ->
          let (newText, newHeads) = ppSapic tc3 mainProc
              vrs = text "(" <> fsep (punctuate comma (map (ppTypeVar tc3) pvars)) <> text ")"
              headers = headersOfType $ map extractType pvars
              macroDef =
                text "let "
                  <> text p._pName
                  <> vrs
                  <> text "="
                  $$ nest 4 newText
                  <> text "."
           in (macroDef : docs, hd `S.union` newHeads `S.union` heads `S.union` headers)
  where
    mainProc = makeAnnotations thy p._pBody
    extractType (SapicLVar _ ty) = ty
    hasStates = hasBoundUnboundStates mainProc
    (tc2, hd) = case attackerChannel tc of
      -- we set up the attacker channel if it does not already exists
      Nothing -> mkAttackerContext tc mainProc
      Just _ -> (tc, S.empty)
    tc3 = tc2 {hasBoundStates = fst hasStates, hasUnboundStates = snd hasStates}

loadDiffProc :: TranslationContext -> OpenTheory -> ([Doc], S.Set ProVerifHeader, Bool, Bool)
loadDiffProc tc thy = case theoryDiffEquivLemmas thy of
  [] -> ([], S.empty, False, False)
  [pr] ->
    let (d, headers) = ppSapic tc2 p
     in ([text "process" $$ nest 4 d], S.union hd headers, fst hasStates, snd hasStates)
    where
      p = makeAnnotations thy pr
      hasStates = hasBoundUnboundStates p
      (tc2, hd) = mkAttackerContext tc {hasBoundStates = fst hasStates, hasUnboundStates = snd hasStates} p
  _ -> translationFail "Multiple sapic processes were defined."

loadEquivProc :: TranslationContext -> OpenTheory -> ([Doc], S.Set ProVerifHeader, Bool, Bool)
loadEquivProc tc thy = loadEquivProcs tc thy (theoryEquivLemmas thy)

loadEquivProcs ::
  TranslationContext ->
  OpenTheory ->
  [(PlainProcess, PlainProcess)] ->
  ([Doc], S.Set ProVerifHeader, Bool, Bool)
loadEquivProcs _ _ [] = ([], S.empty, False, False)
loadEquivProcs tc thy ((p1, p2) : q) =
  let (docs, heads, hadBoundStates, hadUnboundStates) = loadEquivProcs tc3 thy q
      (newText1, newHeads1) = ppSapic tc3 mainProc1
      (newText2, newHeads2) = ppSapic tc3 mainProc2
      macroDef = case trans tc of
        ProVerif ->
          text "equivalence"
            $$ nest 4 newText1
            $$ nest 4 newText2
        DeepSec ->
          text "query session_equiv("
            $$ nest 4 newText1
            <> text ","
            $$ nest 4 newText2
            <> text ")."
   in ( macroDef : docs,
        S.unions [hd, newHeads1, newHeads2, heads],
        hasBoundSt || hadBoundStates,
        hasUnboundSt || hadUnboundStates
      )
  where
    mainProc1 = makeAnnotations thy p1
    mainProc2 = makeAnnotations thy p2
    hasStates1 = hasBoundUnboundStates mainProc1
    hasStates2 = hasBoundUnboundStates mainProc2
    hasBoundSt = fst hasStates1 || fst hasStates2
    hasUnboundSt = snd hasStates1 || snd hasStates2
    (tc2, hd) = case attackerChannel tc of
      -- we set up the attacker channel if it does not already exists
      Nothing -> mkAttackerContext tc mainProc2
      Just _ -> (tc, S.empty)
    tc3 = tc2 {hasBoundStates = hasBoundSt, hasUnboundStates = snd hasStates1 || snd hasStates2}

------------------------------------------------------------------------------
-- Printer for Lemmas
------------------------------------------------------------------------------

-- | Smaller-or-equal / More-or-equally-specific relation on types.
mergeType :: (Eq a) => Maybe a -> Maybe a -> Maybe a
mergeType t Nothing = t
mergeType Nothing t = t
mergeType _ t = t

mergeEnv :: M.Map LVar SapicType -> M.Map LVar SapicType -> M.Map LVar SapicType
mergeEnv = M.mergeWithKey (\_ t1 t2 -> Just $ mergeType t1 t2) id id

typeVarsEvent :: (Ord k) => TypingEnvironment -> FactTag -> [Term (Lit c k)] -> M.Map k SapicType
typeVarsEvent TypingEnvironment {events = ev} tag ts =
  case M.lookup tag ev of
    Just t ->
      foldl
        ( \mp (term, ty) ->
            case viewTerm term of
              Lit (Var lvar) -> M.insert lvar ty mp
              _ -> mp
        )
        M.empty
        (zip ts t)
    Nothing -> M.empty

ppProtoAtom ::
  (HighlightDocument d, Ord k, Show k, Show c) =>
  TypingEnvironment ->
  Bool ->
  (s (Term (Lit c k)) -> d) ->
  (Term (Lit c k) -> d) ->
  ProtoAtom s (Term (Lit c k)) ->
  (d, M.Map k SapicType)
ppProtoAtom te _ _ ppT (Action v f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | (tag == KUFact) || isKLogFact f -- treat KU() and K() facts the same
    =
      (ppFactL "attacker" ts <> opAction <> ppT v, M.empty)
  | otherwise =
      ( text "event(" <> ppFactL ('e' : factTagName tag) ts <> text ")" <> opAction <> ppT v,
        typeVarsEvent te tag ts
      )
  where
    ppFactL n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppT t
ppProtoAtom _ _ ppS _ (Syntactic s) = (ppS s, M.empty)
ppProtoAtom _ False _ ppT (EqE l r) =
  (sep [ppT l <-> opEqual, ppT r], M.empty)
ppProtoAtom _ True _ ppT (EqE l r) =
  (sep [ppT l <-> text "<>", ppT r], M.empty)
-- sep [ppNTerm l <-> text "≈", ppNTerm r]
ppProtoAtom _ _ _ ppT (Less u v) = (ppT u <-> opLess <-> ppT v, M.empty)
ppProtoAtom _ _ _ ppT (Subterm u v) = (text "subterm(" <> ppT u <> comma <> ppT v <> text ")", M.empty)
ppProtoAtom _ _ _ _ (Last i) = (operator_ "last" <> parens (text (show i)), M.empty)

ppAtom :: TypingEnvironment -> Bool -> (LNTerm -> Doc) -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppAtom te b = ppProtoAtom te b (const emptyDoc)

-- only used for ProVerif queries display
-- the Bool is set to False when we must negate the atom
ppNAtom :: TypingEnvironment -> Bool -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppNAtom te b = ppAtom te b (fst . ppLNTerm emptyTC)

mapLits :: (Ord a, Ord b) => (a -> b) -> Term a -> Term b
mapLits f t = case viewTerm t of
  Lit l -> lit . f $ l
  FApp o as -> fApp o (map (mapLits f) as)

extractFree :: BVar p -> p
extractFree (Free v) = v
extractFree (Bound i) = translationFail $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

toLAt :: (Ord (f1 b), Ord (f1 (BVar b)), Functor f2, Functor f1) => f2 (Term (f1 (BVar b))) -> f2 (Term (f1 b))
toLAt = fmap (mapLits (fmap extractFree))

ppLFormula ::
  (MonadFresh m, Ord c, HighlightDocument b, Functor syn) =>
  TypingEnvironment ->
  (TypingEnvironment -> Bool -> ProtoAtom syn (Term (Lit c LVar)) -> (b, M.Map LVar SapicType)) ->
  ProtoFormula syn (String, LSort) c LVar ->
  m ([LVar], (b, M.Map LVar SapicType))
ppLFormula te ppAt =
  pp
  where
    pp (Ato a) = pure ([], ppAt te False (toLAt a))
    pp (TF True) = pure ([], (operator_ "true", M.empty)) -- "T"
    pp (TF False) = pure ([], (operator_ "false", M.empty)) -- "F"
    pp (Not (Ato a@(EqE _ _))) = pure ([], ppAt te True (toLAt a))
    pp (Not p) = do
      (vs, (p', envp)) <- pp p
      pure (vs, (operator_ "not" <> opParens p', envp)) -- text "¬" <> parens (pp a)
      -- pure $ operator_ "not" <> opParens p' -- text "¬" <> parens (pp a)
    pp (Conn op p q) = do
      (vsp, (p', envp)) <- pp p
      (vsq, (q', envq)) <- pp q
      pure (vsp ++ vsq, (sep [opParens p' <-> ppOp op, opParens q'], mergeEnv envp envq))
      where
        ppOp And = text "&&"
        ppOp Or = text "||"
        ppOp Imp = text "==>"
        ppOp Iff = opIff
    pp fm@(Qua {}) =
      scopeFreshness $ do
        (vs, _, fm') <- openFormulaPrefix fm
        (vsp, d') <- pp fm'
        pure (vs ++ vsp, d')

-- | Check if a formula is quantifier-free.
isPropFormula :: LNFormula -> Bool
isPropFormula (Qua {}) = False
isPropFormula (Ato _) = True
isPropFormula (TF _) = True
isPropFormula (Not (Ato (EqE _ _))) = True
isPropFormula (Not _) = True
isPropFormula (Conn _ p q) = isPropFormula p && isPropFormula q

ppQueryFormula ::
  (MonadFresh m, Functor s) =>
  TypingEnvironment ->
  ProtoFormula s (String, LSort) Name LVar ->
  [LVar] ->
  m Doc
ppQueryFormula te fm extravs = do
  (vs, (p, typeVars)) <- ppLFormula te ppNAtom fm
  pure $
    sep
      [ text "query " <> fsep (punctuate comma (map (ppTimeTypeVar typeVars) (S.toList . S.fromList $ extravs ++ vs))) <> text ";",
        nest 1 p,
        text "."
      ]

ppTimeTypeVar :: M.Map LVar SapicType -> LVar -> Doc
ppTimeTypeVar _ lvar@(LVar _ LSortNode _) = ppLVar lvar <> text ":time"
ppTimeTypeVar te lvar =
  case M.lookup lvar te of
    Nothing -> ppLVar lvar <> text ":bitstring"
    Just t -> ppLVar lvar <> text ":" <> text (ppType t)

ppQueryFormulaEx :: TypingEnvironment -> LNFormula -> [LVar] -> Doc
ppQueryFormulaEx te fm vs =
  Precise.evalFresh (ppQueryFormula te fm vs) (avoidPrecise fm)

ppRestrictFormula ::
  TypingEnvironment ->
  ProtoFormula Unit2 (String, LSort) Name LVar ->
  Precise.FreshT Data.Functor.Identity.Identity Doc
ppRestrictFormula te frm =
  if any (\(Fact tag _ _) -> factTagName tag == "KU") $ formulaFacts frm
    then -- todo: Add all translation warnings to the wellformedness report.
      pure $ translationWarning "formula with KU facts is not supported\n" (ppFail frm)
    else pp $ frm -- don't allow KU facts, nothing corresponding in PV
  where
    pp (Not fm@(Qua Ex _ _)) = do
      (vs, _, fm') <- openFormulaPrefix fm
      pure
        ( if isPropFormula fm'
            then ppOk fm' vs
            else ppFail fm
        )
    pp fm@(Qua Ex _ _) = do
      (vs, _, fm') <- openFormulaPrefix fm
      pure
        ( if isPropFormula fm'
            then ppOk fm' vs
            else ppFail fm
        )
    pp fm@(Qua All _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      pp2 fm fm'
    pp fm = pure $ ppFail fm
    ppOk = ppQueryFormulaEx te
    ppFail fm = text "(*" <> prettyLNFormula fm <> text "*)"

    pp2 fm_original fm | isPropFormula fm = pure $ ppOk fm_original []
    pp2 fm_original (Conn Imp p fm) | isPropFormula p = do
      isExDisj <- disjunct_ex fm
      pure $
        if isExDisj
          then ppOk fm_original []
          else ppFail fm_original

    -- pp2 fm_original (Conn Imp p fm@(Qua Ex _ _)) | isPropFormula p  = do
    --             (_,_,fm') <- openFormulaPrefix fm
    --             pure $ (if isPropFormula fm' then
    --                         ppOk fm_original []
    --                       else
    --                         ppFail fm_original)
    -- pp2 fm_original (Conn Imp p (Conn Or fm@(Qua Ex _ _)  fm2@(Qua Ex _ _))) | isPropFormula p  = do
    --             (_,_,fm') <- openFormulaPrefix fm
    --             (_,_,fm2') <- openFormulaPrefix fm2
    --             pure $ (if isPropFormula fm' && isPropFormula fm2' then
    --                         ppOk fm_original []
    --                       else
    --                         ppFail fm_original)

    pp2 fm_original _ = pure $ ppFail fm_original

    disjunct_ex fm@(Qua Ex _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      pure $ isPropFormula fm'
    disjunct_ex (Conn Or fm@(Qua Ex _ _) fm2) = do
      (_, _, fm') <- openFormulaPrefix fm
      b <- disjunct_ex fm2
      pure $ b && isPropFormula fm'
    disjunct_ex (Conn Or fm2 fm@(Qua Ex _ _)) = do
      (_, _, fm') <- openFormulaPrefix fm
      b <- disjunct_ex fm2
      pure $ b && isPropFormula fm'
    disjunct_ex _ = pure False

-- | ppLemma translates ONLY lemmas and only in the "classical way", i.e., with timepoints and so on
-- | The resulting translations are NOT suitable as ProVerif lemmas, axioms and restrictions (only as queries)
ppLemma :: TypingEnvironment -> Lemma ProofSkeleton -> Doc
ppLemma te p =
  trace
    ( "PROVERIF LEMMA: "
        ++ render
          ( vcat
              ( map
                  ( \fm -> case fm of
                      Not fm' ->
                        if allImplsEx fm' && p._lTraceQuantifier == ExistsTrace
                          then printFmNameFormula fm' $$ text "(* Existential lemma " <> text p._lName <> text " has a leading negation, interpret ProVerif's answers accordingly!*)\n"
                          else printFmNameFormula fm
                      _ -> printFmNameFormula fm
                  )
                  fms
              )
              $$ if isEmpty comments then comments else text "(* To reconstruct lemma " <> text p._lName <> text ":" $$ comments $$ text "*)"
          )
        ++ " END"
    )
    $ vcat
      ( map
          ( \fm -> case fm of
              Not fm' ->
                if allImplsEx fm' && p._lTraceQuantifier == ExistsTrace
                  then printFmNameFormula fm' $$ text "(* Existential lemma " <> text p._lName <> text " has a leading negation, interpret ProVerif's answers accordingly!*)\n"
                  else printFmNameFormula fm
              _ -> printFmNameFormula fm
          )
          fms
      )
      $$ if isEmpty comments then comments else text "(* To reconstruct lemma " <> text p._lName <> text ":" $$ comments $$ text "*)"
  where
    fms = map transformFm fms'

    printFmNameFormula f' = text "(*" <> text p._lName <> text "*)" $$ Precise.evalFresh (ppRestrictFormula te f') (avoidPrecise f') <> text "\n"

    -- assuming all formulas we are concerned with have quantifiers at their top level (after splitTopLvlConns)
    transformFm fm = transformWithPullNots $ case () of
      _
        | allActImplsNotExAct fm -> pnf fm
        | notExistsOfExists fm -> replNotAOrBWithAImpB $ either id id $ pullnots $ nnf fm
        -- \| restructToAllImpEx fm /= fm -> restructToAllImpEx fm
        | existsConjOfNotExists fm && p._lTraceQuantifier == ExistsTrace -> replAAndNotBWithAImpB $ either id id $ pullnots $ rearrangeAnd fm
        -- \| existsConjOfNotExists fm -> replAAndNotBWithAImpB $ either id id $ pullnots $ changeAssocLeftToRight fm
        | otherwise -> fm

    {- if existsConjOfNotExists fm
          then trace (render $ prettyLNFormula $ either id id $ strongPullnots fm) $ either id id $ strongPullnots fm
          else fm -}
    -- case allImplsPrenexConc fm of
    -- fm' -> trace (render $ prettyLNFormula $ pnf $ nnf fm) $ fm'
    -- fm -> fm
    -- where
    -- maybePullAlls = if allAlls maybePrenexConcl then transformWithPullnots $ pnf maybePrenexConcl else maybePrenexConcl
    -- maybePrenexConcl = if checkAllImpliesEx maybePulledExists == maybePulledExists then maybePulledExists else transformWithPullnots $ checkAllImpliesEx maybePulledExists
    -- pulledNotsFm = transformWithPullnots fm --convToGuardedStruct fm
    (fms', comments, _) = trace ("TAMARIN LEMMA: " ++ render (prettyLNFormula p._lFormula) ++ " END") $ splitTopLvlConns p._lTraceQuantifier 1 $ simplifyFormula p._lFormula

transformWithPullNots :: LNFormula -> LNFormula
transformWithPullNots f = case pullnots f of
  Left f' -> translationWarning ("Formula " ++ render (prettyLNFormula f) ++ " cannot be rewritten s.t. it either has only 1 ¬ or none, the result is:\n" ++ render (prettyLNFormula f') ++ "!\n\n") f'
  Right f' -> f'

-- turns out guardedness is potentially not good at all (Tamarin already permits only formulas that adhere to guarded quantification)
-- use the type structure for its associativity :)
{-convToGuardedStruct f = case parseString [] "" plainFormula $ render $ prettyGuarded $ formulaToGuarded_ f of
       Left _ -> f
       Right fm' -> trace (render $ prettyLNFormula fm') fm'-}

replAAndNotBWithAImpB :: ProtoFormula syn s c v -> ProtoFormula syn s c v
replAAndNotBWithAImpB (Qua q x p) = Qua q x $ replAAndNotBWithAImpB p
replAAndNotBWithAImpB (Conn And p (Not q)) = Not $ Conn Imp p q
replAAndNotBWithAImpB (Conn c p q) = Conn c (replAAndNotBWithAImpB p) (replAAndNotBWithAImpB q)
replAAndNotBWithAImpB (Not p) = Not (replAAndNotBWithAImpB p)
replAAndNotBWithAImpB fm = fm

rearrangeAnd :: ProtoFormula syn s c v -> ProtoFormula syn s c v
rearrangeAnd (Qua q x p) = Qua q x $ rearrangeAnd p
rearrangeAnd (Conn And (Conn And (Not p) q) f) = Conn And q (Conn And (Not p) f)
rearrangeAnd (Conn And (Conn And p (Not q)) f) = Conn And p (Conn And (Not q) f)
rearrangeAnd (Conn c p q) = Conn c (rearrangeAnd p) (rearrangeAnd q)
rearrangeAnd (Not p) = Not (rearrangeAnd p)
rearrangeAnd fm = fm

replNotAOrBWithAImpB :: ProtoFormula syn s c v -> ProtoFormula syn s c v
replNotAOrBWithAImpB (Qua q x p) = Qua q x $ replNotAOrBWithAImpB p
replNotAOrBWithAImpB (Conn Or (Not p) q) = Conn Imp p q
replNotAOrBWithAImpB (Conn c p q) = Conn c (replNotAOrBWithAImpB p) (replNotAOrBWithAImpB q)
replNotAOrBWithAImpB (Not p) = Not (replNotAOrBWithAImpB p)
replNotAOrBWithAImpB fm = fm

{-reorderQuants :: LNGuarded -> LNGuarded
reorderQuants (GGuarded qua ss as gf) = GGuarded qua ss (sortNotsFst as) (reorderQuants gf)
  where
    sortNotsFst xs = uncurry (++) (partition (\f -> case f of
                                                          (GGuarded All [] [a] gfalse) -> True
                                                          _ -> False) xs)
reorderQuants (GDisj disj)            = gconj $ map reorderQuants (getDisj disj)
reorderQuants (GConj conj)            = gdisj $ map reorderQuants (getConj conj)
reorderQuants af                      = af
-}

loadLemmas ::
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  TranslationContext ->
  TypingEnvironment ->
  OpenTheory ->
  [Doc]
loadLemmas lemSel tc te thy = map (ppLemma te) proverifLemmas
  where
    thyLemmas = theoryLemmas thy

    proverifLemmas = filter isApplicableLemma thyLemmas

    isApplicableLemma lem =
      lemSel lem &&
      not (skipReuseOrSrc tc &&
           (ReuseLemma `elem` lem._lAttributes || SourceLemma `elem` lem._lAttributes)) &&
      moduleCondition lem

    moduleCondition lem =
      let modules = concat [ ls | LemmaModule ls <- lem._lAttributes ]
      in null modules || exportModule (trans tc) `elem` modules

------------------------------------------------------------------------------
-- Header Generation
------------------------------------------------------------------------------

headersOfType :: [SapicType] -> S.Set ProVerifHeader
headersOfType types =
  S.fromList $
    foldl
      ( \y x -> case x of
          Nothing -> y
          Just s -> Type s : y
      )
      []
      types

headerOfFunSym :: SapicFunSym -> S.Set ProVerifHeader
headerOfFunSym ((f, (k, pub, Constructor)), inTypes, outType) =
  Fun "fun" (ppFunSym f) k ("(" ++ makeArgtypes inTypes ++ "):" ++ ppType outType) (priv_or_pub pub) `S.insert` headersOfType (outType : inTypes)
  where
    priv_or_pub Public = []
    priv_or_pub Private = ["private"]
headerOfFunSym _ = S.empty

-- | Load headers from an OpenTheory into a set of ProVerif Headers
loadHeaders :: TranslationContext -> OpenTheory -> TypingEnvironment -> IO (S.Set ProVerifHeader)
loadHeaders tc thy typeEnv = do
  eqHeaders <- foldMap (headersOfRule tc typeEnv) sigRules
  pure $ typedHeaderOfFunSym
      `S.union` headerBuiltins'
      `S.union` eqHeaders
      `S.union` eventHeaders
  where
    sig = thy._thySignature._sigMaudeInfo
    builtins' x = case builtins x of
      AccurateBuiltin y -> y
      BestEffortBuiltin y -> translationWarning ("Using best-effort translation for " ++ x) y
      NotSupportedBuiltin s -> translationFail s
    -- all builtins are contained in Sapic Element
    headerBuiltins = S.fromList $ foldMap builtins' (theoryBuiltins thy)

    -- builtin headers need to be filtered, to make sure we don't redefine a user-defined function
    headerBuiltins' = S.filter keep headerBuiltins
      where
        funNames = S.fromList [ n | Fun _ n _ _ _ <- S.toList typedHeaderOfFunSym ]
        keep (Fun _ n _ _ _) = n `S.notMember` funNames
        keep _               = True

    -- all user declared function symbols have typinginfos
    userDeclaredFunctions = theoryFunctionTypingInfos thy
    typedHeaderOfFunSym = foldMap headerOfFunSym userDeclaredFunctions

    -- events headers
    eventHeaders = M.foldrWithKey (\tag types acc -> HEvent ('e' : factTagName tag) ("(" ++ makeArgtypes types ++ ")") `S.insert` acc) S.empty typeEnv.events
    -- generating headers for equations
    sigRules = S.toList (stRules sig)

toSapicLVar :: LVar -> SapicLVar
toSapicLVar v = SapicLVar v Nothing

toSapicTerm :: LNTerm -> SapicTerm
toSapicTerm = fmap f
  where
    f (Con c) = Con c
    f (Var v) = Var $ toSapicLVar v

headersOfRule :: TranslationContext -> TypingEnvironment -> CtxtStRule -> IO (S.Set ProVerifHeader)
headersOfRule tc typeEnv r | (lhs `RRule` rhs) <- ctxtStRuleToRRule r = do
  tye <- typeTermsWithEnv typeEnv (map toSapicTerm [lhs, rhs])
  let (plhs, lsh) = ppLNTerm tc lhs
      (prhs, rsh) = ppLNTerm tc rhs
      prefix = case viewTerm lhs of
        FApp (NoEq (_, (_, _, Destructor))) _ -> "reduc"
        _ -> "equation"
      suffix = case viewTerm lhs of
        FApp (NoEq (_, (_, Private, Destructor))) _ -> " [private]"
        _ -> ""
      freesr = frees lhs `union` frees rhs
      freesrTyped = map (\v -> (v, M.lookup v tye.vars)) freesr
      hrule =
        Eq
          prefix
          ( case map ppFreeTyped freesrTyped of
              [] -> ""
              xs ->
                "forall "
                  ++ render (fsep (punctuate comma xs))
                  ++ ";"
          )
          ( render $
              sep
                [ nest 2 plhs,
                  text "=" <-> prhs
                ]
          )
          suffix

  pure $ S.unions [S.singleton hrule, lsh, rsh]
  where
    ppFreeTyped (v, Nothing) = ppLVar v <> text ":bitstring"
    ppFreeTyped (v, Just s) = ppLVar v <> text ":" <> text (ppType s)

prettyProVerifHeader :: ProVerifHeader -> Doc
prettyProVerifHeader = \case
  Type s -> text "type " <> text s <> text "."
  HEvent s ty -> text "event " <> text s <> text ty <> text "."
  Table s ty -> text "table " <> text s <> text ty <> text "."
  Eq eqtype quant eq pub -> text eqtype <> text " " <> text quant <> text " " <> text eq <> text pub <> text "."
  Sym symkind name symtype [] -> text symkind <> text " " <> text name <> text symtype <> text "."
  Sym symkind name symtype attr -> text symkind <> text " " <> text name <> text symtype <> text "[" <> fsep (punctuate comma (map text attr)) <> text "]" <> text "."
  Fun "" _ _ _ _ -> text ""
  Fun fkind name _ symtype [] -> text fkind <> text " " <> text name <> text symtype <> text "."
  Fun fkind name _ symtype attr ->
    text fkind <> text " " <> text name <> text symtype <> text "[" <> fsep (punctuate comma (map text attr)) <> text "]" <> text "."

prettyDeepSecHeader :: ProVerifHeader -> Doc
prettyDeepSecHeader = \case
  Type _ -> text "" -- no types in deepsec
  Eq "reduc" _ eq _ -> text "reduc" <> text " " <> text eq <> text "."
  Eq eqtype _ eq _ -> error $ "Deepsec does not support equations ATM: " ++ eqtype ++ " " ++ eq
  HEvent _ _ -> text ""
  Table _ _ -> text ""
  -- drop symtypes in symbol declarations
  Sym symkind name _ [] -> text symkind <> text " " <> text name <> text "."
  Sym symkind name _ attr ->
    if "private" `elem` attr
      then text symkind <> text " " <> text name <> text "[private]" <> text "."
      else text symkind <> text " " <> text name <> text "."
  -- only keep arity for fun declarations
  Fun "" _ _ _ _ -> text ""
  Fun fkind name arity _ [] ->
    text fkind
      <> text " "
      <> text name
      <> text "/"
      <> text (show arity)
      <> text "."
  Fun fkind name arity _ attr ->
    if "private" `elem` attr
      then
        text fkind
          <> text " "
          <> text name
          <> text "/"
          <> text (show arity)
          <> text "[private]"
          <> text "."
      else text fkind <> text " " <> text name <> text "/" <> text (show arity) <> text "."

attribHeaders :: TranslationContext -> [ProVerifHeader] -> [Doc]
attribHeaders tc hd =
  sym ++ fun ++ eq
  where
    (eq, fun, sym) = splitHeaders hd
    pph = case trans tc of
      ProVerif -> prettyProVerifHeader
      DeepSec -> prettyDeepSecHeader
    splitHeaders [] = ([], [], [])
    splitHeaders (x : xs)
      | Sym {} <- x = (e1, f1, pph x : s1)
      | Fun {} <- x = (e1, pph x : f1, s1)
      | Eq {} <- x = (pph x : e1, f1, s1)
      | HEvent _ _ <- x = (pph x : e1, f1, s1)
      | Table _ _ <- x = (pph x : e1, f1, s1)
      | Type _ <- x = (e1, f1, pph x : s1)
      where
        (e1, f1, s1) = splitHeaders xs

attChanName :: String
attChanName = "att"

mkAttackerChannel ::
  (MonadFresh m) =>
  LProcess (ProcessAnnotation LVar) ->
  m LVar
mkAttackerChannel _ = freshLVar attChanName LSortMsg

mkAttackerContext ::
  TranslationContext ->
  LProcess (ProcessAnnotation LVar) ->
  (TranslationContext, S.Set ProVerifHeader)
mkAttackerContext tc p =
  (tc {attackerChannel = Just attackerVar}, S.singleton hd)
  where
    attackerVar@(LVar n _ _) = evalFresh (mkAttackerChannel p) initStateAtt
    initState = avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $ S.toList $ varsProc p
    initStateAtt = fromMaybe 0 (M.lookup attChanName initState)
    hd = Sym "free" n ":channel" []

-- given an optional channel name and a translation context, returns the corresponding printer
getAttackerChannel ::
  TranslationContext ->
  Maybe SapicTerm ->
  (Doc, S.Set ProVerifHeader)
getAttackerChannel tc t1 = case (t1, attackerChannel tc) of
  (Just tt1, _) -> ppSapicTerm tc tt1
  (Nothing, Just (LVar n _ _)) -> (text n, S.empty)
  _ -> translationFail "Unexpected error -> please report with an issue on the github."

------------------------------------------------------------------------------
-- Some utility functions
------------------------------------------------------------------------------

makeArgtypes :: [SapicType] -> String
makeArgtypes [] = ""
makeArgtypes [x] = ppType x
makeArgtypes (x : t) = ppType x ++ "," ++ makeArgtypes t

stripNonAlphanumerical :: [Char] -> [Char]
stripNonAlphanumerical = filter isAlpha

-- return the annotated process
makeAnnotations :: OpenTheory -> PlainProcess -> LProcess (ProcessAnnotation LVar)
makeAnnotations thy p = res
  where
    p' = report $ toAnProcess p
    res = annotatePureStates p'
    report pr =
      if isNothing (List.find (== "locations-report") (theoryBuiltins thy))
        then pr
        else translateTermsReport pr

-- | Pull out nots in formula
pullnots :: LNFormula -> Either LNFormula LNFormula
pullnots fm =
  let fm_partially_rewritten = fixedpoint pullStep fm -- nots pulled out by pullStep can enable new pull-out steps, so need to compute fixed point
   in if onlyTopLevelNot fm_partially_rewritten
        then Right fm_partially_rewritten -- in this case, formula is fully rewritten, i.e. has only 1 top-level not or no nots at all
        else Left fm_partially_rewritten -- Error with partially rewritten formula
  where
    fixedpoint f phi = if phi /= f phi then fixedpoint f (f phi) else phi

    pullStep fm' = case fm' of
      Conn And (Not p) (Not q) -> Not $ p .||. q
      Conn Or (Not p) (Not q) -> Not $ p .&&. q
      Conn Imp p (Not q) -> if isLessOrEqe q then Conn Imp p (Not q) else Not $ p .&&. q
      Conn Iff (Not p) q -> Not $ p .<=>. q
      Conn Iff p (Not q) -> Not $ p .<=>. q
      Conn c p q -> Conn c (pullStep p) (pullStep q)
      Qua All x (Not p) -> Not $ Qua Ex x p
      Qua Ex x (Not p) -> Not $ Qua All x p
      Qua qua x p -> Qua qua x $ pullStep p
      Not (Not p) -> p
      Not (Ato (EqE t1 t2)) -> Not (Ato (EqE t1 t2))
      Not p -> Not $ pullStep p
      _ -> fm'

    -- Don't pull nots infront of equality tests/comparisons.
    isLessOrEqe (Ato (EqE _ _)) = True
    isLessOrEqe (Ato (Less _ _)) = True
    isLessOrEqe _ = False

onlyTopLevelNot :: ProtoFormula syn s c v -> Bool
onlyTopLevelNot (Not p) = noNots p -- top-level not expected if rewriting was successful
onlyTopLevelNot p = noNots p -- no top-level not may mean the rewriting has been successful and the formula has no nots at all

noNots :: ProtoFormula syn s c v -> Bool
noNots (Not (Ato (EqE _ _))) = True -- check that there are no nots below top level (except before equality tests/comparisons)
noNots (Not (Ato (Less _ _))) = True
noNots (Not _) = False
noNots (Conn _ p q) = noNots p && noNots q
noNots (Qua _ _ p) = noNots p
noNots _ = True

{-
-- | ProVerif does not allow equalities in the premise/in existential lemmas.
-- | If possible, we merge the variables/terms and remove the equality.
mergeEqs :: LNFormula -> LNFormula
mergeEqs f@(Qua All _ _) = mergeEqsUniv f
where
    mergeEqsUniv (Qua All x p) = mergeEqsUniv p
    mergeEqsUniv (Conn p q) = merge
mergeEqs f@(Qua Ex _ _) = mergeEqsEx f
-}

allAlls :: LNFormula -> Bool
allAlls p =
  onlyQua All p
    && ( (1 :: Int)
           < foldFormula
             (const 0)
             (const 0)
             (const 0)
             (\c q1 q2 -> case c of Imp -> 1 + q1 + q2; _ -> q1 + q2)
             (\_ _ q1 -> q1)
             p
       )

restructToAllImpEx :: LNFormula -> LNFormula
restructToAllImpEx (Qua All x p) = Qua All x $ restructToAllImpEx p
restructToAllImpEx (Conn Imp p q) = Conn Imp p (pnf q)
restructToAllImpEx fm = fm

-- | Check if the formula has the structure All x1...xn. (f_a => Ex y1...yn. f_b)
checkAllImpliesEx :: LNFormula -> LNFormula
checkAllImpliesEx (Qua All x p) = Qua All x $ checkAll p
  where
    checkAll (Qua All y f) = Qua All y $ checkAll f
    checkAll (Conn Imp q1 q2) = Conn Imp q1 (pnf q2)
    checkAll f = f
-- \$ checkEx q2
--      checkAll f = f
--      checkEx f = if and $
--                          foldFormula (const [True]) (const [True]) (const [True])
--                          (\_ _ _-> [True]) (\q _ q1 -> case q of Ex -> q1; All -> [False]) f
--                  then pnf f else f
checkAllImpliesEx f = f

-- | Check if a formula has only universal quantifiers and more than one implication.
-- allAlls :: LNFormula -> Bool
-- allAlls p = onlyQua All p
--            && ((1::Int) < foldFormula (const 0) (const 0) (const 0)
--                          (\c q1 q2 -> case c of Imp -> 1 + q1 + q2; _ -> q1 + q2) (\_ _ q1 -> q1) p)

-- | Check if a formula is of the form All x1 ... xn. (F => (not(Ex y1 ... yn. F')).
allImplsNotEx :: LNFormula -> Bool
allImplsNotEx (Qua All _ body) = allImplsNotEx body
allImplsNotEx (Conn Imp p (Not f'@(Qua Ex _ _))) = isPropFormula p && onlyEx f'
  where
    onlyEx (Qua Ex _ body') = isPropFormula body' || onlyEx body'
    onlyEx _ = False
allImplsNotEx _ = False

-- | Check if a formula is of the form All x1 ... xn. (F => (Ex y1 ... yn. F') or All x1 ... xn. (F => (Ex y1 ... yn. F') \/ (Ex y1' ... yn'. F'').
allImplsEx :: LNFormula -> Bool
allImplsEx (Qua All _ body) = allImplsEx body
allImplsEx f@(Conn Imp p q) = isPropFormula f || (isPropFormula p && onlyEx q)
  where
    onlyEx (Qua Ex _ body') = isPropFormula body' || onlyEx body'
    onlyEx (Conn Or (Qua Ex _ b1) (Qua Ex _ b2)) = isPropFormula b1 || isPropFormula b2
    onlyEx _ = False
allImplsEx _ = False

-- | Check if a formula is of the form All x1 ... xn. (F => F') and F' contains quantifiers.
-- | If so, return the formula where F' is in PNF else return the input formula.
allImplsPrenexConc :: LNFormula -> LNFormula
allImplsPrenexConc (Qua All x body) = Qua All x $ allImplsPrenexConc body
allImplsPrenexConc f@(Conn Imp p q) = if isPropFormula p && not (isPropFormula q) then Conn Imp p (pnf q) else f
allImplsPrenexConc f = f

-- | Check if a formula is of the form not(Ex x1 ... xn. F) where F is a conjunction, may contain existential quantifiers and has one negation.
notExistsOfExists :: LNFormula -> Bool
notExistsOfExists (Not (Qua Ex _ body)) = existsConjUnderNot body && ((1 :: Int) == (foldFormula (const 0) (const 0) (1 +) (\_ p q -> p + q) (\_ _ p -> p) $ body))
  where
    existsConjUnderNot (Qua Ex _ p) = existsConjUnderNot p
    existsConjUnderNot (Conn And p q) = existsConjUnderNot p && existsConjUnderNot q
    existsConjUnderNot (Conn {}) = False
    existsConjUnderNot _ = True
notExistsOfExists _ = False

-- | -- | Check if a formula is of the form Ex x1 ... xn. F where F contains only negative existential quantifiers and conjunctions.
existsConjOfNotExists :: LNFormula -> Bool
existsConjOfNotExists (Qua Ex _ body) = existsConjOfNotExists body
existsConjOfNotExists (Conn _ p q) = checkNotExists p && checkNotExists q
  where
    checkNotExists (Not (Qua Ex _ p)) = checkExistsInNotExists p
    checkNotExists (Conn And p q) = checkNotExists p && checkNotExists q
    checkNotExists (Conn {}) = False
    checkNotExists _ = True

    checkExistsInNotExists (Qua Ex _ p) = checkExistsInNotExists p
    checkExistsInNotExists (Conn And p q) = checkNotExists p && checkNotExists q
    checkExistsInNotExists (Conn {}) = False
    checkExistsInNotExists _ = True
existsConjOfNotExists _ = False

-- | Check if a formula contains only one type of quantifier.
onlyQua :: Quantifier -> ProtoFormula syn s c v -> Bool
onlyQua qua =
  and
    . foldFormula
      (const [True])
      (const [True])
      (const [True])
      (\_ q1 q2 -> q1 ++ q2)
      (\q _ q1 -> if qua == q then q1 else [False])

-- | Recursively split a formula at its connectives (until we split it into subformulas that start with quantifiers).
-- | Also add a formal comment so that the user knows how to reconstruct the original formula.
-- | Trace quantification influences if we distribute AND and OR.
splitTopLvlConns :: TraceQuantifier -> Int -> LNFormula -> ([LNFormula], Doc, Int)
splitTopLvlConns AllTraces step (Conn And p q) =
  ( fstP ++ fstQ,
    sndP
      $$ sndQ
      $$ text (show stepQ ++ ". Combine ")
      $$ prettyLNFormula p
      $$ text " and "
      $$ prettyLNFormula q
      $$ text " with ∧.",
    stepQ + 1
  )
  where
    (fstP, sndP, stepP) = splitTopLvlConns AllTraces step p
    (fstQ, sndQ, stepQ) = splitTopLvlConns AllTraces stepP q

{- splitTopLvlConns AllTraces step (Conn Or p q) =
    (fstP ++ fstQ,
     sndP $$ sndQ $$ text ("Distribution of a universal trace quantifier over ∨ yields a stronger statement!\nA positive result is transferable, while a negative result is not!" ++ "\n" ++ show stepQ ++ ". Combine ")
                     $$ prettyLNFormula p
                     $$ text " and "
                     $$ prettyLNFormula q
                     $$ text " with ∨.",
     stepQ + 1)
  where
    (fstP, sndP, stepP) = splitTopLvlConns AllTraces step p
    (fstQ, sndQ, stepQ) = splitTopLvlConns AllTraces stepP q -}

splitTopLvlConns ExistsTrace step (Conn Or p q) =
  ( fstP ++ fstQ,
    sndP
      $$ sndQ
      $$ text (show stepQ ++ ". Combine ")
      $$ prettyLNFormula p
      $$ text " and "
      $$ prettyLNFormula q
      $$ text " with ∨.",
    stepQ + 1
  )
  where
    (fstP, sndP, stepP) = splitTopLvlConns ExistsTrace step p
    (fstQ, sndQ, stepQ) = splitTopLvlConns ExistsTrace stepP q

-- distributing exists over AND yields a weaker statement (implied by the undistributed statement => useless)

{- splitTopLvlConns AllTraces step (Conn Imp p q) =
    (fstNotP ++ fstQ,
     sndNotP $$ sndQ $$ text ("Distribution of a universal trace quantifier over ⇒.\nA ⇒ B is being treated as ¬A ∨ B!\nThe distribution yields a stronger statement!" ++ "\n" ++ show stepQ ++ ". Combine ")
                           $$ prettyLNFormula p
                           $$ text " and "
                           $$ prettyLNFormula q
                           $$ text " with ⇒ (attention: negate the premise).",
     stepQ + 1)
  where
    (fstNotP, sndNotP, stepP) = splitTopLvlConns AllTraces step (Not p)
    (fstQ, sndQ, stepQ) = splitTopLvlConns AllTraces stepP q -}

-- case is OK, but it does not happen in Tamarin
{-splitTopLvlConns ExistsTrace step (Conn Imp p q) =
    (fstNotP ++ fstQ,
     sndNotP $$ sndQ $$ text (show stepQ ++ ". Combine ")
                           $$ prettyLNFormula p
                           $$ text " and "
                           $$ prettyLNFormula q
                           $$ text " with ⇒ (attention: negate the premise).",
     stepQ + 1)
  where
    (fstNotP, sndNotP, stepP) = splitTopLvlConns AllTraces step (Not p)
    (fstQ, sndQ, stepQ) = splitTopLvlConns  ExistsTrace stepP q-}

splitTopLvlConns _ step fm = ([fm], mempty, step)

------------------------------------------------------------------------------
-- Printers for Restrictions and ProVerif Lemmas
------------------------------------------------------------------------------

data PVElement = R | RSL

ppAtomR :: TypingEnvironment -> Bool -> (LNTerm -> Doc) -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppAtomR te b = ppProtoAtomR te b (const emptyDoc)

-- only used for ProVerif queries display
-- the Bool is set to False when we must negate the atom
ppNAtomR :: TypingEnvironment -> Bool -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppNAtomR te b = ppAtomR te b (fst . ppLNTerm emptyTC)

ppProtoAtomR ::
  (HighlightDocument d, Ord k, Show k, Show c) =>
  TypingEnvironment ->
  Bool ->
  (s (Term (Lit c k)) -> d) ->
  (Term (Lit c k) -> d) ->
  ProtoAtom s (Term (Lit c k)) ->
  (d, M.Map k SapicType)
ppProtoAtomR te _ _ ppT (Action _ f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | (tag == KUFact) || isKLogFact f -- treat KU() and K() facts the same
    =
      (ppFactL "attacker" ts, M.empty)
  | otherwise =
      ( text "event(" <> ppFactL ('e' : factTagName tag) ts <> text ")",
        typeVarsEvent te tag ts
      )
  where
    ppFactL n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppT t
ppProtoAtomR _ _ ppS _ (Syntactic s) = (ppS s, M.empty)
ppProtoAtomR _ False _ ppT (EqE l r) =
  (sep [ppT l <-> opEqual, ppT r], M.empty)
ppProtoAtomR _ True _ ppT (EqE l r) =
  (sep [ppT l <-> text "<>", ppT r], M.empty)
-- sep [ppNTerm l <-> text "≈", ppNTerm r]
ppProtoAtomR _ _ _ ppT (Less u v) = (ppT u <-> opLess <-> ppT v, M.empty)
ppProtoAtomR _ _ _ ppT (Subterm u v) = (text "subterm(" <> ppT u <> comma <> ppT v <> text ")", M.empty)
ppProtoAtomR _ _ _ _ (Last i) = (operator_ "last" <> parens (text (show i)), M.empty)

ppLFormulaR ::
  (MonadFresh m, Ord c, HighlightDocument b, Functor syn) =>
  TypingEnvironment ->
  (TypingEnvironment -> Bool -> ProtoAtom syn (Term (Lit c LVar)) -> (b, M.Map LVar SapicType)) ->
  ProtoFormula syn (String, LSort) c LVar ->
  m ([LVar], (b, M.Map LVar SapicType))
ppLFormulaR te ppAt =
  pp
  where
    pp (Ato a) = pure ([], ppAt te False (toLAt a))
    pp (TF True) = pure ([], (operator_ "true", M.empty)) -- "T"
    pp (TF False) = pure ([], (operator_ "false", M.empty)) -- "F"
    pp (Not (Ato a@(EqE _ _))) = pure ([], ppAt te True (toLAt a))
    pp (Not p) = do
      (vs, (p', envp)) <- pp p
      pure (vs, (operator_ "not" <> opParens p', envp)) -- text "¬" <> parens (pp a)
      -- pure $ operator_ "not" <> opParens p' -- text "¬" <> parens (pp a)
    pp (Conn op p q) = do
      (vsp, (p', envp)) <- pp p
      (vsq, (q', envq)) <- pp q
      pure (vsp ++ vsq, (sep [opParens p' <-> ppOp op, opParens q'], mergeEnv envp envq))
      where
        ppOp And = text "&&"
        ppOp Or = text "||"
        ppOp Imp = text "==>"
        ppOp Iff = opIff
    pp fm@(Qua {}) =
      scopeFreshness $ do
        (vs, _, fm') <- openFormulaPrefix fm
        (vsp, d') <- pp fm'
        pure (filter (\v -> lvarSort v /= LSortNode) (vs ++ vsp), d')

ppQueryFormulaR ::
  (MonadFresh m, Functor s) =>
  PVElement ->
  TypingEnvironment ->
  ProtoFormula s (String, LSort) Name LVar ->
  [LVar] ->
  m Doc
ppQueryFormulaR pe te fm extravs = do
  (vs, (p, typeVars)) <- ppLFormulaR te ppNAtomR fm
  pure $
    sep
      [ text word <> fsep (punctuate comma (map (ppTimeTypeVar typeVars) (S.toList . S.fromList $ extravs ++ vs))) <> text ";",
        nest 1 p,
        text "."
      ]
  where
    word = case pe of
      R -> "restriction "
      RSL -> "axiom "

ppQueryFormulaExR :: PVElement -> TypingEnvironment -> LNFormula -> [LVar] -> Doc
ppQueryFormulaExR pe te fm vs =
  Precise.evalFresh (ppQueryFormulaR pe te fm vs) (avoidPrecise fm)

ppRestrictFormulaR ::
  PVElement ->
  TypingEnvironment ->
  ProtoFormula Unit2 (String, LSort) Name LVar ->
  Precise.FreshT Data.Functor.Identity.Identity Doc
ppRestrictFormulaR pe te frm =
  if any (\(Fact tag _ _) -> factTagName tag == "KU") (formulaFacts frm) -- don't allow KU facts, nothing corresponding in PV
    || hasLessOrTmpEq frm -- by this point we have stripped the less if that was possible in the 1st place
    || allActImplsExAct frm
    then pure $ ppFail frm
    else pp $ allImplExLessWoTmps frm
  where
    pp (Not fm@(Qua Ex _ _)) = do
      (vs, _, fm') <- openFormulaPrefix fm
      pure
        ( if isPropFormula fm'
            then ppOk fm' vs
            else ppFail fm
        )
    pp fm@(Qua All _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      pp2 fm fm'
    pp fm = pure $ ppFail fm
    ppOk = ppQueryFormulaExR pe te
    ppFail fm = text "(*" <> prettyLNFormula fm <> text "*)"

    pp2 fm_original fm | isPropFormula fm = do
      pure $ ppOk fm_original []
    pp2 fm_original (Conn Imp p fm) | isPropFormula p = do
      isExDisj <- disjunct_ex fm
      pure $
        if isExDisj
          then ppOk fm_original []
          else ppFail fm_original
    pp2 fm_original _ = pure $ ppFail fm_original

    disjunct_ex fm@(Qua Ex _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      pure $ isPropFormula fm'
    disjunct_ex (Conn Or fm@(Qua Ex _ _) fm2) = do
      (_, _, fm') <- openFormulaPrefix fm
      b <- disjunct_ex fm2
      pure $ b && isPropFormula fm'
    disjunct_ex (Conn Or fm2 fm@(Qua Ex _ _)) = do
      (_, _, fm') <- openFormulaPrefix fm
      b <- disjunct_ex fm2
      pure $ b && isPropFormula fm'
    disjunct_ex _ = pure False

    -- pp2 fm_original (Conn Imp p fm@(Qua Ex _ _)) | isPropFormula p  = do
    --             (_,_,fm') <- openFormulaPrefix fm
    --             pure $ (if isPropFormula fm' then
    --                         ppOk fm_original []
    --                       else
    --                         ppFail fm_original)
    -- pp2 fm_original (Conn Imp p (Conn Or fm@(Qua Ex _ _)  fm2@(Qua Ex _ _))) | isPropFormula p  = do
    --             (_,_,fm') <- openFormulaPrefix fm
    --             (_,_,fm2') <- openFormulaPrefix fm2
    --             pure $ (if isPropFormula fm' && isPropFormula fm2' then
    --                         ppOk fm_original []
    --                       else
    --                         ppFail fm_original)

    -- check if a formula has no timepoint comparisons/eqs; should've been removed at that point
    hasLessOrTmpEq fm =
      foldFormula
        ( \a -> case a of
            Less _ _ -> True
            EqE t1 _ -> t1 `elem` formulaActsTmps
            _ -> False
        )
        (const False)
        (const False)
        (\_ p q -> p || q)
        (\_ _ p -> p)
        fm
      where
        -- gather the of the actions to check of we have some eq/ineq with them
        formulaActsTmps = foldFormula fAto (const []) id (\_ p q -> p ++ q) (\_ _ p -> p) fm
          where
            fAto a = case a of
              Action tf _ -> [tf]
              _ -> []

-- | Only works for restrictions (due to them being different types than lemmas)
ppRestr :: TypingEnvironment -> Restriction -> Doc
ppRestr te rstr =
  trace
    ( "PROVERIF RESTR: "
        ++ render
          ( text "(*"
              <> text rstr._rstrName
              <> text "*)"
              $$ Precise.evalFresh (ppRestrictFormulaR R te fm) (avoidPrecise fm)
          )
        ++ " END"
    )
    $ text "(*"
      <> text rstr._rstrName
      <> text "*)"
      $$ Precise.evalFresh (ppRestrictFormulaR R te fm) (avoidPrecise fm)
  where
    fm = transformWithPullNots $ transformWithStamps $ trace ("TAMARIN RESTR: " ++ render (prettyLNFormula rstr._rstrFormula) ++ " END") $ rstr._rstrFormula

{-fm = case parseString [] "" plainFormula $ render $ prettyGuarded gf of
       Left e -> error (show e ++ render (prettyGuarded gf))
       Right fm' -> fm' --- trace (show $ render $ prettyGuarded $ formulaToGuarded_ rstr._rstrFormula) $ fm'
transformWithPullnots f = case pullnots f of
    Left _ -> f
    Right f' -> f'
gf = formulaToGuarded_ $ transformWithPullnots $ transformWithStamps rstr._rstrFormula-}

-- | Printer for reuse/src lemmas.
-- | Different than ppLemma in that it ignores timepoints and does transformations custom to these lemmas.
ppReuseSrcLemma :: TypingEnvironment -> Lemma ProofSkeleton -> Doc
ppReuseSrcLemma te l =
  text "(*"
    <> text l._lName
    <> text "*)"
    $$ Precise.evalFresh (ppRestrictFormulaR RSL te fm) (avoidPrecise fm)
  where
    fm = allImplExLessWoTmps $ transformWithPullNots $ transformWithStamps l._lFormula

{-fm = transformWithPullnots $ case parseString [] "" plainFormula $ render $ prettyGuarded gf of
       Left _ -> error "should not happen"
       Right fm' -> fm' --- trace (show $ render $ prettyGuarded $ formulaToGuarded_ rstr._rstrFormula) $ fm'
transformWithPullnots f = case pullnots f of
    Left _ -> f
    Right f' -> f'
gf = formulaToGuarded_ $ transformWithStamps l._lFormula-}

-- Check if a formula is of the form "All x1 .. xn tA. A(x1 ... xn)@tA ==> not (Ex y1 ... yn tB. B(y1 ... yn)@tB)"
allActImplsNotExAct :: LNFormula -> Bool
allActImplsNotExAct (Qua All _ body) = allActImplsNotExAct body
allActImplsNotExAct f@(Conn Imp p@(Ato at) (Not q)) = isActionAtom at && onlyEx q
  where
    onlyEx (Qua Ex _ body') = onlyEx body'
    onlyEx (Ato a) = isActionAtom a
    onlyEx _ = False
allActImplsNotExAct _ = False

-- Check if a formula is of the form "All x1 .. xn tA. A(x1 ... xn)@tA ==> Ex y1 ... yn tB. B(y1 ... yn)@tB"
-- We reject such formulas as lemmas/axioms/restrictions.
allActImplsExAct :: LNFormula -> Bool
allActImplsExAct (Qua All _ body) = allActImplsExAct body
allActImplsExAct f@(Conn Imp p@(Ato at) q) = isActionAtom at && onlyEx q
  where
    onlyEx (Qua Ex _ body') = onlyEx body'
    onlyEx (Ato a) = isActionAtom a
    onlyEx _ = False
allActImplsExAct _ = False

-- Check if a formula is of the form "All x1 .. xn tA. A(x1 ... xn)@tA ==> Ex y1 ... yn tB. B(y1 ... yn)@tB & tB < tA"
-- If so, remove the less (it's implicit as we translate to a basic correspondence).
allImplExLessWoTmps :: LNFormula -> LNFormula
allImplExLessWoTmps (Qua All x p) = Qua All x $ allImplExLessWoTmps p
allImplExLessWoTmps (Conn Imp (Ato (Action tA fA)) q) = Conn Imp (Ato (Action tA fA)) $ case q of
  (Qua Ex x p) -> Qua Ex x $ onlyEx p
  f -> f
  where
    onlyEx (Qua Ex x p) = Qua Ex x $ onlyEx p
    onlyEx f@(Conn And (Ato (Action tB fB)) (Ato (Less tB' tA'))) = if tA == tA' && tB == tB' then Ato (Action tB fB) else f
    onlyEx f = f
allImplExLessWoTmps f = f

transformWithStamps :: LNFormula -> LNFormula
transformWithStamps f = if snd $ go False f then forAll ("st0", LSortFresh) (LVar "st0" LSortFresh 0) $ forAll ("st1", LSortFresh) (LVar "st1" LSortFresh 1) $ fst $ go False f else fst $ go False f
  where
    go False (Qua All s fm) = (Qua All s $ fst $ go False fm, snd recCall)
      where
        recCall = go False fm
    go False fm@(Conn Imp (Conn And l r) tmpEq) = case (l, r, tmpEq) of
      (Ato (Action i1 (Fact (ProtoFact m1 name1 arr1) ann1 ts1)), Ato (Action i2 (Fact (ProtoFact m2 name2 arr2) ann2 ts2)), Ato (EqE t1 t2)) ->
        -- matches both OnlyOnce and Unique restriction types
        if ((i2 == t1 && i1 == t2) || (i1 == t1 && i2 == t2)) && name1 == name2
          then (Conn Imp (Conn And l' r') tmpEq', True)
          else (fm, False)
        where
          l' = Ato (Action i1 (Fact (ProtoFact m1 (newName name1) (arr1 + 1)) ann1 (varTerm (Free $ LVar "st0" LSortFresh 0) : ts1)))
          r' = Ato (Action i2 (Fact (ProtoFact m2 (newName name2) (arr2 + 1)) ann2 (varTerm (Free $ LVar "st1" LSortFresh 1) : ts2)))
          tmpEq' = Ato (EqE (varTerm (Free $ LVar "st0" LSortFresh 0)) (varTerm (Free $ LVar "st1" LSortFresh 1)))
          newName "OnlyOnce" = "OnlyOnce"
          newName name = "U" ++ name
      (Conn And (Ato (Action i1 (Fact (ProtoFact m1 name1 arr1) ann1 ts1))) (Ato (Action i2 (Fact (ProtoFact m2 name2 arr2) ann2 _))), Ato (EqE tA tB), Ato (EqE t1 t2)) ->
        -- handle the OnlyOnce variant with A=B in addition to the OnlyOnces
        if ((i2 == t1 && i1 == t2) || (i1 == t1 && i2 == t2)) && name1 == name2 -- hacky, but ProVerif does not have a problem with the dangling B
          then (Conn Imp (Conn And l' r') tmpEq', True)
          else (fm, False)
        where
          l' = Ato (Action i1 (Fact (ProtoFact m1 "OnlyOnce" (arr1 + 1)) ann1 (varTerm (Free $ LVar "st0" LSortFresh 0) : ts1)))
          r' = Ato (Action i2 (Fact (ProtoFact m2 "OnlyOnce" (arr2 + 1)) ann2 (varTerm (Free $ LVar "st1" LSortFresh 1) : ts1)))
          tmpEq' = Ato (EqE (varTerm (Free $ LVar "st0" LSortFresh 0)) (varTerm (Free $ LVar "st1" LSortFresh 1)))
      _ -> (fm, False)
    go _ fm = (fm, False)

loadRestrictions ::
  TranslationContext ->
  TypingEnvironment ->
  OpenTheory ->
  [Doc]
loadRestrictions _ te thy = map (ppRestr te) thyRestrs
  where
    thyRestrs = theoryRestrictions thy

findActsByTmp :: (Eq t) => [GAtom t] -> t -> [GAtom t]
findActsByTmp (a : as) tmp = case a of
  GEqE _ _ -> findActsByTmp as tmp
  GAction t _ -> if t == tmp then a : findActsByTmp as tmp else findActsByTmp as tmp
findActsByTmp [] _ = []

{-modifyAtoms :: ((Integer, Atom (VTerm Name (BVar LVar))) -> (Integer, Atom (VTerm Name (BVar LVar)))) -> (Integer, LNGuarded) -> (Integer, LNGuarded)
modifyAtoms f (i, GDisj d) = (i, GDisj $ Disj $ map (\a -> snd $ modifyAtoms f (i,a)) $ getDisj d)
modifyAtoms f (i, GConj c) = (i, GConj $ Conj $ map (\a -> snd $ modifyAtoms f (i,a)) $ getConj c)
modifyAtoms f (i, GGuarded q vs gas gf) = case q of
                                            All -> (i, GGuarded q vs (modifiedAtoms i gas) (snd $ modifyAtoms f (i, gf)))
                                            Ex -> (i, GGuarded q vs gas gf)
    where
        modifiedAtoms ind = snd . foldl (\(i, acc) a -> (fst (f (i, a)), acc ++ [snd (f (i, a))])) (ind, [])
        -- modifiedFormulas ind = snd . foldl (\(i, acc) a -> (fst (modifyAtoms i a), acc ++ [snd (modifyAtoms i a)])) (ind, [])
modifyAtoms f (i, GAto a) = (i, GAto $ snd $ f (i, a))

modifyOnlyOnceAtom :: Integer -> Atom (VTerm Name (BVar LVar)) -> Atom (VTerm Name (BVar LVar))
modifyOnlyOnceAtom i a = case a of
                            Action t f -> case f of
                                              Fact (ProtoFact m "OnlyOnce" arr) ann ts -> Action t (Fact (ProtoFact m "OnlyOnce" (arr+1)) ann (varTerm (Bound i):ts))
                                              _ -> a
                            _ -> a

modifyOnlyOnceEqe :: Integer -> Atom (VTerm Name (BVar LVar)) -> Atom (VTerm Name (BVar LVar))
modifyOnlyOnceEqe i a = case a of
                            EqE t1 t2 -> if True then EqE (varTerm (Bound (i-1))) (varTerm (Bound i)) else a
                            _ -> a

varVecLen :: LNGuarded -> Integer
varVecLen (GGuarded _ vs _ _) = genericLength vs
varVecLen _ = 0-}

{-modifyAtoms :: LNFormula -> LNFormula
modifyAtoms = mapAtoms (\_ a -> case a of
                                       Action _ f -> case f of
                                                         Fact tag an terms -> case tag of
                                                             ProtoFact _ "OnlyOnce" _ -> ProtoFact _ "OnlyOnce" _
                                                             _ -> a
                                                         _ -> a
                                       _ -> a)-}
