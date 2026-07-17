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
import Extension.Data.Label qualified as L
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

-- ===========================================================================
-- SECTION 1: Module Header & Types
-- ===========================================================================

-- | Types of translation the export module covers (others are covered by sapic module).
data Translation
  = ProVerif
  | DeepSec
  deriving (Ord, Eq, Typeable, Data)

-- | Types of translations covered here map to other modules, but not vice versa (for instance, Sapic to MSR).
exportModule :: Translation -> ModuleType
exportModule ProVerif = ModuleProVerif
exportModule DeepSec = ModuleDeepSec

-- | Classification for how a lemma should be translated
data LemmaTranslationMode
  = AsQuery       -- ^ Regular lemma, translate as query
  | AsAxiom       -- ^ Reuse/source lemma, translate as axiom
  | ExcludeLemma  -- ^ Don't translate at all
  deriving (Eq, Ord, Show)

-- | Information needed during translation.
data TranslationContext = TranslationContext
  { trans :: Translation,
    attackerChannel :: Maybe LVar,
    hasBoundStates :: Bool,
    hasUnboundStates :: Bool,
    predicates :: [Predicate],
    replicationBound :: Int,
    skipReuseLemmas :: Bool,
    skipSourceLemmas :: Bool,
    skipRestrictions :: Bool,
    skipPrecise :: Bool
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
      skipReuseLemmas = False,
      skipSourceLemmas = False,
      skipRestrictions = False,
      skipPrecise = False
    }

-- ===========================================================================
-- Helper Functions for Formula Construction
-- ===========================================================================

-- | Build a conjunction from a list of formulas.
-- Returns True for empty list, single formula unchanged, otherwise folds with .&&.
buildConjunction :: [LNFormula] -> LNFormula
buildConjunction [] = TF True
buildConjunction [f] = f
buildConjunction fs = foldr1 (.&&.) fs

-- | Build a disjunction from a list of formulas.
-- Returns False for empty list, single formula unchanged, otherwise folds with .||.
buildDisjunction :: [LNFormula] -> LNFormula
buildDisjunction [] = TF False
buildDisjunction [f] = f
buildDisjunction fs = foldr1 (.||.) fs

-- | Rebuild a quantifier prefix around a body that already contains the
-- corresponding de Bruijn-bound variables. This deliberately uses 'Qua'
-- directly: 'forAll' and 'exists' quantify free variables instead.
-- Quantifiers are applied from outer to inner, so the first hint becomes the
-- outermost quantifier.
rewrapBoundPrefix :: Quantifier -> [(String, LSort)] -> LNFormula -> LNFormula
rewrapBoundPrefix _ [] body = body
rewrapBoundPrefix q (v:vs) body = Qua q v (rewrapBoundPrefix q vs body)

-- | Check if a formula represents a valid existential disjunction pattern.
-- Valid patterns include:
-- - An existential formula with quantifier-free body
-- - A disjunction of existential formulas
-- - A temporal/equality constraint: #i < #j, x = y
-- - A bare action atom (from moved negated actions)
-- - A nested implication: All x. P => Q (where Q is valid conclusion)
isExistentialDisjunction :: MonadFresh m => LNFormula -> m Bool
isExistentialDisjunction fm@(Qua Ex _ _) = do
  (_, _, fm') <- openFormulaPrefix fm
  -- Accept either quantifier-free bodies or nested existential/disjunctive structure.
  if isQuantifierFree fm'
    then pure True
    else isExistentialDisjunction fm'
-- Handle universals (nested implications): All x. P => Q
isExistentialDisjunction fm@(Qua All _ _) = do
  (_, _, fm') <- openFormulaPrefix fm
  isExistentialDisjunction fm'
-- Handle implications: P => Q (nested implication body)
isExistentialDisjunction (Conn Imp p q) | isQuantifierFree p = do
  -- The premise must be quantifier-free, conclusion can be:
  -- quantifier-free, existential, or another nested implication
  if isQuantifierFree q
    then pure True
    else isExistentialDisjunction q
-- Handle disjunctions: (Ex...) | (Ex...) | ...
isExistentialDisjunction (Conn Or fm1 fm2) = do
  b1 <- isExistentialDisjunction fm1
  b2 <- isExistentialDisjunction fm2
  pure $ b1 && b2
-- Handle conjunctions: (Ex...) & (Ex...) & ... or (All...) & (Ex...)
-- This allows patterns like: ((Ex #j. A@j) & (Ex #k. B@k)) | ((Ex #r. C@r) & (Ex #t. D@t))
-- Also allows: (All #j. B@j => C) & (Ex #k. D@k)
isExistentialDisjunction (Conn And fm1 fm2) = do
  b1 <- isExistentialDisjunction fm1
  b2 <- isExistentialDisjunction fm2
  pure $ b1 && b2
isExistentialDisjunction fm | isConstraintAtom fm = pure True
isExistentialDisjunction fm | isBareActionAtom fm = pure True
isExistentialDisjunction _ = pure False

-- | Check if a formula is a temporal or equality constraint
isConstraintAtom :: LNFormula -> Bool
isConstraintAtom (Ato (Less _ _)) = True
isConstraintAtom (Ato (EqE _ _)) = True
isConstraintAtom (Not (Ato (EqE _ _))) = True
isConstraintAtom (Conn Or f1 f2) = isConstraintAtom f1 && isConstraintAtom f2
isConstraintAtom _ = False

-- | Check if a formula is a bare action atom
isBareActionAtom :: LNFormula -> Bool
isBareActionAtom (Ato (Action _ _)) = True
isBareActionAtom _ = False

-- | Check if a formula is a nested implication that can be flattened.
-- Pattern: All x. Q => R  where Q is quantifier-free and R is quantifier-free or existential disjunction
-- This is equivalent to adding Q to the premise.
isNestedImplicationOk :: MonadFresh m => LNFormula -> m Bool
isNestedImplicationOk fm@(Qua All _ _) = do
  (_, _, fm') <- openFormulaPrefix fm
  isNestedImplicationOk fm'
isNestedImplicationOk (Conn Imp q r) | isQuantifierFree q = do
  -- The nested premise q must be quantifier-free
  -- The nested conclusion r can be:
  -- 1. Quantifier-free (like #i < #j)
  -- 2. An existential disjunction
  -- 3. Another nested implication
  if isQuantifierFree r
    then pure True
    else do
      isExDisj <- isExistentialDisjunction r
      if isExDisj
        then pure True
        else isNestedImplicationOk r
isNestedImplicationOk _ = pure False

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

proverifTemplate :: (Document d) => Bool -> [d] -> [d] -> d -> [d] -> [d] -> [d] -> [d] -> [d] -> [d] -> d
proverifTemplate skipPrecise headers queries process macroproc ruleproc restrictions axioms lemmas comments =
  (if skipPrecise then text "" else text "set preciseActions = true.")
    $$ vcat headers
    $$ vcat queries
    $$ (if null restrictions then text "" else text "" $$ text "(* Restrictions *)" $$ text "" $$ vcat restrictions)
    $$ (if null axioms then text "" else text "" $$ text "(* Axioms from reuse/source lemmas *)" $$ text "" $$ vcat axioms)
    $$ (if null lemmas then text "" else text "" $$ text "(* Lemmas (queries) *)" $$ text "" $$ vcat lemmas)
    $$ vcat macroproc
    $$ vcat ruleproc
    $$ text "" $$ text "(* Process *)" $$ text ""
    $$ text "process"
    $$ nest 4 process
    $--$ vcat (intersperse (text "") comments)

prettyProVerifTheory ::
  ModuleType ->
  Bool -> -- noReuseLemmas
  Bool -> -- noSourceLemmas
  Bool -> -- noRestrictions
  Bool -> -- noMultiset
  Bool -> -- noPrecise
  Bool -> -- hasSpecificLemmas
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  (OpenTheory, TypingEnvironment) ->
  IO Doc
prettyProVerifTheory m noReuseLemmas noSourceLemmas noRestrictions noMultiset noPrecise hasSpecificLemmas lemSel (thy', typEnv) = do
  headersTheory <- loadHeaders sharedEventTags tc thy typEnv -- load headers from theory
  let headersTranslation =
        [ baseHeaders, -- base headers for translation
          prochd, -- headers from the process
          macroprochd, -- headers from the macroprocess
          ruleHeaders, -- headers from the rules
          lemmaHeaders, -- headers from the lemmas
          restrictionHeaders -- headers from the restrictions
        ]
  headers <- checkDuplicates' $ filterHeaders $ S.unions $ headersTheory : headersTranslation
  let hd = attribHeaders tc headers
  pure $ proverifTemplate (skipPrecise tc) hd queries proc' macroproc ruleproc restrictions axioms lemmas comments
  where
    thy = if noMultiset then thy' else multisetTheory thy'

    tc =
      emptyTC
        { predicates = theoryPredicates thy,
          skipReuseLemmas = noReuseLemmas,
          skipSourceLemmas = noSourceLemmas,
          skipRestrictions = noRestrictions,
          skipPrecise = noPrecise
        }
    (proc, prochd, hasBoundState, hasUnboundState) = loadProc tc thy
    proc'
      | null (theoryProcesses thy) = ruleComb
      | null (theoryRules thy) = proc
      | otherwise = proc <-> text "|" <-> ruleComb
    baseHeaders = if hasUnboundState then stateHeaders else S.empty
    -- Compute shared events from both lemmas and restrictions
    lemmaSharedEvents = detectSharedTimepointEvents (filter lemSel (theoryLemmas thy))
    restrictionSharedEvents = detectSharedTimepointEventsRestrictions (theoryRestrictions thy)
    sharedEventTags = lemmaSharedEvents `S.union` restrictionSharedEvents
    (restrictions, restrictionHeaders) =
      if skipRestrictions tc
        then ([], S.empty)
        else loadRestrictions sharedEventTags tc typEnv thy
    queries = loadQueries thy
    (axioms, lemmas, lemmaHeaders) = loadLemmas sharedEventTags hasSpecificLemmas lemSel tc typEnv thy
    (ruleproc, ruleComb, ruleHeaders) = loadRules sharedEventTags thy m
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
      -- Note: The following commented out functions and equations are not supported by ProVerif.
      -- Fun "fun" "inv" 1 "(bitstring):bitstring" [],
      -- Eq "equation" "forall a:bitstring,b:bitstring;" "exp( exp(a,b), inv(b)) = a" "",
      -- Eq "equation" "forall a:bitstring;" "inv( inv(a)) = a" ""
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
getProVerifHeaderIdentifier (Fun _ n _ _ _) = Just n
getProVerifHeaderIdentifier (Sym _ n _ _) = Just n
getProVerifHeaderIdentifier (HEvent n _) = Just n
getProVerifHeaderIdentifier (Table n _) = Just n
getProVerifHeaderIdentifier _ = Nothing

-- | Fail if any identifier occurs more than once; otherwise return all headers
checkDuplicates :: (MonadFail m) => [ProVerifHeader] -> m [ProVerifHeader]
checkDuplicates headers = do
  let identMap :: M.Map String [ProVerifHeader]
      identMap =
        M.fromListWith
          (<>)
          [ (n, [h])
            | h <- headers,
              Just n <- [getProVerifHeaderIdentifier h]
          ]
      conflicts = M.toList $ M.filter ((> 1) . length) identMap

  -- if there are conflicts, bail; otherwise return the whole input
  unless (null conflicts) $
    fail $
      unlines
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
  _ -> "v" ++ n

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
  headersTheory <- loadHeaders S.empty tc thy typEnv
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
  headers <- loadHeaders S.empty tc thy emptyTypeEnv
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

-- | Print a variable name. For timepoint (node) variables, we need to ensure
-- they don't collide with term variables of the same name. In Tamarin, #t and t
-- are different variables, but in ProVerif they would both become 't'.
-- We handle this by checking the sort and NOT adding a prefix here - instead,
-- we use a separate function for timepoint variables in query declarations.
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

-- | Render a term and collect required ProVerif header declarations.
-- Takes a literal rendering function and a term, returns the rendered
-- Doc and the set of headers needed for declarations (e.g., free constants).
renderTermWithHeaders :: (Show v) => (Lit Name v -> Doc) -> VTerm Name v -> (Doc, S.Set ProVerifHeader)
renderTermWithHeaders ppLit t = (ppTerm t, getHdTerm t)
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

-- | Render a SapicTerm, collecting the constants that need to be declared.
-- matchVars is the set of vars that correspond to pattern matching.
-- isPattern enables pattern match printing, which adds types to variables and = to constants.
renderSapicTermWithPattern :: TranslationContext -> S.Set LVar -> Bool -> SapicTerm -> (Doc, S.Set ProVerifHeader)
renderSapicTermWithPattern tc mVars isPattern = renderTermWithHeaders ppLit
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
              $ if isPattern || S.member lvar mVars
                  then text "=" <> ppLVar lvar
                  else ppLVar lvar
      Var (SapicLVar lvar _)
        | S.member lvar mVars -> text "=" <> ppLVar lvar
      l | isPattern -> ppTypeLit tc l
      Var (SapicLVar lvar _) -> ppLVar lvar
      l -> text . sanitizeSymbol 'a' $ show l

ppSapicTerm :: TranslationContext -> SapicTerm -> (Doc, S.Set ProVerifHeader)
ppSapicTerm tc = renderSapicTermWithPattern tc S.empty False

-- | Render an LNTerm, collecting the constants that need to be declared.
-- The boolean parameter enables type annotations in the output.
renderLNTermTyped :: TranslationContext -> Bool -> LNTerm -> (Doc, S.Set ProVerifHeader)
renderLNTermTyped _ includeTypes = renderTermWithHeaders ppLit
  where
    ppLit v = case v of
      Con (Name FreshName n) -> text . sanitizeSymbol 'a' $ show n
      Con (Name PubName n) -> ppPubName n
      tm2 | includeTypes -> text $ sanitizeSymbol 'a' (show tm2) <> ":bitstring"
      Var lvar -> ppLVar lvar
      tm2 -> text . sanitizeSymbol 'a' $ show tm2

ppLNTerm :: TranslationContext -> LNTerm -> (Doc, S.Set ProVerifHeader)
ppLNTerm tc = renderLNTermTyped tc False

-- | Render a Fact, collecting the constants that need to be declared.
ppFact :: TranslationContext -> Fact SapicTerm -> (Doc, S.Set ProVerifHeader)
ppFact tc (Fact tag _ ts)
  | factTagArity tag /= length ts = renderFactWithName ("MALFORMED-" ++ show tag) ts
  | otherwise = renderFactWithName ('e' : factTagName tag) ts
  where
    renderFactWithName name ts2 =
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
    (pt2, sh2) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t2
ppAction _ tc@TranslationContext {trans = DeepSec} (ChIn t1 t2@(LIT (Var (SapicLVar _ _))) mvars) =
  ( text "in(" <> pt1 <> text "," <> pt2 <> text ")",
    sh1 `S.union` sh2,
    True
  )
  where
    (pt1, sh1) = getAttackerChannel tc t1
    (pt2, sh2) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t2

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
    (pt2, sh2) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t2
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
    (pt, sh) = renderSapicTermWithPattern tc freevars True t
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
ppAction _ TranslationContext {trans = ProVerif} (MSR prems acts concs rests matchVars)
  | not (null rests) =
      translationFail "Embedded MSR constraints are currently not supported for ProVerif export."
  | otherwise =
      (msrDoc, msrHeaders, hasTailDocs)
  where
    lnPrems = map toLNFact prems
    lnActs = map toLNFact acts
    lnConcs = map toLNFact concs
    matched = S.map (show . toLVar) matchVars
    (msrDoc, msrHeaders, hasTailDocs) = translateEmbeddedRuleAction matched lnPrems lnActs lnConcs
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
    (pt1, sh1) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t1
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
    (pt1, sh1) = renderSapicTermWithPattern tc (S.map toLVar mvars) True t1
    (pt2, sh2) = ppSapicTerm tc t2

-- if the process call does not have any argument, we just inline
ppSapic tc (ProcessAction (ProcessCall _ []) _ pl) = (ppl, pshl)
  where
    (ppl, pshl) = ppSapic tc pl

-- if there are state or lock channels created by addStateChannels, we must inline
ppSapic tc@TranslationContext {hasBoundStates = True} (ProcessAction (ProcessCall {}) _ pl) =
  (ppl, pshl)
  where
    (ppl, pshl) = ppSapic tc pl
ppSapic tc (ProcessAction (ProcessCall name ts) _ _) =
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
        Right form -> (fst . snd $ Precise.evalFresh (ppLFormula emptyTypeEnv (ppNAtom M.empty S.empty) form) (avoidPrecise form), S.empty)
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
    (pt, sh) = renderSapicTermWithPattern tc freevars True t
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
    (pt, sh) = renderSapicTermWithPattern tc freevars True t
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
      Just (Predicate _ form) -> Precise.evalFresh (ppLFormula emptyTypeEnv (ppNAtom M.empty S.empty) form) (avoidPrecise form)

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
  (Term (Lit c k) -> Maybe d) -> -- per-occurrence rule-id variable of a timepoint variable, if any
  S.Set String -> -- events requiring rule identifiers
  TypingEnvironment ->
  Bool ->
  (s (Term (Lit c k)) -> d) ->
  (Term (Lit c k) -> d) ->
  ProtoAtom s (Term (Lit c k)) ->
  (d, M.Map k SapicType)
ppProtoAtom ridOf ruleIdEvents te _ _ ppT (Action v f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | (tag == KUFact) || isKLogFact f -- treat KU() and K() facts the same
    =
      (ppFactL "attacker" ts <> opAction <> ppT v, M.empty)
  | otherwise =
      ( text "event("
          <> eventArgs ('e' : factTagName tag) ts
          <> text ")"
          <> opAction
          <> ppT v,
        typeVarsEvent te tag ts
      )
  where
    factName = factTagName tag
    useRuleId = factName `S.member` ruleIdEvents
    ppFactL n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppT t
    eventArgs n t
      | useRuleId = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ (ridDoc : map ppT t)
      | otherwise = ppFactL n t
    ridDoc = fromMaybe (text "rid") (ridOf v)
ppProtoAtom _ _ _ _ ppS _ (Syntactic s) = (ppS s, M.empty)
-- A temporal equality between rule-id instrumented events is translated as an
-- equality of their rule-id variables: distinct ProVerif events never share a
-- timepoint, while in Tamarin equal timepoints mean "same rule instance".
ppProtoAtom ridOf _ _ False _ ppT (EqE l r) =
  case (ridOf l, ridOf r) of
    (Just dl, Just dr) -> (sep [dl <-> opEqual, dr], M.empty)
    _ -> (sep [ppT l <-> opEqual, ppT r], M.empty)
ppProtoAtom ridOf _ _ True _ ppT (EqE l r) =
  case (ridOf l, ridOf r) of
    (Just dl, Just dr) -> (sep [dl <-> text "<>", dr], M.empty)
    _ -> (sep [ppT l <-> text "<>", ppT r], M.empty)
-- sep [ppNTerm l <-> text "≈", ppNTerm r]
ppProtoAtom _ _ _ _ _ ppT (Less u v) = (ppT u <-> opLess <-> ppT v, M.empty)
ppProtoAtom _ _ _ _ _ ppT (Subterm u v) = (text "subterm(" <> ppT u <> comma <> ppT v <> text ")", M.empty)
ppProtoAtom _ _ _ _ _ _ (Last i) = (operator_ "last" <> parens (text (show i)), M.empty)

ppAtom :: M.Map String String -> S.Set String -> TypingEnvironment -> Bool -> (LNTerm -> Doc) -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppAtom ridNames ruleIdEvents te b = ppProtoAtom ridOf ruleIdEvents te b (const emptyDoc)
  where
    ridOf t = case viewTerm t of
      Lit (Var (LVar n LSortNode _)) -> text <$> M.lookup n ridNames
      _ -> Nothing

-- only used for ProVerif queries display
-- the Bool is set to False when we must negate the atom
ppNAtom :: M.Map String String -> S.Set String -> TypingEnvironment -> Bool -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppNAtom ridNames ruleIdEvents te b = ppAtom ridNames ruleIdEvents te b (fst . ppLNTerm emptyTC)

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
  printFormula
  where
    printFormula (Ato a) = pure ([], ppAt te False (toLAt a))
    printFormula (TF True) = pure ([], (operator_ "true", M.empty)) -- "T"
    printFormula (TF False) = pure ([], (operator_ "false", M.empty)) -- "F"
    printFormula (Not (Ato a@(EqE _ _))) = pure ([], ppAt te True (toLAt a))
    printFormula (Not p) = do
      (vs, (p', envp)) <- printFormula p
      pure (vs, (operator_ "not" <> opParens p', envp)) -- text "¬" <> parens (printFormula a)
      -- pure $ operator_ "not" <> opParens p' -- text "¬" <> parens (printFormula a)
    printFormula (Conn op p q) = do
      (vsp, (p', envp)) <- printFormula p
      (vsq, (q', envq)) <- printFormula q
      pure (vsp ++ vsq, (sep [opParens p' <-> ppOp op, opParens q'], mergeEnv envp envq))
      where
        ppOp And = text "&&"
        ppOp Or = text "||"
        ppOp Imp = text "==>"
        ppOp Iff = opIff
    printFormula fm@(Qua {}) =
      scopeFreshness $ do
        (vs, _, fm') <- openFormulaPrefix fm
        (vsp, d') <- printFormula fm'
        pure (vs ++ vsp, d')

-- | Check if a formula is quantifier-free.
isQuantifierFree :: LNFormula -> Bool
isQuantifierFree (Qua {}) = False
isQuantifierFree (Ato _) = True
isQuantifierFree (TF _) = True
isQuantifierFree (Not p) = isQuantifierFree p
isQuantifierFree (Conn _ p q) = isQuantifierFree p && isQuantifierFree q

-- | Count the number of quantifier alternations in a formula.
-- An alternation occurs when we switch from All to Ex or vice versa.
-- For example:
--   All x. P(x)                     -> 0 alternations (All only)
--   All x. Ex y. P(x,y)             -> 1 alternation  (All -> Ex)
--   All x. Ex y. not(Ex z. Q)       -> 2 alternations (All -> Ex -> All, since not(Ex) = All)
--   All x. (P(x) => Ex y. Q(y))     -> 1 alternation  (All -> Ex)
-- The supported fragment has at most 1 alternation: All* (premise => Ex* conclusion)
countQuantifierAlternations :: LNFormula -> Int
countQuantifierAlternations = go Nothing
  where
    -- go tracks the current quantifier context (Nothing = none yet, Just All/Ex = last seen)
    go :: Maybe Quantifier -> LNFormula -> Int
    go _ (Ato _) = 0
    go _ (TF _) = 0
    go ctx (Not (Qua Ex v body)) = go ctx (Qua All v body)  -- not(Ex) = All
    go ctx (Not (Qua All v body)) = go ctx (Qua Ex v body)  -- not(All) = Ex
    go ctx (Not body) = go ctx body
    go ctx (Qua q _ body) =
      let alternation = case ctx of
            Nothing -> 0  -- First quantifier, no alternation
            Just q' -> if q == q' then 0 else 1  -- Same quantifier = 0, different = 1
          bodyAlternations = go (Just q) body
      in alternation + bodyAlternations
    go ctx (Conn _ p q) = max (go ctx p) (go ctx q)

ppQueryFormula ::
  (MonadFresh m) =>
  M.Map String String ->
  S.Set String ->
  TypingEnvironment ->
  ProtoFormula Unit2 (String, LSort) Name LVar ->
  [LVar] ->
  String ->
  m Doc
ppQueryFormula ridNames ruleIdEvents te fm extravs attrs = do
  (vs, (p, typeVars)) <- ppLFormula te (ppNAtom ridNames ruleIdEvents) fm
  -- The shared "rid" variable is needed for rule-id instrumented events
  -- without a per-occurrence rule-id variable (see ridOccurrenceNames);
  -- the per-occurrence variables are declared separately below.
  let includeRuleId
        | M.null ridNames = formulaUsesRuleIdEvents ruleIdEvents fm
        | otherwise =
            any
              (\(tv, tag) -> tag `S.member` ruleIdEvents && tv `M.notMember` ridNames)
              (collectEventTimeVars fm)
  let ruleIdVar = text "rid:bitstring"
  let ridEqVars = [text (n ++ ":bitstring") | n <- S.toList . S.fromList $ M.elems ridNames]
  let allVarsList = S.toList . S.fromList $ extravs ++ vs
  -- Check for name collisions between term and timepoint variables
  -- In Tamarin, t and #t are different, but in ProVerif they'd both be 't'
  let termVarNames = S.fromList [n | LVar n s _ <- allVarsList, s /= LSortNode]
  let timepointVarsWithCollision = [n | LVar n LSortNode _ <- allVarsList, S.member n termVarNames]
  -- If there's a collision, we can't translate this query
  if not (null timepointVarsWithCollision)
    then pure $ text "(* Variable name collision: '" <> text (head timepointVarsWithCollision) <>
                text "' is used both as term and timepoint. Please rename one in the Tamarin source. *)"
    else do
      let allVars = map (ppTimeTypeVar typeVars) allVarsList
      let quantifiedVars =
            [ruleIdVar | includeRuleId] ++ ridEqVars ++ allVars
      let queryLine =
            case quantifiedVars of
              [] -> text "query;"
              _ -> text "query " <> fsep (punctuate comma quantifiedVars) <> text ";"
      let attrsDoc = if null attrs then text "" else text attrs
      pure $
        sep
          [ queryLine,
            nest 1 p <> attrsDoc <> text "."
          ]

ppTimeTypeVar :: M.Map LVar SapicType -> LVar -> Doc
ppTimeTypeVar _ lvar@(LVar _ LSortNode _) = ppLVar lvar <> text ":time"
ppTimeTypeVar te lvar =
  case M.lookup lvar te of
    Nothing -> ppLVar lvar <> text ":bitstring"
    Just t -> ppLVar lvar <> text ":" <> text (ppType t)

ppQueryFormulaEx :: M.Map String String -> S.Set String -> TypingEnvironment -> LNFormula -> [LVar] -> String -> Doc
ppQueryFormulaEx ridNames ruleIdEvents te fm vs attrs =
  Precise.evalFresh (ppQueryFormula ridNames ruleIdEvents te fm vs attrs) (avoidPrecise fm)

ppRestrictFormula ::
  M.Map String String ->
  S.Set String ->
  TypingEnvironment ->
  ProtoFormula Unit2 (String, LSort) Name LVar ->
  String ->
  Precise.FreshT Data.Functor.Identity.Identity (Doc, Bool)
ppRestrictFormula ridNames ruleIdEvents te frm attrs =
  if any (\(Fact tag _ _) -> factTagName tag == "KU") $ formulaFacts frm
    then -- todo: Add all translation warnings to the wellformedness report.
      pure (ppFail (Just "lemma contains KU fact") frm, False)
    else renderFormula frm
  where
    -- attrs contains lemma attributes like "[induction]" but these don't affect
    -- ProVerif translation - they are Tamarin-specific proving hints
    _attrs = attrs  -- suppress unused warning

    renderFormula (Not fm@(Qua Ex _ _)) = do
      (vs, _, fm') <- openFormulaPrefix fm
      pure
        ( if isQuantifierFree fm'
            then (ppOk fm' vs, True)
            else (ppFail (Just "lemma is not quantifier-free") fm, False)
        )
    -- Handle Not(All...) - translate the inner All formula and mark as having leading negation
    renderFormula (Not fm@(Qua All _ _)) = do
      (_, _, fm') <- openFormulaPrefix fm
      (doc, succeeded) <- handleUniversalFormula fm fm'
      pure (doc, succeeded)  -- The caller will add the leading negation comment
    renderFormula fm@(Qua Ex _ _) = do
      (vs, _, fm') <- openFormulaPrefix fm
      pure
        ( if isQuantifierFree fm'
            then (ppOk fm' vs, True)
            else (ppFail (Just "lemma is not quantifier-free") fm, False)
        )
    renderFormula fm@(Qua All _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      handleUniversalFormula fm fm'
    renderFormula fm = pure (ppFail (Just "Lemma outside of logic fragment") fm, False)
    ppOk f l = ppQueryFormulaEx ridNames ruleIdEvents te f l attrs
    ppFail Nothing fm = text "(* Lemma outside of logic fragment *)" $$ text "(*" <> prettyLNFormula fm <> text "*)"
    ppFail (Just reason) fm = text "(*" <> text reason <> text "*)" $$ text "(*" <> prettyLNFormula fm <> text "*)"

    handleUniversalFormula fm_original fm | isQuantifierFree fm = pure (ppOk fm_original [], True)
    handleUniversalFormula fm_original (Conn Imp p fm) | isQuantifierFree p = do
      isExDisj <- isExistentialDisjunction fm
      if isExDisj
        then pure (ppOk fm_original [], True)
        else do
          -- Try handling nested implications/universals
          -- Pattern: P => (All x. Q => R) is equivalent to P & Q => R (with x bound)
          isNestedOk <- isNestedImplicationOk fm
          pure $
            if isNestedOk
              then (ppOk fm_original [], True)
              else (ppFail (Just "conclusion is not an existential disjunction") fm_original, False)
    -- Handle Ex... (P => Q) case - existentials wrapping an implication
    -- This arises from transforming not(Ex... P & not(Ex... Q))
    handleUniversalFormula fm_original fm@(Qua Ex _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      handleUniversalFormula fm_original fm'

    handleUniversalFormula fm_original _fm_inner =
      pure (ppFail (Just "Lemma outside of logic fragment") fm_original, False)

-- ===========================================================================
-- SECTION 7: Lemma Translation
-- ===========================================================================

-- | Translate a lemma formula for ProVerif output.
-- This function translates ONLY lemmas in the "classical way" with timepoints.
-- The resulting translations are suitable only as ProVerif queries (not lemmas/axioms/restrictions).
--
-- Key steps:
-- 1. Simplify and apply rewriting transformations
-- 2. Split shared timepoints if needed
-- 3. Split top-level connectives (AND for all-traces, OR for exists-trace)
-- 4. Apply final transformations and print each subformula
ppLemma :: S.Set String -> TypingEnvironment -> Lemma ProofSkeleton -> Doc
ppLemma ruleIdEvents te p =
  let subformulas = vcat (intersperse (text "") (zipWith (curry renderSubformula) fms hadNegationFlags))
  in if isEmpty comments
     then subformulas $$ text ""
     else subformulas $$ text "" $$ reconstructionComment
  where
    simplifiedFormula = simplifyFormula p._lFormula
    -- Apply rewriting transformations FIRST before time splitting
    -- This ensures De Bruijn indices remain correct when quantifiers are moved
    rewrittenFormula = applyRewriteTransformations simplifiedFormula
    needsRuleId = formulaHasSharedTimepoints rewrittenFormula
    hadTimepointSplit = needsRuleId
    formulaForProcessing =
      if needsRuleId
        then makeTimeVarsDistinct rewrittenFormula
        else rewrittenFormula
    fmsWithFlags = map transformFm fms'
    fms = map fst fmsWithFlags
    hadNegationFlags = map snd fmsWithFlags

    -- Apply all rewriting transformations that change formula structure
    -- This must happen BEFORE makeTimeVarsDistinct to avoid De Bruijn index corruption
    -- Uses FormulaShape classification to determine which transformation to apply
    -- Finally applies pnf to flatten nested quantifiers (e.g., Ex x. A & Ex y. B -> Ex x y. A & B)
    --
    -- Order of transformations:
    -- 1. Eliminate temporal equality constraints by unifying the equated
    --    timepoints (Ex #j. B@j & #i=#j → B@i), so the shared-timepoint
    --    splitting applies to them
    -- 2. Eliminate double negations
    -- 3. Convert negated existentials with time constraints to implications
    --    (not(Ex vars. A & not(#i=#j)) → All vars. A ==> #i=#j)
    -- 4. Move negated actions from premise to conclusion (enables pattern matching)
    -- 5. Classify formula shape
    -- 6. Apply shape-specific transformation
    -- 7. Flatten nested quantifiers
    applyRewriteTransformations fm =
      let fm0 = eliminateTemporalEqualities fm
          fm1 = eliminateDoubleNegations fm0
          -- Move negated actions/existentials from premise to conclusion FIRST
          -- This transforms: (not(Ex r. A@r) & B@i) ==> C into B@i ==> (C | (Ex r. A@r))
          -- This MUST run before convertNegExWithTimeConstraint so that not(Ex...) in premise
          -- gets moved to conclusion rather than being transformed in place
          fm1a = moveNegatedActionsToConclusion fm1
          -- Convert negated existentials with trailing time constraints to implications
          -- This transforms: not(Ex vars. A & not(#i=#j)) into All vars. A ==> #i=#j
          -- avoiding the need for a "leading negation" interpretation
          -- Now this only handles not(Ex...) at top level or in conclusion, not in premise
          fm1b = convertNegExWithTimeConstraint fm1a
          fm2 = fm1b
          shape = classifyFormulaShape p._lTraceQuantifier fm2
          transformed = applyRewriteForShape shape fm2
          -- Note: transformWithPullNots was removed as it can undo implication conversion
          -- Apply pnf to flatten nested quantifiers in the conclusion
          -- This handles cases like: All x. P => Ex y. A & Ex z. B -> All x. P => Ex y z. A & B
          -- And: Ex x. A & Ex y. B -> Ex x y. A & B
      in flattenNestedQuantifiers transformed

    -- Flatten nested quantifiers using pnf, but preserve the structure for implications
    -- For implications, only apply pnf to the conclusion if it has nested existentials
    -- that need flattening (e.g., Ex x. A & Ex y. B), NOT if it's already a disjunction
    flattenNestedQuantifiers :: LNFormula -> LNFormula
    flattenNestedQuantifiers (Qua All x body) =
      case flattenNestedQuantifiers body of
        Conn Imp prem concl
          | needsFlatteningInConclusion concl -> Qua All x (Conn Imp prem (pnf concl))
          | otherwise -> Qua All x (Conn Imp prem concl)
        body' -> Qua All x body'
    flattenNestedQuantifiers (Conn Imp prem concl)
      | needsFlatteningInConclusion concl = Conn Imp prem (pnf concl)
      | otherwise = Conn Imp prem concl
    flattenNestedQuantifiers fm@(Qua Ex _ _) = pnf fm
    -- Handle Not(Qua Ex ...) - flatten the inner existential and wrap with Not
    flattenNestedQuantifiers (Not fm@(Qua Ex _ _)) = Not (pnf fm)
    -- Handle Conn And - recursively flatten each part (needed after splitting)
    flattenNestedQuantifiers (Conn And left right) =
      Conn And (flattenNestedQuantifiers left) (flattenNestedQuantifiers right)
    flattenNestedQuantifiers fm = fm

    -- Check if conclusion needs flattening (has nested Ex inside conjunction)
    -- We DON'T want to flatten disjunctions of existentials - those are already in the right form
    needsFlatteningInConclusion :: LNFormula -> Bool
    needsFlatteningInConclusion (Qua Ex _ body) = needsFlatteningInConclusion body
    needsFlatteningInConclusion (Conn And left right) = hasNestedEx left || hasNestedEx right
    needsFlatteningInConclusion (Conn Or _ _) = False  -- Disjunctions don't need flattening
    needsFlatteningInConclusion _ = False

    -- Check if formula has a nested existential
    hasNestedEx :: LNFormula -> Bool
    hasNestedEx (Qua Ex _ _) = True
    hasNestedEx (Conn And left right) = hasNestedEx left || hasNestedEx right
    hasNestedEx _ = False

    -- Rule-id instrumented events get per-occurrence rule-id variables, and
    -- temporal equalities that survive rewriting are translated as rule-id
    -- equalities. Lemmas whose timepoints were split keep the shared "rid"
    -- scheme throughout, since the split copies are tied together by that
    -- shared variable.
    formula f' =
      let ridNames = if hadTimepointSplit then M.empty else ridOccurrenceNames ruleIdEvents f'
       in Precise.evalFresh (ppRestrictFormula ridNames ruleIdEvents te f' useInduction) (avoidPrecise f')

    -- Lemma name comment (always shown)
    lemmaNameComment = text "(*" <> text p._lName <> text "*)"

    -- For soem reason, "use_induction" attribute is named InvariantLemma.
    useInduction
      | InvariantLemma `elem` p._lAttributes = "[induction]"
      | otherwise = ""

    -- assuming all formulas we are concerned with have quantifiers at their top level (after splitTopLvlConns)
    -- Returns (transformed formula, hadLeadingNegation flag)
    -- Note: Main rewriting has already been done by applyRewriteTransformations
    transformFm fm =
      let -- Detect if formula has leading negation
          -- Check for simple Not (Ex ...) pattern as well as complex patterns
          hasLeadingNotEx = case fm of
            Not (Qua Ex _ _) -> True
            _ -> False
          -- Check for All x. ... ==> False pattern (equivalent to not(Ex x. ...))
          -- This appears as All x. All y. ... Not(...) after normalization
          hasAllImpliesFalse = case fm of
            Qua All _ body -> checkAllImpliesNot body
            _ -> False
            where
              checkAllImpliesNot (Qua All _ body) = checkAllImpliesNot body
              checkAllImpliesNot (Not _) = True
              checkAllImpliesNot (Conn Imp _ (TF False)) = True
              checkAllImpliesNot _ = False
          notExists = isNegatedExistsWithConjunction fm
          existsConj = isExistsWithNegatedExistentials fm
          hadLeadingNegation = hasLeadingNotEx || hasAllImpliesFalse || notExists || (existsConj && p._lTraceQuantifier == ExistsTrace)
          -- Apply final cleanup (constraint movement, negated action movement, simplification, and expand negated timepoint comparisons)
          -- moveNegatedActionsToConclusion transforms: (A & not(B)) ==> C into A ==> (C | B)
          -- After moving negated actions, apply shape-based transformation to handle patterns like A ==> (not(B) | C)
          movedToConclusion = moveNegatedActionsToConclusion $ moveConstraintsToConclusion fm
          -- Apply shape-based transformation to move negated disjuncts from conclusion to premise
          shape = classifyFormulaShape p._lTraceQuantifier movedToConclusion
          shapeTranformed = applyRewriteForShape shape movedToConclusion
          finalFormula = simplifyFormula $ expandNegatedTimepointComparisons shapeTranformed
          hasLeadingNegationAfterTransform = case finalFormula of
            Not _ -> True
            _ -> False
          -- Combine both checks: original detection OR negation introduced by transformation
          finalHadLeadingNegation = hadLeadingNegation || hasLeadingNegationAfterTransform
          result = (finalFormula, finalHadLeadingNegation)
      in finalHadLeadingNegation `seq` result  -- Force evaluation of finalHadLeadingNegation

    -- Split top-level connectives for the formula
    (fms', comments, _) = splitTopLvlConns p._lTraceQuantifier 1 formulaForProcessing

    -- Render a single subformula with appropriate comments
    renderSubformula :: (LNFormula, Bool) -> Doc
    renderSubformula (fm, hadNegation) =
      let timepointComment = if hadTimepointSplit
            then Just $ text "(* Timepoints in lemma have been split *)"
            else Nothing
          -- Get the formula to translate (inner formula for leading negation)
          -- For Not (Qua Ex ...), strip the Not and emit the inner existential as a reachability query
          -- ProVerif will check if it's reachable; if "true" (not reachable), the original property holds
          (fmToTranslate, isExistentialNegation) = case fm of
            Not fm'@(Qua Ex _ _) -> (fm', True)  -- Strip Not for any Not(Ex...) pattern
            Not fm' | isAllImpliesExists fm' && p._lTraceQuantifier == ExistsTrace -> (fm', True)
            _ -> (fm, False)
          -- Check for existentially quantified K facts (not supported in ProVerif)
          hasExistentialK = hasExistentiallyQuantifiedKFact fmToTranslate
          -- Check for too many quantifier alternations AFTER all rewrites
          alternations = countQuantifierAlternations fmToTranslate
          -- Check if the formula to translate contains negated actions that will produce not(event(...))
          -- This happens for exists-trace lemmas like "All x. A(x) ==> F" which become "Not (All x. A(x))"
          -- and can't be transformed into a valid ProVerif query (ProVerif can't find a trace without an action)
          hasNegatedActionInQuery = hasNegatedActionInFormula fmToTranslate
          (queryDoc, succeeded)
            | hasExistentialK =
                (text "(* Lemma contains existentially quantified K fact which is not supported *)"
                 $$ text "(*" <> prettyLNFormula fmToTranslate <> text "*)", False)
            | alternations > 1 =
                (text "(* Lemma has " <> text (show alternations) <> text " quantifier alternations (e.g., All-Ex-All). ProVerif only supports at most 1 alternation. *)"
                 $$ text "(*" <> prettyLNFormula fmToTranslate <> text "*)", False)
            | hasNegatedActionInQuery =
                (text "(* Lemma has negated event (from exists-trace lemma with negation). ProVerif cannot find a trace without an action. *)"
                 $$ text "(*" <> prettyLNFormula fm <> text "*)", False)
            | otherwise = formula fmToTranslate
          -- Determine negation warning (no lemma name, that's separate)
          negationWarning
            | isExistentialNegation && succeeded = Just $ text "(* Existential lemma has a leading negation, interpret ProVerif's answers accordingly! *)"
            | hadNegation && succeeded = Just $ text "(* Lemma has a leading negation, interpret ProVerif's answers accordingly! *)"
            | otherwise = Nothing
          -- Build output: lemma name, timepoint comment, negation warning, query
          parts = [lemmaNameComment]
                  ++ catMaybes [timepointComment, negationWarning]
                  ++ [queryDoc]
      in vcat parts

    -- Reconstruction comment for split lemmas
    reconstructionComment =
      if isEmpty comments
      then text ""
      else text "(* To reconstruct lemma " <> text p._lName <> text ":"
           $$ comments
           $$ text "*)" $$ text ""

-- ===========================================================================
-- SECTION 7b: Formula Shape Classification
-- ===========================================================================

-- | Classification of formula shapes for rewriting.
-- Formulas are classified by their top-level structure to determine
-- which rewrite strategy to apply. Each shape maps to exactly one
-- transformation strategy.
--
-- Listed in priority order (first match wins during classification).
data FormulaShape
    = ShapeAllActionsImpliesNotExists
      -- ^ ∀x. (A@i ⇒ ¬∃y. B@j)
      -- Action: Convert to PNF

    | ShapeNotExistsConj
      -- ^ ¬(∃x. P ∧ Q ∧ ¬R) with exactly one negation
      -- Action: Pull negations, convert ¬A∨B to A⇒B

    | ShapeExistsConjNotExists
      -- ^ ∃x. (P ∧ ¬∃y. Q)  [only for existential trace quantifier]
      -- Action: Rearrange conjuncts, convert A∧¬B to A⇒B

    | ShapeAllImpliesDisjWithNegations
      -- ^ ∀x. (P ⇒ ¬Q₁ ∨ ¬Q₂ ∨ R)
      -- Action: Move negated disjuncts to premise

    | ShapeAllImpliesConjWithNegations
      -- ^ ∀x. (P ⇒ ¬Q₁ ∧ ¬Q₂)
      -- Action: Distribute implication over conjunction to create
      -- (∀x. P ⇒ ¬Q₁) ∧ (∀x. P ⇒ ¬Q₂) which gets split by splitTopLvlConns

    | ShapeOther
      -- ^ No special structure detected
      -- Action: No structural rewrite needed (identity transform)
    deriving (Eq, Show)

-- | Classify a formula's shape for rewriting.
-- This examines the formula structure after double negation elimination
-- and determines which rewrite strategy should be applied.
classifyFormulaShape :: TraceQuantifier -> LNFormula -> FormulaShape
classifyFormulaShape traceQuant fm
    | isAllActionsImpliesNotExists fm = ShapeAllActionsImpliesNotExists
    | isNegatedExistsWithConjunction fm = ShapeNotExistsConj
    | isExistsWithNegatedExistentials fm && traceQuant == ExistsTrace = ShapeExistsConjNotExists
    | isAllImpliesConjWithNegations fm = ShapeAllImpliesConjWithNegations
    | isAllImpliesDisjWithNegations fm = ShapeAllImpliesDisjWithNegations
    | otherwise = ShapeOther

-- | Apply the rewrite strategy for a given formula shape.
-- Each shape has exactly one associated transformation.
applyRewriteForShape :: FormulaShape -> LNFormula -> LNFormula
applyRewriteForShape shape fm = case shape of
    ShapeAllActionsImpliesNotExists  -> convertPnfToNegatedExists $ pnf fm
    ShapeNotExistsConj               -> transformNotExistsConjToImplication fm
    ShapeExistsConjNotExists         -> transformExistsConjToNegatedImplication fm
    ShapeAllImpliesConjWithNegations -> distributeImplicationOverConjunction fm
    ShapeAllImpliesDisjWithNegations -> moveNegatedDisjunctsToPremise fm
    ShapeOther                       -> fm
  where
    -- Convert the result of pnf to negated existential form
    -- pnf(All x. A ==> not(Ex y. B)) = All x y. not(A) | not(B)
    -- We want: not(Ex x y. A & B) which renders as a conjunction with leading negation
    -- This is the standard form for reachability queries with negation
    convertPnfToNegatedExists :: LNFormula -> LNFormula
    convertPnfToNegatedExists formula =
        -- Collect all quantifiers and the body
        let (quants, body) = collectQuantifiers formula
            -- Extract the negated atoms from the disjunction
            atoms = collectNegatedAtoms body
            -- Build the conjunction and wrap with existentials, then negate
            conjunction = buildConjunction atoms
            existential = rewrapBoundPrefix Ex quants conjunction
        in Not existential

    collectQuantifiers :: LNFormula -> ([(String, LSort)], LNFormula)
    collectQuantifiers (Qua All (name, srt) body) =
        let (rest, innerBody) = collectQuantifiers body
        in ((name, srt) : rest, innerBody)
    collectQuantifiers (Qua Ex (name, srt) body) =
        let (rest, innerBody) = collectQuantifiers body
        in ((name, srt) : rest, innerBody)
    collectQuantifiers f = ([], f)

    collectNegatedAtoms :: LNFormula -> [LNFormula]
    collectNegatedAtoms (Conn Or p q) = collectNegatedAtoms p ++ collectNegatedAtoms q
    collectNegatedAtoms (Not p) = [p]
    collectNegatedAtoms _ = []

-- ===========================================================================
-- SECTION 8: Formula Transformations
-- ===========================================================================

-- | Apply pullNegationsToTop transformation with warning on partial rewrite
transformWithPullNots :: LNFormula -> LNFormula
transformWithPullNots f = case pullNegationsToTop f of
  Left f' -> translationWarning ("Formula " ++ render (prettyLNFormula f) ++ " cannot be rewritten s.t. it either has only 1 ¬ or none, the result is:\n" ++ render (prettyLNFormula f') ++ "!\n\n") f'
  Right f' -> f'

-- ===========================================================================
-- SECTION 9: Timepoint Variable Handling
-- ===========================================================================

-- | Eliminate temporal equality constraints by unifying the equated timepoint
-- variables (one-point rule). In Tamarin, @Ex #j. B()\@j & #i = #j@ is
-- equivalent to @B()\@i@; rewriting the explicit-equality form into the
-- shared-variable form lets the shared-timepoint splitting (rule-id
-- instrumentation) apply, instead of leaving behind an equality between two
-- distinct ProVerif timepoints, which is never satisfiable there (every
-- ProVerif event has a unique timepoint).
-- Dually for universals: @All #j. (A()\@j & #i = #j) ==> C@ becomes
-- @A()\@i ==> C@. Both rewrites are equivalences, so they are sound at any
-- polarity.
eliminateTemporalEqualities :: LNFormula -> LNFormula
eliminateTemporalEqualities fm0 =
  let fm' = go fm0
   in if fm' == fm0 then fm0 else simplifyFormula fm'
  where
    go (Qua q v@(_, LSortNode) body) =
      let body' = go body
       in case pinningEq q body' of
            Just repl -> substituteBinder repl body'
            Nothing -> Qua q v body'
    go (Qua q v body) = Qua q v (go body)
    go (Conn c p q) = Conn c (go p) (go q)
    go (Not p) = Not (go p)
    go fm = fm

    -- Find an equality that pins the binder being eliminated (Bound 0 at the
    -- binder level) to a variable bound outside of it, in a position where the
    -- equality is definite: a positive conjunct under an existential,
    -- respectively a positive premise conjunct of the implication under a
    -- universal. Returns the replacement variable, indexed relative to the
    -- position of the binder with the binder itself removed.
    pinningEq :: Quantifier -> LNFormula -> Maybe (BVar LVar)
    pinningEq Ex body = findPin 0 body
    pinningEq All body = descendAll 0 body
      where
        descendAll d (Qua All _ b) = descendAll (d + 1) b
        descendAll d (Conn Imp prem _) = findPin d prem
        descendAll _ _ = Nothing

    -- Search positive conjunct positions (through conjunctions and nested
    -- existentials) at depth d below the binder being eliminated.
    findPin :: Integer -> LNFormula -> Maybe (BVar LVar)
    findPin d (Conn And p q) = findPin d p `orElse` findPin d q
    findPin d (Qua Ex _ p) = findPin (d + 1) p
    findPin d (Ato (EqE s t)) = pin d s t `orElse` pin d t s
    findPin _ _ = Nothing

    pin d s t = case (viewTerm s, viewTerm t) of
      (Lit (Var (Bound i)), Lit (Var other))
        | i == d -> case other of
            Bound k | k > d -> Just (Bound (k - d - 1))
            Free v | lvarSort v == LSortNode -> Just (Free v)
            _ -> Nothing
      _ -> Nothing

    orElse m@(Just _) _ = m
    orElse Nothing n = n

    -- Substitute the eliminated binder by repl (indexed relative to the
    -- binder's position, with the binder itself already removed) and shift the
    -- indices of all enclosing binders down accordingly. The pinning equality
    -- itself becomes trivial (t = t) and is removed by the final
    -- simplifyFormula.
    substituteBinder :: BVar LVar -> LNFormula -> LNFormula
    substituteBinder repl = mapAtoms (\d a -> fmap (mapLits (fmap (adjust d))) a)
      where
        adjust d (Bound i)
          | i == d = case repl of
              Bound r -> Bound (r + d)
              Free v -> Free v
          | i > d = Bound (i - 1)
        adjust _ v = v

-- | Resolve a timepoint term to its variable name if it is a node-sorted
-- variable: bound (resolved through the given quantifier context) or free.
timeVarNameIn :: [(String, LSort)] -> VTerm Name (BVar LVar) -> Maybe String
timeVarNameIn ctx t = case viewTerm t of
  Lit (Var (Bound i)) -> case drop (fromIntegral i) ctx of
    (n, LSortNode) : _ -> Just n
    _ -> Nothing
  Lit (Var (Free v)) | lvarSort v == LSortNode -> Just (lvarName v)
  _ -> Nothing

-- | Collect (time variable name, fact tag name) pairs for all action atoms
-- that are translated to ProVerif events (i.e. excluding K/KU facts).
collectEventTimeVars :: LNFormula -> [(String, String)]
collectEventTimeVars = go []
  where
    go ctx (Ato (Action tv f@(Fact tag _ _)))
      | tag == KUFact || isKLogFact f = []
      | otherwise = maybe [] (\n -> [(n, factTagName tag)]) (timeVarNameIn ctx tv)
    go ctx (Not p) = go ctx p
    go ctx (Conn _ p q) = go ctx p ++ go ctx q
    go ctx (Qua _ v p) = go (v : ctx) p
    go _ _ = []

-- | Collect pairs of time-variable names linked by a temporal equality:
-- an equality atom #i = #j (possibly negated), or a negated strict
-- comparison not(#i < #j), which is expanded later into a disjunction
-- containing the equality.
collectTemporalEqPairs :: LNFormula -> [(String, String)]
collectTemporalEqPairs = go []
  where
    go ctx (Ato (EqE l r)) = pairOf ctx l r
    go ctx (Not (Ato (Less l r))) = pairOf ctx l r
    go ctx (Not p) = go ctx p
    go ctx (Conn _ p q) = go ctx p ++ go ctx q
    go ctx (Qua _ v p) = go (v : ctx) p
    go _ _ = []

    pairOf ctx l r = case (timeVarNameIn ctx l, timeVarNameIn ctx r) of
      (Just a, Just b) | a /= b -> [(a, b)]
      _ -> []

-- | Per-occurrence rule-id variable names for rule-id instrumented events in
-- formulas without split timepoints. The shared "rid" variable is only
-- meaningful for split-timepoint groups, whose copies it ties to the same
-- rule instance; reusing it across independent event occurrences would
-- silently constrain them to the same rule instance. Instead, each event
-- occurrence gets its own rule-id variable, named after its time variable.
--
-- This also gives temporal equalities that survive rewriting (e.g. in
-- disjunctions such as at-or-before: #j < #i | #j = #i) a translation: in
-- ProVerif, distinct events never share a timepoint, so a timepoint equality
-- would be unsatisfiable there. Since in Tamarin equal timepoints mean "same
-- rule instance", such an equality is translated as an equality between the
-- rule-id variables of the two events instead.
--
-- Only time variables used by exactly one instrumented event are mapped;
-- anything else falls back to the shared "rid" scheme.
ridOccurrenceNames :: S.Set String -> LNFormula -> M.Map String String
ridOccurrenceNames ruleIdEvents fm = M.fromSet ("rid_" ++) mapped
  where
    eventTVs = collectEventTimeVars fm
    tagsOf n = [tag | (n', tag) <- eventTVs, n' == n]
    mapped =
      S.fromList
        [ n
        | (n, _) <- eventTVs,
          case tagsOf n of
            [tag] -> tag `S.member` ruleIdEvents
            _ -> False
        ]

-- | Event tags linked by temporal equalities that survive rewriting; these
-- need rule-id instrumentation so the equality can be translated as a
-- rule-id equality (see 'ridEqualityNames').
temporalEqualityLinkedEvents :: LNFormula -> S.Set String
temporalEqualityLinkedEvents fm =
  S.fromList $
    concat
      [ tagsOf a ++ tagsOf b
      | (a, b) <- collectTemporalEqPairs fm,
        not (null (tagsOf a)),
        not (null (tagsOf b))
      ]
  where
    eventTVs = collectEventTimeVars fm
    tagsOf n = [tag | (n', tag) <- eventTVs, n' == n]

-- | Make time variables distinct for each action occurrence in a formula.
-- This ensures that events with shared timepoints in Tamarin get distinct time variables in ProVerif.
-- Transforms: ∃ x #i. A(x)@i & B(x)@i  into  ∃ x #i1 #i2. A(x)@i1 & B(x)@i2
makeTimeVarsDistinct :: LNFormula -> LNFormula
makeTimeVarsDistinct fm =
  let sharedTimeVars = findSharedTimeVars fm
  in if M.null sharedTimeVars
     then fm
     else splitTimeVars sharedTimeVars fm

-- | Find time variables (LSortNode quantifiers) that are used more than once
-- Returns: Map from (variable name, quantifier depth) to occurrence count
-- Note: quantifier depth is where the quantifier appears, not the Bound index from action perspective
findSharedTimeVars :: LNFormula -> M.Map (String, Integer) Int
findSharedTimeVars fm =
  M.filter (> 1) $ countTimeVarOccurrences [] 0 fm M.empty
  where
    -- ctx: list of (name, sort) for each quantifier (newest first)
    -- depth: current depth (number of enclosing quantifiers)
    countTimeVarOccurrences :: [(String, LSort)] -> Integer -> LNFormula -> M.Map (String, Integer) Int -> M.Map (String, Integer) Int
    countTimeVarOccurrences ctx depth (Ato (Action timeVar _fact)) acc =
      case viewTerm timeVar of
        Lit (Var (Bound idx)) | idx < depth ->
          -- Compute quantifier depth: if action is at depth D and uses Bound B,
          -- the quantifier is at depth (D - B - 1)
          let quantifierDepth = depth - idx - 1
          in case drop (fromIntegral idx) ctx of
               (name, LSortNode) : _ ->
                 M.insertWith (+) (name, quantifierDepth) 1 acc
               _ -> acc
        _ -> acc
    countTimeVarOccurrences ctx depth (Conn _ p q) acc =
      let acc' = countTimeVarOccurrences ctx depth p acc
      in countTimeVarOccurrences ctx depth q acc'
    countTimeVarOccurrences ctx depth (Not p) acc = countTimeVarOccurrences ctx depth p acc
    countTimeVarOccurrences ctx depth (Qua _q (name, varSort) p) acc =
      countTimeVarOccurrences ((name, varSort) : ctx) (depth + 1) p acc
    countTimeVarOccurrences _ _ _ acc = acc

-- | Split time variables that occur multiple times
-- For each quantifier matching a shared time var, replace with N copies
-- and adjust Bound indices in action atoms
splitTimeVars :: M.Map (String, Integer) Int -> LNFormula -> LNFormula
splitTimeVars sharedVars fm =
  fst $ splitAndReindexTimeVars [] 0 0 M.empty fm
  where
    -- ctx: list of (name, sort, original_depth) for tracking quantifiers
    -- depth: current depth (adjusted as we add quantifiers)
    -- originalDepth: the depth in the original formula (before any splits)
    -- seenCounts: tracks how many times we've seen each (originalName, originalDepth)
    splitAndReindexTimeVars :: [(String, LSort, Integer)] -> Integer -> Integer -> M.Map (String, Integer) Int -> LNFormula
       -> (LNFormula, M.Map (String, Integer) Int)

    splitAndReindexTimeVars ctx depth originalDepth seenCounts (Qua q (name, srt) p) =
      -- Check if this quantifier is a shared time variable
      -- Use originalDepth for lookup since sharedVars was computed from original formula
      let lookupKey = (name, originalDepth)
      in case M.lookup lookupKey sharedVars of
        Just count | srt == LSortNode ->
          -- This is a shared time variable - split it into multiple quantifiers
          let makeQuantifiers i body
                | i > count = body
                | otherwise =
                    let newName = name ++ show i
                    in Qua q (newName, srt) (makeQuantifiers (i + 1) body)
              -- Shift indices in p by (count - 1) because we're adding (count - 1) extra quantifiers
              p_shifted = shiftFreeIndices (fromIntegral (count - 1)) p
              -- Process the shifted body with updated context
              -- Add count entries to context (one for each new quantifier)
              -- IMPORTANT: Store the original name (before splitting), not the split name
              newCtxEntries = [(name, srt, originalDepth) | _ <- [1..count]]
              (p', seenCounts') = splitAndReindexTimeVars (newCtxEntries ++ ctx) (depth + fromIntegral count) (originalDepth + 1) seenCounts p_shifted
          in (makeQuantifiers 1 p', seenCounts')
        _ ->
          -- Normal quantifier - just process recursively
          let (p', seenCounts') = splitAndReindexTimeVars ((name, srt, originalDepth) : ctx) (depth + 1) (originalDepth + 1) seenCounts p
          in (Qua q (name, srt) p', seenCounts')

    splitAndReindexTimeVars ctx depth _originalDepth seenCounts (Ato (Action timeVar fact)) =
      case viewTerm timeVar of
        Lit (Var (Bound idx)) | idx < depth ->
          -- Check if this bound variable refers to a split time variable
          case drop (fromIntegral idx) ctx of
            (origName, LSortNode, origDepth) : _ ->
              let lookupKey = (origName, origDepth)
              in -- Check if the original quantifier was split
              case M.lookup lookupKey sharedVars of
                Just count | count > 1 ->
                  -- This action uses a split time variable
                  -- Determine which occurrence this is
                  let key = (origName, origDepth)
                      currentCount = M.findWithDefault 0 key seenCounts
                      newSeenCounts = M.insert key (currentCount + 1) seenCounts
                      -- Adjust the Bound index: subtract currentCount because j1 is furthest, j2 is closest
                      -- If original was Bound idx, first occurrence uses Bound idx, second uses Bound (idx-1), etc.
                      newIdx = idx - fromIntegral currentCount
                      newTimeVar = lit $ Var $ Bound newIdx
                  in (Ato (Action newTimeVar fact), newSeenCounts)
                _ -> (Ato (Action timeVar fact), seenCounts)
            _ -> (Ato (Action timeVar fact), seenCounts)
        _ -> (Ato (Action timeVar fact), seenCounts)

    splitAndReindexTimeVars ctx depth originalDepth seenCounts (Conn c p q) =
      let (p', seenCounts') = splitAndReindexTimeVars ctx depth originalDepth seenCounts p
          (q', seenCounts'') = splitAndReindexTimeVars ctx depth originalDepth seenCounts' q
      in (Conn c p' q', seenCounts'')

    splitAndReindexTimeVars ctx depth originalDepth seenCounts (Not p) =
      let (p', seenCounts') = splitAndReindexTimeVars ctx depth originalDepth seenCounts p
      in (Not p', seenCounts')

    splitAndReindexTimeVars _ _ _ seenCounts f = (f, seenCounts)

-- ===========================================================================
-- SECTION 10: Constraint Movement
-- ===========================================================================

-- | Move temporal and equality constraints from premise to conclusion for ProVerif compatibility.
-- ProVerif requires: "Disequalities and inequalities on time variables should not occur before the premise."
-- Transforms: (A && C) ==> B  into  A ==> (¬C || B)
-- For Less: (A && (i < j)) ==> B becomes A ==> ((i >= j) || B)
-- For disequality: (A && ¬(i = j)) ==> B becomes A ==> ((i = j) || B)
moveConstraintsToConclusion :: LNFormula -> LNFormula
moveConstraintsToConclusion fm = case fm of
  -- Handle quantifiers recursively
  Qua q x p -> Qua q x (moveConstraintsToConclusion p)

  -- Main transformation: (A && constraint) ==> B becomes A ==> (¬constraint || B)
  Conn Imp premise conclusion ->
    let (constraints, premise') = extractConstraints premise
    in if null constraints
       then Conn Imp (moveConstraintsToConclusion premise') (moveConstraintsToConclusion conclusion)
       else Conn Imp (moveConstraintsToConclusion premise') (addConstraintsToConclusion constraints (moveConstraintsToConclusion conclusion))

  -- Recursively process other connectives
  Conn c p q -> Conn c (moveConstraintsToConclusion p) (moveConstraintsToConclusion q)
  Not p -> Not (moveConstraintsToConclusion p)

  -- Base cases
  _ -> fm
  where
    -- Check if an atom is a constraint (Less or EqE on time variables)
    isConstraint :: LNFormula -> Bool
    isConstraint (Ato (Less _ _)) = True
    isConstraint (Ato (EqE _ _)) = True
    isConstraint (Not (Ato (EqE _ _))) = True
    isConstraint _ = False

    -- Extract constraints from a formula in the premise
    -- Returns: (list of constraints, formula without constraints)
    extractConstraints :: LNFormula -> ([LNFormula], LNFormula)
    extractConstraints (Conn And p q)
      | isConstraint q =
          let (cs, p') = extractConstraints p
          in (q : cs, p')
      | isConstraint p =
          let (cs, q') = extractConstraints q
          in (p : cs, q')
      | otherwise =
          let (cs1, p') = extractConstraints p
              (cs2, q') = extractConstraints q
          in (cs1 ++ cs2, if null cs1 && null cs2 then Conn And p q else if null cs1 then Conn And p q' else if null cs2 then Conn And p' q else Conn And p' q')
    extractConstraints (Qua Ex v p) =
      let (cs, p') = extractConstraints p
      in (cs, Qua Ex v p')
    extractConstraints f
      | isConstraint f = ([f], TF True)
      | otherwise = ([], f)

    -- Add negated constraints to conclusion with OR
    -- For (i < j): negate to (i >= j) which is (i > j) || (i = j)
    -- For ¬(i = j): negate to (i = j)
    addConstraintsToConclusion :: [LNFormula] -> LNFormula -> LNFormula
    addConstraintsToConclusion [] conclusion = conclusion
    addConstraintsToConclusion (c:cs) conclusion =
      let negatedC = negateConstraint c
          conclusion' = Conn Or negatedC conclusion
      in addConstraintsToConclusion cs conclusion'

    -- Negate a constraint for moving to conclusion
    negateConstraint :: LNFormula -> LNFormula
    negateConstraint (Ato (Less i j)) =
      -- ¬(i < j) is (i >= j) which is (i > j) || (i = j)
      -- In ProVerif this becomes: (i > j) || (i = j)
      -- We use Not Less to represent >=
      Conn Or (Ato (Less j i)) (Ato (EqE i j))
    negateConstraint (Not (Ato (EqE i j))) =
      -- ¬¬(i = j) is (i = j)
      Ato (EqE i j)
    negateConstraint (Ato (EqE i j)) =
      -- ¬(i = j) is (i ≠ j)
      Not (Ato (EqE i j))
    negateConstraint c = Not c

-- | Convert negated existentials with trailing time constraints to implications.
-- This transforms patterns like:
--   not(Ex #i #j vars. A@i & B@j & not(#i=#j))
-- into:
--   All #i #j vars. (A@i & B@j) ==> #i=#j
--
-- Similarly for Less constraints:
--   not(Ex #i #j #k vars. A & #i < #j & #j < #k)
-- into:
--   All #i #j #k vars. A ==> not(#i < #j) | not(#j < #k)
--   which simplifies to: All #i #j #k vars. A ==> (#j <= #i) | (#k <= #j)
--
-- This avoids the "leading negation" pattern and puts time constraints in the
-- conclusion where ProVerif can handle them properly.
convertNegExWithTimeConstraint :: LNFormula -> LNFormula
convertNegExWithTimeConstraint fm = case fm of
  -- Main pattern: not(Ex vars. body) where body has trailing time constraints
  Not fm'@(Qua Ex _ _) ->
    -- First, collect all the nested existential quantifiers and get the inner body
    let (vars, innerBody) = collectExistentialVars fm'
        -- Build a context from the collected vars (innermost first after reversing)
        -- vars are collected outermost first, so reverse for de Bruijn lookup
        ctx = reverse vars
     in case extractTrailingTimeConstraints ctx innerBody of
      Just (conjuncts, constraints) | not (null constraints) ->
        -- Build: All vars. conjuncts ==> disjunctionOfConstraints
        let premise = buildConjunction conjuncts
            -- For not(#i=#j), conclusion is #i=#j (remove negation)
            -- For #i < #j, conclusion is not(#i < #j) which we'll expand later
            conclusion = buildConclusionFromConstraints constraints
            -- Wrap with all the universal quantifiers (converted from existential)
         in rewrapBoundPrefix All vars (Conn Imp premise conclusion)
      _ -> Not (convertNegExWithTimeConstraint fm')

  -- Recurse through other structures
  Qua q x p -> Qua q x (convertNegExWithTimeConstraint p)
  Conn c p q -> Conn c (convertNegExWithTimeConstraint p) (convertNegExWithTimeConstraint q)
  Not p -> Not (convertNegExWithTimeConstraint p)
  _ -> fm
  where
    -- Collect all existential quantifier variables from nested Ex structure
    collectExistentialVars (Qua Ex x body) =
      let (vars, innerBody) = collectExistentialVars body
       in (x : vars, innerBody)
    collectExistentialVars body = ([], body)

    -- Extract trailing time constraints from a conjunction
    -- Returns (other conjuncts, time constraints) if time constraints are found
    -- ctx is the binder context (innermost first) for looking up bound variable sorts
    extractTrailingTimeConstraints :: [(String, LSort)] -> LNFormula -> Maybe ([LNFormula], [LNFormula])
    extractTrailingTimeConstraints ctx f =
      let conjuncts = flattenConjunction f
          (timeCs, others) = partition (isNegatedTimeConstraintOrLess ctx) conjuncts
       in if null timeCs then Nothing else Just (others, timeCs)

    -- Check if formula is a negated equality on time variables: not(#i = #j)
    -- Or a Less constraint: #i < #j
    -- IMPORTANT: Only match actual time variable comparisons, not term disequalities like not(b=ba)
    isNegatedTimeConstraintOrLess :: [(String, LSort)] -> LNFormula -> Bool
    isNegatedTimeConstraintOrLess ctx (Not (Ato (EqE t1 t2))) =
      -- Only match if both terms are time variables (LSortNode)
      isTimeVar ctx t1 && isTimeVar ctx t2
    isNegatedTimeConstraintOrLess _ (Ato (Less _ _)) = True  -- Less is always on time vars
    isNegatedTimeConstraintOrLess _ _ = False

    -- Check if a term is a time variable
    -- Free variables: check the sort is LSortNode
    -- Bound variables: look up the binder context to check the sort
    isTimeVar ctx t = case viewTerm t of
      Lit (Var (Free v)) -> lvarSort v == LSortNode
      Lit (Var (Bound idx)) ->
        -- Look up the sort in the context
        let i = fromIntegral idx
         in i < length ctx && snd (ctx !! i) == LSortNode
      _ -> False  -- Compound terms are not time variables

    -- Flatten a conjunction into a list
    flattenConjunction :: LNFormula -> [LNFormula]
    flattenConjunction (Conn And p q) = flattenConjunction p ++ flattenConjunction q
    flattenConjunction (Qua Ex x body) = [Qua Ex x body]  -- Don't recurse into existentials
    flattenConjunction f = [f]

    -- Build conclusion from extracted constraints
    -- For not(#i=#j), the conclusion is #i=#j (negation removed)
    -- For #i < #j, the conclusion is (#j < #i) | (#i = #j) (i.e., #i >= #j)
    buildConclusionFromConstraints :: [LNFormula] -> LNFormula
    buildConclusionFromConstraints [] = TF True
    buildConclusionFromConstraints [c] = negateTimeConstraint c
    buildConclusionFromConstraints (c:cs) =
      Conn Or (negateTimeConstraint c) (buildConclusionFromConstraints cs)

    -- Negate a time constraint for moving to conclusion
    negateTimeConstraint :: LNFormula -> LNFormula
    negateTimeConstraint (Not (Ato (EqE i j))) = Ato (EqE i j)  -- not(not(#i=#j)) = #i=#j
    negateTimeConstraint (Ato (Less i j)) =
      -- not(#i < #j) = #i >= #j = (#j < #i) | (#i = #j)
      Conn Or (Ato (Less j i)) (Ato (EqE i j))
    negateTimeConstraint f = Not f  -- fallback

-- | Move negated actions from premise to conclusion.
-- ProVerif doesn't allow negated events in queries at all.
-- Transforms: (A & not(B@t)) ==> C  into  A ==> (C | B@t)
-- This is valid because: A & not(B) ==> C  ≡  A ==> C | B
moveNegatedActionsToConclusion :: LNFormula -> LNFormula
moveNegatedActionsToConclusion fm = case fm of
  -- Handle quantifiers recursively
  Qua q x p -> Qua q x (moveNegatedActionsToConclusion p)

  -- Main transformation: (A && not(action)) ==> B becomes A ==> (B || action)
  Conn Imp premise conclusion ->
    let (negatedActions, premise') = extractNegatedActions premise
    in if null negatedActions
       then Conn Imp (moveNegatedActionsToConclusion premise') (moveNegatedActionsToConclusion conclusion)
       else Conn Imp (moveNegatedActionsToConclusion premise') (addActionsToConclusion negatedActions (moveNegatedActionsToConclusion conclusion))

  -- Recursively process other connectives
  Conn c p q -> Conn c (moveNegatedActionsToConclusion p) (moveNegatedActionsToConclusion q)
  Not p -> Not (moveNegatedActionsToConclusion p)

  -- Base cases
  _ -> fm
  where
    -- Check if a formula is a negated action, negated existential, or disjunction of negations
    -- Patterns:
    --   Not (Ato (Action ...))           -- negated bare action (usually invalid in Tamarin)
    --   Not (Qua Ex _ body)              -- negated existential, where body contains action
    --   Conn Or (Not a) (Not b)          -- disjunction of negations = not(a & b) by De Morgan
    isNegatedAction :: LNFormula -> Bool
    isNegatedAction (Not (Ato (Action _ _))) = True
    isNegatedAction (Not (Qua Ex _ _)) = True  -- negated existential
    isNegatedAction (Conn Or (Not _) (Not _)) = True  -- disjunction of negations
    isNegatedAction _ = False

    -- Extract the inner formula from a negated action pattern
    -- For Not (Ato action) -> Ato action
    -- For Not (Ex x. body) -> Ex x. body  (preserving the existential)
    -- For Conn Or (Not a) (Not b) -> Conn And a b  (De Morgan)
    extractInnerFormula :: LNFormula -> LNFormula
    extractInnerFormula (Not inner) = inner
    extractInnerFormula (Conn Or (Not a) (Not b)) = Conn And a b  -- De Morgan: not(a) | not(b) = not(a & b)
    extractInnerFormula f = f

    -- Extract negated actions from a formula in the premise
    -- Returns: (list of unnegated formulas to move to conclusion, formula without negated actions)
    extractNegatedActions :: LNFormula -> ([LNFormula], LNFormula)
    extractNegatedActions (Conn And p q) =
      -- Extract from both children
      let (actsP, p') = extractNegatedActions p
          (actsQ, q') = extractNegatedActions q
          allActs = actsP ++ actsQ
      in if null allActs
         then ([], Conn And p q)
         else
           -- At least one negated action found
           -- Build remaining formula from the non-negated parts
           case (isNegatedAction p, isNegatedAction q, actsP, actsQ) of
             -- Both p and q are directly negated actions
             (True, True, _, _) ->
               (allActs, TF True)  -- Nothing left in premise except true
             -- Only p is a direct negated action
             (True, False, _, _) ->
               (allActs, q')
             -- Only q is a direct negated action
             (False, True, _, _) ->
               (allActs, p')
             -- Neither is directly negated, but they may have nested negated actions
             (False, False, _, _) ->
               (allActs, Conn And p' q')
    extractNegatedActions f
      | isNegatedAction f = ([extractInnerFormula f], TF True)
      | otherwise = ([], f)

    -- Add unnegated actions to conclusion as disjuncts
    addActionsToConclusion :: [LNFormula] -> LNFormula -> LNFormula
    addActionsToConclusion [] conclusion = conclusion
    addActionsToConclusion (action:rest) conclusion =
      addActionsToConclusion rest (Conn Or conclusion action)

-- | Transform not(Ex x1...xn. P1 & P2 & ... & (Ex y. Q) & ... & not(Ex z. R) & ...)
-- into: All x1...xn y ... . (P1 & P2 & ... & Q & ...) ==> (Ex z. R | ...)
--
-- This transformation uses the standard approach: apply nnf to push negation inside,
-- then use pnf to pull all quantifiers to the front (with proper De Bruijn shifting).
--
-- Input: not(Ex x. P(x) & (Ex y. Q(y)) & not(Ex z. R(z)))
-- After nnf: All x. not(P(x)) | (All y. not(Q(y))) | (Ex z. R(z))
--          = All x. not(P(x) & (Ex y. Q(y))) | (Ex z. R(z))
-- After pnf: All x y. (not(P(x)) | not(Q(y))) | (Ex z. R(z))
--          = All x y. not(P(x) & Q(y)) | (Ex z. R(z))
--          = All x y. (P(x) & Q(y)) => (Ex z. R(z))
--
-- The key insight is that we only want to pull UNIVERSAL quantifiers from the disjunction,
-- not existentials. The existentials should stay where they are as separate disjuncts.
-- This is because (Ex r. A) | (Ex r. B) is semantically "there exists r for A OR there exists r for B"
-- while Ex r. (A | B) means "there exists ONE r that makes A OR B true" - different semantics!
transformNotExistsConjToImplication :: LNFormula -> LNFormula
transformNotExistsConjToImplication fm =
    -- Apply NNF (negation normal form) to push negation inside
    -- This converts not(Ex...) to All... and flips inner negations correctly
    let nnfFormula = nnf fm
        -- Apply custom prenex that only pulls UNIVERSAL quantifiers, not existentials
        -- This keeps existentials as separate disjuncts in the conclusion
        prenexFormula = prenexUniversalsOnly nnfFormula
        -- Convert the resulting disjunction to implication form
        -- All x y. (not(P) | not(Q) | R) becomes All x y. (P & Q) => R
    in convertDisjunctionToImplication prenexFormula
  where
    -- Custom prenex that only pulls universal quantifiers, leaving existentials in place
    prenexUniversalsOnly :: LNFormula -> LNFormula
    prenexUniversalsOnly (Qua All x body) = Qua All x (prenexUniversalsOnly body)
    prenexUniversalsOnly (Qua Ex x body) = Qua Ex x (prenexUniversalsOnly body)
    prenexUniversalsOnly (Conn And p q) = pullUniversalsOnly $ prenexUniversalsOnly p .&&. prenexUniversalsOnly q
    prenexUniversalsOnly (Conn Or p q) = pullUniversalsOnly $ prenexUniversalsOnly p .||. prenexUniversalsOnly q
    prenexUniversalsOnly f = f

    -- Pull only universal quantifiers from connectives, not existentials
    pullUniversalsOnly :: LNFormula -> LNFormula
    pullUniversalsOnly (Conn And (Qua All x p) (Qua All x' q)) | x == x' = Qua All x (pullUniversalsOnly (p .&&. q))
    pullUniversalsOnly (Conn And (Qua All x p) q) = Qua All x (pullUniversalsOnly (p .&&. shiftFreeIndices 1 q))
    pullUniversalsOnly (Conn And p (Qua All x q)) = Qua All x (pullUniversalsOnly (shiftFreeIndices 1 p .&&. q))
    pullUniversalsOnly (Conn Or (Qua All x p) (Qua All x' q)) | x == x' = Qua All x (pullUniversalsOnly (p .||. q))
    pullUniversalsOnly (Conn Or (Qua All x p) q) = Qua All x (pullUniversalsOnly (p .||. shiftFreeIndices 1 q))
    pullUniversalsOnly (Conn Or p (Qua All x q)) = Qua All x (pullUniversalsOnly (shiftFreeIndices 1 p .||. q))
    -- Don't pull existentials - leave them in place!
    pullUniversalsOnly f = f

    -- Convert All x. (not(P) | Q) to All x. (P => Q)
    -- More generally: All x. (not(P1) | not(P2) | ... | Q1 | Q2 | ...)
    --              => All x. (P1 & P2 & ...) => (Q1 | Q2 | ...)
    convertDisjunctionToImplication :: LNFormula -> LNFormula
    convertDisjunctionToImplication (Qua All x body) =
        Qua All x (convertDisjunctionToImplication body)
    convertDisjunctionToImplication (Qua Ex x body) =
        -- Existential in conclusion - keep it
        Qua Ex x (convertDisjunctionToImplication body)
    convertDisjunctionToImplication disjunction =
        let (negated, positive) = partitionDisjuncts disjunction
            -- negated contains formulas that were Not(...), we take the inner part for premise
            premise = buildConjunction negated
            -- positive contains existentials and atoms for conclusion
            conclusion = buildDisjunction positive
        in if null negated
           then conclusion
           else Conn Imp premise conclusion

    -- Partition disjuncts into negated (premise) and positive (conclusion)
    partitionDisjuncts :: LNFormula -> ([LNFormula], [LNFormula])
    partitionDisjuncts (Conn Or p q) =
        let (neg1, pos1) = partitionDisjuncts p
            (neg2, pos2) = partitionDisjuncts q
        in (neg1 ++ neg2, pos1 ++ pos2)
    partitionDisjuncts (Not p) = ([p], [])  -- Negated term goes to premise
    partitionDisjuncts p = ([], [p])        -- Positive term goes to conclusion

-- | Transform Ex x. (P & not(Ex y. Q) & not(Ex z. R)) to Not(All x. P => (Ex y. Q | Ex z. R))
-- This is the dual of transformNotExistsConjToImplication.
-- The pattern Ex x. (A & not(B)) is equivalent to not(All x. A => B).
-- We reuse the not(Ex...) transformation by wrapping with Not and then transforming.
transformExistsConjToNegatedImplication :: LNFormula -> LNFormula
transformExistsConjToNegatedImplication fm =
    -- Wrap the existential formula with Not to get not(Ex x. P & not(Q))
    -- Then apply the not(Ex...) transformation which gives All x. not(P) | Q
    -- Finally the outer Not gives us not(All x. P => Q)
    let notFm = Not fm
        transformed = transformNotExistsConjToImplication notFm
    in Not transformed

-- | Flatten nested implications for axiom translation.
-- In ProVerif, axioms and restrictions don't support nested correspondences like A => (B => C).
-- This function flattens them: A => (B => C) becomes (A & B) => C
-- This is logically equivalent: A => (B => C) = ¬A ∨ (¬B ∨ C) = ¬(A ∧ B) ∨ C = (A ∧ B) => C
--
-- IMPORTANT: This transformation is ONLY valid for direct nested implications.
-- The pattern A => ((D => E) & F) CANNOT be transformed to (A & D) => (E & F)
-- because this is NOT logically equivalent. Use hasNestedImplicationInConjunction
-- to detect such unsupported patterns before calling this function.
--
-- Also, A => (All x. B => C) can only be flattened to All x. (A & B) => C if x is NOT
-- free in A. Use hasVariableCaptureInNestedImplication to detect this case.
flattenNestedImplications :: LNFormula -> LNFormula
flattenNestedImplications = go
  where
    go (Qua q x p) = Qua q x (go p)
    go (Conn Imp p (Conn Imp q r)) =
      -- A => (B => C) becomes (A & B) => C, then recurse on C
      go (Conn Imp (Conn And p q) r)
    go (Conn Imp p (Qua All x q)) =
      -- A => (All x. Q) - need to look inside the All
      -- If Q is an implication, we can potentially flatten it
      -- SOUNDNESS CHECK: x must not be free in p, otherwise variable capture occurs
      -- x is (String, LSort), frees returns [LVar], so check by name and sort
      let freeInP = frees p
          (xName, xSort) = x
          xFreeInP = any (\v -> lvarName v == xName && lvarSort v == xSort) freeInP
      in if xFreeInP
         then Conn Imp (go p) (Qua All x (go q))  -- Cannot flatten safely, just recurse
         else case go (Qua All x q) of
           Qua All x' (Conn Imp q' r') ->
             -- A => (All x. B => C) becomes All x. (A & B) => C
             -- Safe because x is not free in A
             Qua All x' (Conn Imp (Conn And (shiftFreeIndices 1 p) q') r')
           other -> Conn Imp (go p) other
    go (Conn Imp p (Conn And q r)) =
      -- A => (B & C) - we can only recurse, NOT flatten implications inside B or C
      -- The transformation A => ((D => E) & F) -> (A & D) => (E & F) is UNSOUND
      -- Just recurse on each part
      Conn Imp (go p) (Conn And (go q) (go r))
    go (Conn c p q) = Conn c (go p) (go q)
    go (Not p) = Not (go p)
    go f = f

-- | Check if a formula has nested implications inside conjunctions in the conclusion.
-- Such formulas cannot be soundly flattened and are outside ProVerif's supported fragment.
-- Pattern: A => ((B => C) & D) or A => (D & (B => C))
hasNestedImplicationInConjunction :: LNFormula -> Bool
hasNestedImplicationInConjunction = go
  where
    go (Qua _ _ p) = go p
    go (Conn Imp _ conclusion) = hasImpInConj conclusion
    go (Conn _ p q) = go p || go q
    go (Not p) = go p
    go _ = False

    -- Check if there's an implication inside a conjunction
    hasImpInConj (Conn And p q) = hasImp p || hasImp q || hasImpInConj p || hasImpInConj q
    hasImpInConj (Qua _ _ body) = hasImpInConj body
    hasImpInConj _ = False

    -- Check if the formula is or contains an implication at the top level
    hasImp (Conn Imp _ _) = True
    hasImp (Qua _ _ body) = hasImp body
    hasImp _ = False

-- | Check if a formula has variable capture issues in nested quantified implications.
-- Pattern: A => (All x. B => C) where x is free in A cannot be flattened safely.
hasVariableCaptureInNestedImplication :: LNFormula -> Bool
hasVariableCaptureInNestedImplication = go
  where
    go (Qua _ _ p) = go p
    go (Conn Imp p (Qua All x q)) =
      let freeInP = frees p
          (xName, xSort) = x
          xFreeInP = any (\v -> lvarName v == xName && lvarSort v == xSort) freeInP
      in (xFreeInP && hasNestedImp q) || go p || go q
    go (Conn _ p q) = go p || go q
    go (Not p) = go p
    go _ = False

    hasNestedImp (Conn Imp _ _) = True
    hasNestedImp (Qua _ _ body) = hasNestedImp body
    hasNestedImp _ = False

-- | Check if a formula contains not(...event...) anywhere.
-- This pattern is not supported in ProVerif axioms/restrictions.
hasNegatedEventInFormula :: LNFormula -> Bool
hasNegatedEventInFormula = go
  where
    go (Qua _ _ p) = go p
    go (Not p) = hasEventAnywhere p || go p
    go (Conn _ p q) = go p || go q
    go _ = False

    hasEventAnywhere (Ato (Action _ _)) = True
    hasEventAnywhere (Not f) = hasEventAnywhere f
    hasEventAnywhere (Conn _ f1 f2) = hasEventAnywhere f1 || hasEventAnywhere f2
    hasEventAnywhere (Qua _ _ f) = hasEventAnywhere f
    hasEventAnywhere _ = False

-- | Check if a negated restriction can potentially be rewritten to positive form.
-- Pattern: not(Ex... (P & Q) & (i ≠ j)) can become All... (P & Q) => (i = j)
-- Returns a description of the pattern if found, Nothing otherwise.
canRewriteNegatedRestriction :: LNFormula -> Maybe String
canRewriteNegatedRestriction (Not fm@(Qua Ex _ _)) =
  -- Check if the body has a conjunction ending with an inequality
  let body = getExistentialBody fm
  in if hasInequalityInConj body
     then Just "Pattern: not(Ex... P & (i ≠ j)) can be rewritten as All... P => (i = j)"
     else Nothing
  where
    getExistentialBody (Qua Ex _ b) = getExistentialBody b
    getExistentialBody b = b

    hasInequalityInConj (Conn And _ (Not (Ato (EqE _ _)))) = True
    hasInequalityInConj (Conn And (Not (Ato (EqE _ _))) _) = True
    hasInequalityInConj (Conn And p q) = hasInequalityInConj p || hasInequalityInConj q
    hasInequalityInConj _ = False
canRewriteNegatedRestriction _ = Nothing

-- | Check if a formula has a simple negated action pattern that cannot be translated.
-- Pattern: not(Ex x. Action(x)@i) - this cannot be rewritten to a positive form
isSimpleNegatedAction :: LNFormula -> Bool
isSimpleNegatedAction (Not fm@(Qua Ex _ _)) =
  let body = getExistentialBody fm
  in isJustAction body
  where
    getExistentialBody (Qua Ex _ b) = getExistentialBody b
    getExistentialBody b = b

    isJustAction (Ato (Action _ _)) = True
    isJustAction _ = False
isSimpleNegatedAction _ = False

data TimeVarKey
  = FreeTimeVar LVar
  | BoundTimeVar Int
  deriving (Show, Eq, Ord)

data BinderInfo = BinderInfo
  { _binderId :: Int,
    _binderSort :: LSort
  }

collectActionsWithTimepoints :: LNFormula -> M.Map TimeVarKey [String]
collectActionsWithTimepoints fm = snd (collectActions [] 0 fm M.empty)
  where
    collectActions ctx nextId (Ato (Action timeVar (Fact tag _ _))) acc =
      let (nextId', maybeKey) = extractKey ctx nextId timeVar
          updatedAcc = case maybeKey of
            Just key -> M.insertWith (++) key [factTagName tag] acc
            Nothing -> acc
       in (nextId', updatedAcc)
    collectActions _ctx nextId (Ato _) acc = (nextId, acc)
    collectActions _ctx nextId (TF _) acc = (nextId, acc)
    collectActions ctx nextId (Not p) acc = collectActions ctx nextId p acc
    collectActions ctx nextId (Conn _ p q) acc =
      let (nextAfterP, acc') = collectActions ctx nextId p acc
       in collectActions ctx nextAfterP q acc'
    collectActions ctx nextId (Qua _ (_, varSort) body) acc =
      let binder = BinderInfo nextId varSort
       in collectActions (binder : ctx) (nextId + 1) body acc

    extractKey ctx nextId timeVar =
      case viewTerm timeVar of
        Lit (Var (Free v)) ->
          if lvarSort v == LSortNode
            then (nextId, Just (FreeTimeVar v))
            else (nextId, Nothing)
        Lit (Var (Bound i)) ->
          case drop (fromIntegral i) ctx of
            BinderInfo bid bSort : _ ->
              if bSort == LSortNode
                then (nextId, Just (BoundTimeVar bid))
                else (nextId, Nothing)
            [] -> (nextId, Nothing)
        _ -> (nextId, Nothing)

-- | Find events that share timepoints in a formula
eventsSharingTimepoints :: LNFormula -> S.Set String
eventsSharingTimepoints fm =
  let actionMap = collectActionsWithTimepoints fm
      sharedTimepoints = M.filter ((> 1) . length) actionMap
   in S.fromList . concatMap (S.toList . S.fromList) $ M.elems sharedTimepoints

-- | Check if a formula has any shared timepoints
formulaHasSharedTimepoints :: LNFormula -> Bool
formulaHasSharedTimepoints = not . S.null . eventsSharingTimepoints

formulaUsesRuleIdEvents :: S.Set String -> ProtoFormula syn (a, LSort) c LVar -> Bool
formulaUsesRuleIdEvents ruleIdEvents =
  foldFormula
    ( \atom -> case atom of
        Action _ (Fact tag _ _) -> factTagName tag `S.member` ruleIdEvents
        _ -> False
    )
    (const False)
    id
    (\_ p q -> p || q)
    (\_ _ p -> p)

-- | Detect which event fact tags appear with shared timepoints in lemmas.
-- Returns a set of fact tag names that need rule IDs.
detectSharedTimepointEvents :: [ProtoLemma LNFormula ProofSkeleton] -> S.Set String
detectSharedTimepointEvents lemmas =
  S.unions $ map (analyze . L.get lFormula) lemmas
  where
    -- Definite temporal equalities are eliminated by unifying the equated
    -- timepoints, turning them into shared timepoints; equalities that
    -- survive (e.g. in disjunctions) are translated as rule-id equalities,
    -- so their events need rule-id instrumentation as well.
    analyze fm =
      let fm' = eliminateTemporalEqualities fm
       in eventsSharingTimepoints fm' `S.union` temporalEqualityLinkedEvents fm'

loadLemmas ::
  S.Set String ->  -- sharedEventTags: events that need rule IDs
  Bool ->  -- hasSpecificLemmas: whether --lemma flag was used
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  TranslationContext ->
  TypingEnvironment ->
  OpenTheory ->
  ([Doc], [Doc], S.Set ProVerifHeader)  -- (axioms, queries, headers)
loadLemmas sharedEventTags hasSpecificLemmas lemSel tc te thy = (axiomDocs, queryDocs, headers)
  where
    thyLemmas = theoryLemmas thy

    -- Classify all lemmas
    classified = [(lem, classifyLemma hasSpecificLemmas tc lemSel lem) | lem <- thyLemmas]

    -- Separate into axioms and queries
    axiomsLemmas = [lem | (lem, AsAxiom) <- classified]
    queryLemmas = [lem | (lem, AsQuery) <- classified]

    -- Include both axioms and queries for fact extraction
    allIncludedLemmas = axiomsLemmas ++ queryLemmas

    -- Translate axioms using ppAxiomLemma
    axiomDocs = map (ppAxiomLemma sharedEventTags te) axiomsLemmas

    -- Translate queries using existing ppLemma
    queryDocs = map (ppLemma sharedEventTags te) queryLemmas

    allFacts = concatMap (formulaFacts . L.get lFormula) allIncludedLemmas
    headers = makeEventHeaders sharedEventTags allFacts

-- | Classify how a lemma should be translated based on selector and attributes
classifyLemma ::
  Bool ->  -- ^ hasSpecificLemmas: whether --lemma flag was used
  TranslationContext
  -> (Lemma ProofSkeleton -> Bool)  -- ^ lemSel selector
  -> Lemma ProofSkeleton
  -> LemmaTranslationMode
classifyLemma hasSpecificLemmas tc lemSel lem
  -- If lemma doesn't pass module condition, exclude it
  | not (moduleCondition lem) = ExcludeLemma

  -- If specific lemmas were targeted AND this lemma is selected
  | hasSpecificLemmas && lemSel lem =
      -- Direct targeting: always treat as query (strip reuse/source behavior)
      AsQuery

  -- If specific lemmas targeted, this one is NOT selected, BUT it's reuse/source
  | hasSpecificLemmas && not (lemSel lem) && isReuseOrSource lem =
      if shouldSkipHelperLemma lem
        then ExcludeLemma
        else AsAxiom

  -- If specific lemmas targeted, this one is NOT selected, and NOT reuse/source
  | hasSpecificLemmas && not (lemSel lem) = ExcludeLemma

  -- If NO specific lemmas targeted (default: all lemmas), and is reuse/source
  | not hasSpecificLemmas && isReuseOrSource lem =
      if shouldSkipHelperLemma lem
        then ExcludeLemma
        else AsAxiom

  -- If NO specific lemmas targeted and lemma is NOT reuse/source
  | not hasSpecificLemmas && not (isReuseOrSource lem) = AsQuery

  -- Default fallback
  | otherwise = AsQuery
  where
    shouldSkipHelperLemma l =
      (skipReuseLemmas tc && ReuseLemma `elem` l._lAttributes)
        || (skipSourceLemmas tc && SourceLemma `elem` l._lAttributes)

    isReuseOrSource l =
      ReuseLemma `elem` l._lAttributes || SourceLemma `elem` l._lAttributes

    moduleCondition l =
      let modules = concat [ls | LemmaModule ls <- l._lAttributes]
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
loadHeaders :: S.Set String -> TranslationContext -> OpenTheory -> TypingEnvironment -> IO (S.Set ProVerifHeader)
loadHeaders ruleIdEvents tc thy typeEnv = do
  eqHeaders <- foldMap (headersOfRule tc typeEnv) sigRules
  pure $
    typedHeaderOfFunSym
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
        funNames = S.fromList [n | Fun _ n _ _ _ <- S.toList typedHeaderOfFunSym]
        keep (Fun _ n _ _ _) = n `S.notMember` funNames
        -- Models define g/0 themselves even when using the diffi-hellman builtin.
        -- FIXME: Given builtins higher precedence than user defined functions seems more intuitive.
        keep (Sym _ n _ _) = n `S.notMember` funNames
        keep _ = True

    -- all user declared function symbols have typinginfos
    userDeclaredFunctions = theoryFunctionTypingInfos thy
    typedHeaderOfFunSym = foldMap headerOfFunSym userDeclaredFunctions

    -- events headers
    eventHeaders =
      M.foldrWithKey
        ( \tag types acc ->
            let factName = factTagName tag
                adjustedTypes =
                  if factName `S.member` ruleIdEvents
                    then Nothing : types
                    else types
            in HEvent ('e' : factName) ("(" ++ makeArgtypes adjustedTypes ++ ")") `S.insert` acc
        )
        S.empty
        typeEnv.events
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
pullNegationsToTop :: LNFormula -> Either LNFormula LNFormula
pullNegationsToTop fm =
  let fm_partially_rewritten = fixedpoint applyPullNegationStep fm -- nots pulled out by applyPullNegationStep can enable new pull-out steps, so need to compute fixed point
   in if onlyTopLevelNot fm_partially_rewritten
        then Right fm_partially_rewritten -- in this case, formula is fully rewritten, i.e. has only 1 top-level not or no nots at all
        else Left fm_partially_rewritten -- Error with partially rewritten formula
  where
    fixedpoint f phi = if phi /= f phi then fixedpoint f (f phi) else phi

    applyPullNegationStep fm' = case fm' of
      Conn And (Not p) (Not q) -> Not $ p .||. q
      Conn Or (Not p) (Not q) -> Not $ p .&&. q
      Conn Imp p (Not q) ->
        case q of
          Not q' -> Conn Imp (applyPullNegationStep p) (applyPullNegationStep q')  -- q is ¬¬..., simplify to q' by removing double negation
          _ -> if isLessOrEqe q then Conn Imp (applyPullNegationStep p) (Not (applyPullNegationStep q)) else Not $ applyPullNegationStep p .&&. applyPullNegationStep q
      Conn Iff (Not p) q -> Not $ p .<=>. q
      Conn Iff p (Not q) -> Not $ p .<=>. q
      Conn c p q -> Conn c (applyPullNegationStep p) (applyPullNegationStep q)
      Qua All x (Not p) -> Not $ Qua Ex x p
      Qua Ex x (Not p) -> Not $ Qua All x p
      Qua qua x p -> Qua qua x $ applyPullNegationStep p
      Not (Not p) -> p
      Not (Ato (EqE t1 t2)) -> Not (Ato (EqE t1 t2))
      Not p -> Not $ applyPullNegationStep p
      _ -> fm'

    -- Don't pull nots infront of equality tests/comparisons.
    isLessOrEqe (Ato (EqE _ _)) = True
    isLessOrEqe (Ato (Less _ _)) = True
    isLessOrEqe _ = False

onlyTopLevelNot :: ProtoFormula syn s c v -> Bool
onlyTopLevelNot (Not p) = hasNoNegations p -- top-level not expected if rewriting was successful
onlyTopLevelNot p = hasNoNegations p -- no top-level not may mean the rewriting has been successful and the formula has no nots at all

hasNoNegations :: ProtoFormula syn s c v -> Bool
hasNoNegations (Not (Ato (EqE _ _))) = True -- check that there are no nots below top level (except before equality tests/comparisons)
hasNoNegations (Not (Ato (Less _ _))) = True
hasNoNegations (Not _) = False
hasNoNegations (Conn _ p q) = hasNoNegations p && hasNoNegations q
hasNoNegations (Qua _ _ p) = hasNoNegations p
hasNoNegations _ = True

-- | Check if a formula is of the form All x1 ... xn. (F => (Ex y1 ... yn. F') or All x1 ... xn. (F => (Ex y1 ... yn. F') \/ (Ex y1' ... yn'. F'').
isAllImpliesExists :: LNFormula -> Bool
isAllImpliesExists (Qua All _ body) = isAllImpliesExists body
isAllImpliesExists f@(Conn Imp p q) = isQuantifierFree f || (isQuantifierFree p && hasOnlyExistentials q)
  where
    hasOnlyExistentials (Qua Ex _ body') = isQuantifierFree body' || hasOnlyExistentials body'
    hasOnlyExistentials (Conn Or (Qua Ex _ b1) (Qua Ex _ b2)) = isQuantifierFree b1 || isQuantifierFree b2
    -- Allow temporal/equality constraints in disjunction with existentials
    hasOnlyExistentials (Conn Or f1 f2) | isConstr f1 || isConstr f2 = hasOnlyExistentials f1 || hasOnlyExistentials f2 || isConstr f1 || isConstr f2
    hasOnlyExistentials fm | isConstr fm = True
    hasOnlyExistentials _ = False
    -- Check if a formula is a temporal or equality constraint
    isConstr (Ato (Less _ _)) = True
    isConstr (Ato (EqE _ _)) = True
    isConstr (Not (Ato (EqE _ _))) = True
    isConstr (Conn Or g1 g2) = isConstr g1 && isConstr g2
    isConstr _ = False
isAllImpliesExists _ = False

-- | Check if a formula is of the form not(Ex x1 ... xn. F) where F is a conjunction
-- that may contain:
--   - Atoms (action facts)
--   - Positive existential quantifiers: Ex y. G  (e.g., Ex #j. K(s)@j)
--   - Negated existential quantifiers: not(Ex y. G)  (e.g., not(Ex #r. RevLtk(A)@r))
--
-- This covers the common secrecy pattern:
--   not(Ex A B s #i. Secret(A,B,s)@i & (Ex #j. K(s)@j) & not(Ex #r. RevLtk(A)@r) & not(Ex #r. RevLtk(B)@r))
--
-- After NNF and implication conversion, this becomes:
--   All A B s #i. Secret(A,B,s)@i & (Ex #j. K(s)@j) ==> Ex #r. RevLtk(A)@r | Ex #r. RevLtk(B)@r
--
-- Which is exactly what ProVerif can handle (K in premise becomes attacker()).
isNegatedExistsWithConjunction :: LNFormula -> Bool
isNegatedExistsWithConjunction (Not (Qua Ex _ body)) =
    isValidConjunctionBody body && hasNegatedExistential body
  where
    -- Check if body is a valid conjunction structure
    -- Valid elements: atoms, Ex quantifiers (positive or negated), and And connectives
    isValidConjunctionBody (Qua Ex _ p) = isValidConjunctionBody p
    isValidConjunctionBody (Conn And p q) = isValidConjunctionBody p && isValidConjunctionBody q
    -- Allow negated existentials: not(Ex y. G)
    isValidConjunctionBody (Not (Qua Ex _ p)) = isValidConjunctionBody p
    -- Universal quantifiers inside existential body are not supported
    isValidConjunctionBody (Qua All _ _) = False
    -- Disallow other connectives at this level (Or, Imp, Iff would break the pattern)
    isValidConjunctionBody (Conn {}) = False
    -- Atoms (including action facts) are fine
    isValidConjunctionBody (Ato _) = True
    -- TF (true/false) is fine
    isValidConjunctionBody (TF _) = True
    -- Simple negated atoms are fine (like not(A@i))
    isValidConjunctionBody (Not (Ato _)) = True
    -- Any other Not should be rejected
    isValidConjunctionBody (Not _) = False

    -- Check if body contains at least one negated existential
    -- This ensures we only apply this transformation when there's something to move to conclusion
    hasNegatedExistential (Qua Ex _ p) = hasNegatedExistential p
    hasNegatedExistential (Conn And p q) = hasNegatedExistential p || hasNegatedExistential q
    hasNegatedExistential (Not (Qua Ex _ _)) = True
    hasNegatedExistential _ = False
isNegatedExistsWithConjunction _ = False

-- | -- | Check if a formula is of the form Ex x1 ... xn. F where F contains only negative existential quantifiers and conjunctions.
-- This pattern requires at least one negated existential to be useful for transformation.
isExistsWithNegatedExistentials :: LNFormula -> Bool
isExistsWithNegatedExistentials (Qua Ex _ body) = isExistsWithNegatedExistentials body
isExistsWithNegatedExistentials (Conn And p0 q0) = hasNegatedEx && checkNotExists p0 && checkNotExists q0
  where
    -- Check that there's at least one negated existential in the formula
    hasNegatedEx = hasNegExIn p0 || hasNegExIn q0
    hasNegExIn (Not (Qua Ex _ _)) = True
    hasNegExIn (Conn And p' q') = hasNegExIn p' || hasNegExIn q'
    hasNegExIn _ = False

    -- Check that all conjuncts are either atoms, negated existentials, or conjunctions thereof
    -- IMPORTANT: bare Qua Ex should NOT match - only negated ones
    checkNotExists (Not (Qua Ex _ p')) = checkExistsInNotExists p'
    checkNotExists (Conn And p' q') = checkNotExists p' && checkNotExists q'
    checkNotExists (Qua Ex _ _) = False  -- Bare existential - doesn't match this pattern
    checkNotExists (Conn {}) = False
    checkNotExists _ = True  -- Atoms are OK

    checkExistsInNotExists (Qua Ex _ p') = checkExistsInNotExists p'
    checkExistsInNotExists (Conn And p' q') = checkNotExists p' && checkNotExists q'
    checkExistsInNotExists (Conn {}) = False
    checkExistsInNotExists _ = True
isExistsWithNegatedExistentials _ = False

-- | Check if a formula has existentially quantified K (attacker knowledge) facts.
-- K facts can only be supported when universally quantified (in the premise).
-- This function returns True if there are K facts that are existentially quantified.
--
-- The quantification context is determined by:
-- - Under Ex x. P: everything is existentially quantified
-- - Under All x. P: everything is universally quantified
-- - In implication (A ==> B):
--     * Premise A stays in same context (universal if under All)
--     * Conclusion B: always existential (we're asserting B must hold)
-- - Under Not: the quantification context flips
hasExistentiallyQuantifiedKFact :: LNFormula -> Bool
hasExistentiallyQuantifiedKFact = go True  -- Start in existential context (top-level)
  where
    -- isExistential: True if we're in an existential context, False if universal
    go _isExistential (Qua Ex _ body) = go True body  -- Ex always makes context existential
    go _isExistential (Qua All _ body) = go False body  -- All makes context universal
    go _isExistential (Conn Imp premise conclusion) =
      -- Premise is always universal context (we're assuming premise holds)
      -- Conclusion is always existential context (we're asserting it)
      go False premise || go True conclusion
    go isExistential (Conn _ p q) = go isExistential p || go isExistential q
    go isExistential (Not p) = go (not isExistential) p  -- Negation flips context
    go isExistential (Ato (Action _ fact)) = isExistential && isKFactLocal fact
    go _ _ = False

    -- Check if a fact is a K fact (K() or KU())
    isKFactLocal f@(Fact tag _ _) = (tag == KUFact) || isKLogFact f

-- | Eliminate double negations: not(not(P)) ==> P
-- This should be done before any other transformations
eliminateDoubleNegations :: LNFormula -> LNFormula
eliminateDoubleNegations (Not (Not p)) = eliminateDoubleNegations p
eliminateDoubleNegations (Qua q (name, srt) p) = Qua q (name, srt) (eliminateDoubleNegations p)
eliminateDoubleNegations (Conn c p q) = Conn c (eliminateDoubleNegations p) (eliminateDoubleNegations q)
eliminateDoubleNegations (Not p) = Not (eliminateDoubleNegations p)
eliminateDoubleNegations p = p

-- | Expand negated timepoint comparisons: not(i < j) ==> (j < i) | (i = j)
-- ProVerif doesn't support not(i < j) syntax but does support <, >, <=, >=
-- We expand to the disjunction which is semantically equivalent to i >= j
expandNegatedTimepointComparisons :: LNFormula -> LNFormula
expandNegatedTimepointComparisons (Not (Ato (Less i j))) =
  -- not(i < j) becomes (j < i) || (i = j)
  Conn Or (Ato (Less j i)) (Ato (EqE i j))
expandNegatedTimepointComparisons (Qua q x p) = Qua q x (expandNegatedTimepointComparisons p)
expandNegatedTimepointComparisons (Conn c p q) = Conn c (expandNegatedTimepointComparisons p) (expandNegatedTimepointComparisons q)
expandNegatedTimepointComparisons (Not p) = Not (expandNegatedTimepointComparisons p)
expandNegatedTimepointComparisons p = p

-- | Check if a formula is of the form All x1 ... xn. A ==> (not B1) | (not B2) | ... | C1 | C2 | ...
-- where at least one disjunct is negated
-- IMPORTANT: We exclude formulas that contain equalities in negated disjuncts, as ProVerif doesn't support
-- equality constraints in reachability query premises
isAllImpliesDisjWithNegations :: LNFormula -> Bool
isAllImpliesDisjWithNegations (Qua All _ body) = isAllImpliesDisjWithNegations body
isAllImpliesDisjWithNegations (Conn Imp _ concl) = hasNegatedDisjunctWithoutComparison concl
  where
    hasNegatedDisjunctWithoutComparison (Conn Or p q) =
      hasNegatedDisjunctWithoutComparison p || hasNegatedDisjunctWithoutComparison q
    hasNegatedDisjunctWithoutComparison (Not (Qua Ex _ _)) = True
    hasNegatedDisjunctWithoutComparison (Not f) = not (containsComparison f)
    hasNegatedDisjunctWithoutComparison _ = False

    -- Check if a formula contains comparison constraints (EqE or Less)
    -- We want to keep negations of comparisons in the conclusion
    -- Equalities like (x = ch) are represented as Ato (EqE x ch)
    -- Timepoint comparisons like (#i < #j) are represented as Ato (Less i j)
    containsComparison (Ato (EqE _ _)) = True
    containsComparison (Ato (Less _ _)) = True
    containsComparison (Ato (Last _)) = False
    containsComparison (Ato (Action _ _)) = False
    containsComparison (Qua _ _ body) = containsComparison body
    containsComparison (Conn _ p q) = containsComparison p || containsComparison q
    containsComparison (Not p) = containsComparison p
    containsComparison _ = False
isAllImpliesDisjWithNegations _ = False

-- | Detect ∀x. (P ⇒ ¬Q₁ ∧ ¬Q₂ ∧ ...) pattern
-- This pattern needs to be distributed into multiple queries:
-- (∀x. P ⇒ ¬Q₁) ∧ (∀x. P ⇒ ¬Q₂) ∧ ...
-- Because ProVerif doesn't support negated events in conclusions
isAllImpliesConjWithNegations :: LNFormula -> Bool
isAllImpliesConjWithNegations (Qua All _ body) = isAllImpliesConjWithNegations body
isAllImpliesConjWithNegations (Conn Imp _ concl) = isConjOfNegatedExistentials concl
  where
    -- Check if conclusion is a conjunction where at least one conjunct is a negated existential
    isConjOfNegatedExistentials (Conn And p q) =
      (isNegatedExistential p || isConjOfNegatedExistentials p) &&
      (isNegatedExistential q || isConjOfNegatedExistentials q)
    isConjOfNegatedExistentials f = isNegatedExistential f

    isNegatedExistential (Not (Qua Ex _ _)) = True
    isNegatedExistential _ = False
isAllImpliesConjWithNegations _ = False

-- | Transform A ==> (not B1) | (not B2) | ... | C1 | C2 | ... into A & B1 & B2 & ... ==> C1 | C2 | ...
-- This moves negated disjuncts from the conclusion to the premise
-- Also pulls existential quantifiers from premise conjuncts to top level as universal quantifiers
-- When all disjuncts are negated, returns Not(A & B1 & B2 & ...) which will be handled as a leading negation
moveNegatedDisjunctsToPremise :: LNFormula -> LNFormula
moveNegatedDisjunctsToPremise fm = case fm of
  Qua All x p ->
    -- Process the body and then re-wrap with All, but also pull out any new quantifiers
    let p' = moveNegatedDisjunctsToPremise p
     in case p' of
          -- If the result has new All quantifiers at the top, merge them
          Qua All y body -> Qua All x (Qua All y body)
          _ -> Qua All x p'
  Conn Imp premise conclusion ->
    let (negatedTerms, positiveTerms) = partitionDisjuncts conclusion
     in if null negatedTerms
          then fm  -- No negated terms, return unchanged
          else
            -- Build new premise: premise & B1 & B2 & ...
            let newPremise = buildConjunction (premise : negatedTerms)
             in case positiveTerms of
                  -- All disjuncts were negated: pull Ex quantifiers and return Not(premise)
                  -- This will be properly handled as a leading negation by the existing machinery
                  [] ->
                    let prenexForm = prenex newPremise
                     in Not prenexForm
                  -- Some positive terms remain: build implication and pull Ex quantifiers
                  (t:ts) ->
                    let newConclusion = buildDisjunction (t:ts)
                        implication = Conn Imp newPremise newConclusion
                     in pullExFromPremise implication
  _ -> fm
  where
    -- Partition disjuncts into (negated terms with negation removed, positive terms)
    partitionDisjuncts :: LNFormula -> ([LNFormula], [LNFormula])
    partitionDisjuncts (Conn Or p q) =
      let (negsP, posP) = partitionDisjuncts p
          (negsQ, posQ) = partitionDisjuncts q
       in (negsP ++ negsQ, posP ++ posQ)
    partitionDisjuncts (Not p) = ([p], [])  -- Remove the Not, add to negated terms
    partitionDisjuncts p = ([], [p])  -- Add to positive terms

    -- Pull existential quantifiers from premise conjuncts to top level as universal
    -- Transform: (A & Ex x. B) ==> C into All x. (A & B) ==> C
    -- The quantifiers are pulled out of the implication entirely
    pullExFromPremise :: LNFormula -> LNFormula
    pullExFromPremise (Conn Imp premise conclusion) =
      let premise' = convertExToAllInConj premise
          prenexPremise = prenex premise'
       in pullQuantifiersOut (Conn Imp prenexPremise conclusion)
    pullExFromPremise f = f

    -- Pull All quantifiers from the premise of an implication to the outside
    -- When moving a quantifier out, we must shift indices in the conclusion
    -- to account for the new quantifier level
    pullQuantifiersOut :: LNFormula -> LNFormula
    pullQuantifiersOut (Conn Imp (Qua All x premise) conclusion) =
      -- Shift free indices in conclusion by 1 to account for the new quantifier
      let shiftedConclusion = shiftFreeIndices 1 conclusion
       in Qua All x (pullQuantifiersOut (Conn Imp premise shiftedConclusion))
    pullQuantifiersOut f = f

    -- Convert Ex quantifiers to All quantifiers within conjunctions
    convertExToAllInConj :: LNFormula -> LNFormula
    convertExToAllInConj (Conn And p q) =
      convertExToAllInConj p .&&. convertExToAllInConj q
    convertExToAllInConj (Qua Ex x body) =
      Qua All x (convertExToAllInConj body)
    convertExToAllInConj (Qua q x body) =
      Qua q x (convertExToAllInConj body)
    convertExToAllInConj f = f

-- | Distribute implication over a conjunction of negated existentials
-- Transforms: ∀x. (P ⇒ ¬Q₁ ∧ ¬Q₂) into (∀x. P ⇒ ¬Q₁) ∧ (∀x. P ⇒ ¬Q₂)
-- which is equivalent to: not(∃x. P ∧ Q₁) ∧ not(∃x. P ∧ Q₂)
-- This produces a top-level conjunction that will be split by splitTopLvlConns
-- Each resulting formula will be processed independently with leading negation
distributeImplicationOverConjunction :: LNFormula -> LNFormula
distributeImplicationOverConjunction fm = case fm of
  Qua All x body ->
    case distributeImplicationOverConjunction body of
      -- If the body became a conjunction, distribute the All over it
      -- Then recursively process each part to convert Qua All (Not (Qua Ex ...)) to Not (Qua Ex ...)
      Conn And p q ->
        let leftProcessed = distributeImplicationOverConjunction (Qua All x p)
            rightProcessed = distributeImplicationOverConjunction (Qua All x q)
        in Conn And leftProcessed rightProcessed
      -- If the body is Not (Qua Ex ...), pull the Not outside and convert All to Ex
      -- All x. not(Ex y. P) is equivalent to not(Ex x y. P)
      Not (Qua Ex y innerBody) -> Not (Qua Ex x (Qua Ex y innerBody))
      -- If the body is a single Not (Qua Ex ...) without nested Qua Ex
      Not innerBody -> Not (Qua Ex x innerBody)
      body' -> Qua All x body'
  Conn Imp premise (Conn And concl1 concl2) ->
    -- Distribute: (P => Q1 & Q2) becomes (P => Q1) & (P => Q2)
    -- Then recursively process in case there are more conjuncts
    let left = distributeImplicationOverConjunction (Conn Imp premise concl1)
        right = distributeImplicationOverConjunction (Conn Imp premise concl2)
     in Conn And left right
  Conn Imp premise (Not (Qua Ex x body)) ->
    -- For a single negated existential: P => not(Ex x. Q)
    -- Transform to: not(Ex x. P & Q)
    -- This is done by moving P into the existential and negating the whole thing
    let -- Shift premise indices to account for the new quantifier
        shiftedPremise = shiftFreeIndices 1 premise
        -- The body already contains nested existentials, just add the conjunction
        newBody = Conn And shiftedPremise body
     in Not (Qua Ex x newBody)
  _ -> fm

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

splitTopLvlConns _ step fm = ([fm], mempty, step)

------------------------------------------------------------------------------
-- Printers for Restrictions and ProVerif Lemmas
------------------------------------------------------------------------------

data PVElement = R | RSL

ppAtomR :: S.Set String -> TypingEnvironment -> Bool -> (LNTerm -> Doc) -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppAtomR ruleIdEvents te b = ppProtoAtomR ruleIdEvents te b (const emptyDoc)

-- only used for ProVerif queries display
-- the Bool is set to False when we must negate the atom
ppNAtomR :: S.Set String -> TypingEnvironment -> Bool -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppNAtomR ruleIdEvents te b = ppAtomR ruleIdEvents te b (fst . ppLNTerm emptyTC)

ppProtoAtomR :: (Ord a1, Show a1, Show c, Typeable a1, HighlightDocument a2) => S.Set String -> TypingEnvironment -> Bool -> (s (Term (Lit c a1)) -> a2) -> (Term (Lit c a1) -> a2) -> ProtoAtom s (Term (Lit c a1)) -> (a2, M.Map a1 SapicType)
ppProtoAtomR ruleIdEvents te _ _ ppT (Action _ f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | (tag == KUFact) || isKLogFact f -- treat KU() and K() facts the same
    =
      (ppFactL "attacker" ts, M.empty)
  | otherwise =
      ( text "event(" <> eventArgs ('e' : factTagName tag) ts <> text ")",
        typeVarsEvent te tag ts
      )
  where
    factName = factTagName tag
    useRuleId = factName `S.member` ruleIdEvents
    ppFactL n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppT t
    eventArgs n t
      | useRuleId = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ (text "rid" : map ppT t)
      | otherwise = ppFactL n t
ppProtoAtomR _ _ _ ppS _ (Syntactic s) = (ppS s, M.empty)
ppProtoAtomR _ _ False _ ppT (EqE l r) =
  (sep [ppT l <-> opEqual, ppT r], M.empty)
ppProtoAtomR _ _ True _ ppT (EqE l r) =
  (sep [ppT l <-> text "<>", ppT r], M.empty)
-- sep [ppNTerm l <-> text "≈", ppNTerm r]
ppProtoAtomR _ _ _ _ ppT (Less u v) = (ppT u <-> opLess <-> ppT v, M.empty)
ppProtoAtomR _ _ _ _ ppT (Subterm u v) = (text "subterm(" <> ppT u <> comma <> ppT v <> text ")", M.empty)
ppProtoAtomR _ _ _ _ _ (Last i) = (operator_ "last" <> parens (text (show i)), M.empty)

ppLFormulaR ::
  (MonadFresh m, Ord c, HighlightDocument b, Functor syn) =>
  Bool -> -- True if we want to remove timepoint declarations.
  S.Set String -> -- events requiring rule identifiers
  TypingEnvironment ->
  (TypingEnvironment -> Bool -> ProtoAtom syn (Term (Lit c LVar)) -> (b, M.Map LVar SapicType)) ->
  ProtoFormula syn (String, LSort) c LVar ->
  m ([LVar], (b, M.Map LVar SapicType))
ppLFormulaR keepTimeVars _ruleIdEvents te ppAt =
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
        pure (filter (\v -> keepTimeVars || lvarSort v /= LSortNode) (vs ++ vsp), d')

ppQueryFormulaR ::
  (MonadFresh m) =>
  Bool -> -- True if we want to remove timepoint declarations.
  PVElement ->
  M.Map String String ->
  S.Set String -> -- events requiring rule identifiers
  TypingEnvironment ->
  ProtoFormula Unit2 (String, LSort) Name LVar ->
  [LVar] ->
  String ->
  m Doc
ppQueryFormulaR keepTimeVars pe ridNames0 ruleIdEvents te fm extravs attrs = do
  -- Per-occurrence rule-id variables only make sense while timepoints are kept.
  let ridNames = if keepTimeVars then ridNames0 else M.empty
  (vs, (p, typeVars)) <- ppLFormulaR keepTimeVars ruleIdEvents te (if keepTimeVars then ppNAtom ridNames ruleIdEvents else ppNAtomR ruleIdEvents) fm
  let includeRuleId
        | M.null ridNames = formulaUsesRuleIdEvents ruleIdEvents fm
        | otherwise =
            any
              (\(tv, tag) -> tag `S.member` ruleIdEvents && tv `M.notMember` ridNames)
              (collectEventTimeVars fm)
  let ruleIdVar = text "rid:bitstring"
  let ridEqVars = [text (n ++ ":bitstring") | n <- S.toList . S.fromList $ M.elems ridNames]
  let allVars = map (ppTimeTypeVar typeVars) (S.toList . S.fromList $ extravs ++ vs)
  let quantifiedVars = [ruleIdVar | includeRuleId] ++ ridEqVars ++ allVars
  pure $
    sep
      [ text word <> fsep (punctuate comma quantifiedVars) <> text ";",
        nest 1 p,
        text attrs,
        text "."
      ]
  where
    word = case pe of
      R -> "restriction "
      RSL -> "axiom "

ppQueryFormulaExR :: Bool -> PVElement -> M.Map String String -> S.Set String -> TypingEnvironment -> LNFormula -> [LVar] -> String -> Doc
ppQueryFormulaExR keepTimeVars pe ridNames ruleIdEvents te fm vs attrs =
  Precise.evalFresh (ppQueryFormulaR keepTimeVars pe ridNames ruleIdEvents te fm vs attrs) (avoidPrecise fm)

ppRestrictFormulaR ::
  PVElement ->
  M.Map String String ->
  S.Set String -> -- events requiring rule identifiers
  TypingEnvironment ->
  LNFormula ->
  String ->
  Precise.FreshT Data.Functor.Identity.Identity Doc
ppRestrictFormulaR pe ridNames ruleIdEvents te frm attrs =
  if any (\(Fact tag _ _) -> factTagName tag == "KU") (formulaFacts frm) -- don't allow KU facts, nothing corresponding in PV
    || (hasLessOrTmpEqInPremise frm && not (hasDistinctFact frm)) -- by this point we have stripped the less if that was possible in the 1st place
    then pure $ ppFail frm
    else let transformedFrm = allImplExLessWoTmps frm
             -- Flatten nested implications for axioms: A => (B => C) becomes (A & B) => C
             flattenedFrm = flattenNestedImplications transformedFrm
         in if hasTopLevelNegatedAction flattenedFrm
            then pure $ ppFailNegatedAction flattenedFrm
            -- Check for nested implications in conclusion (axioms don't support this)
            else if rejectNestedImplicationInConclusion && hasNestedImplicationInConclusion flattenedFrm
            then pure $ ppFailNestedImpl flattenedFrm
            else pp flattenedFrm
  where
    -- Check if the formula has nested implications in the conclusion
    -- This is not supported for axioms in ProVerif
    rejectNestedImplicationInConclusion = case pe of
      R -> False
      RSL -> True

    hasNestedImplicationInConclusion = checkNested False
      where
        checkNested inConc (Qua _ _ q) = checkNested inConc q
        checkNested False (Conn Imp _ q) = checkNested True q  -- Enter conclusion
        checkNested True (Conn Imp _ _) = True  -- Nested implication in conclusion
        checkNested inConc (Conn _ l r) = checkNested inConc l || checkNested inConc r
        checkNested inConc (Not n) = checkNested inConc n
        checkNested _ _ = False

    ppFailNestedImpl fm = text "(*" <> prettyLNFormula fm <> text "*)" $$
                text ("(* " ++ failMsg ++ " has nested implication in conclusion which is not supported for axioms in ProVerif. *)") $$
                text ""
      where
        failMsg = case pe of
          R -> "Restriction"
          RSL -> "Axiom"

    pp (Not fm@(Qua Ex _ _)) = do
      (vs, _, fm') <- openFormulaPrefix fm
      -- Check if this is a simple negated action that can't be rewritten
      if isSimpleNegatedAction (Not fm)
        then pure $ ppFailSimpleNegatedAction (Not fm)
        else if isQuantifierFree fm'
          then pure $ ppOk fm' vs
          else
            -- Check if it could be rewritten to positive form
            case canRewriteNegatedRestriction (Not fm) of
              Just rewriteHint -> pure $ ppFailWithRewriteHint (Not fm) rewriteHint
              Nothing -> pure $ ppFail (Not fm)
    pp fm@(Qua All _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      handleUniversalFormula fm fm'
    pp fm = pure $ ppFail fm
    ppOk f l = ppQueryFormulaExR keepTimeVars pe ridNames ruleIdEvents te f l attrs
      where
        keepTimeVars = case pe of
          R -> True
          RSL -> hasDistinctFact frm || hasTimepointEqInConclusion frm
    ppFail fm = text "(*" <> prettyLNFormula fm <> text "*)" $$
                text ("(* " ++ failMsg ++ " translation failed. Results may be incomplete. *)") $$
                text ""
      where
        failMsg = case pe of
          R -> "Restriction"
          RSL -> "Axiom"
    -- Special failure message for negated actions (from exists-trace lemmas with leading negation)
    ppFailNegatedAction fm = text "(*" <> prettyLNFormula fm <> text "*)" $$
                text ("(* " ++ failMsg ++ " has negated event (from exists-trace lemma with negation). Cannot translate to ProVerif. *)") $$
                text ""
      where
        failMsg = case pe of
          R -> "Restriction"
          RSL -> "Axiom"
    -- Failure message for simple negated actions like not(Ex x i. Neq(x,x)@i)
    ppFailSimpleNegatedAction fm = text "(*" <> prettyLNFormula fm <> text "*)" $$
                text ("(* " ++ failMsg ++ " contains negated event that cannot be expressed in ProVerif. *)") $$
                text ""
      where
        failMsg = case pe of
          R -> "Restriction"
          RSL -> "Axiom"
    -- Failure message with a rewrite hint
    ppFailWithRewriteHint fm hintMsg = text "(*" <> prettyLNFormula fm <> text "*)" $$
                text ("(* " ++ failMsg ++ " translation failed. " ++ hintMsg ++ " *)") $$
                text ""
      where
        failMsg = case pe of
          R -> "Restriction"
          RSL -> "Axiom"

    handleUniversalFormula fm_original fm | isQuantifierFree fm = do
      pure $ ppOk fm_original []
    handleUniversalFormula fm_original (Conn Imp p fm) | isQuantifierFree p = do
      isExDisj <- isExistentialDisjunction fm
      if isExDisj
        then pure $ ppOk fm_original []
        else do
          -- Try handling nested implications/universals
          isNestedOk <- isNestedImplicationOk fm
          pure $
            if isNestedOk
              then ppOk fm_original []
              else ppFail fm_original
    handleUniversalFormula fm_original _ = pure $ ppFail fm_original

    hasDistinctFact fm =
      any (\(Fact tag _ _) -> factTagName tag == "DistinctFact") (formulaFacts fm)

    -- Check if formula has timepoint equality/inequality in conclusion
    hasTimepointEqInConclusion fm = checkConclusion fm
      where
        checkConclusion (Qua _ _ p) = checkConclusion p
        checkConclusion (Conn Imp _ q) = hasTimepointConstraint q
        checkConclusion f = hasTimepointConstraint f

        hasTimepointConstraint (Ato a) = case a of
          EqE t1 t2 -> isTimepoint t1 || isTimepoint t2
          Less _ _ -> True
          _ -> False
        hasTimepointConstraint (Not p) = hasTimepointConstraint p
        hasTimepointConstraint (Conn _ p q) = hasTimepointConstraint p || hasTimepointConstraint q
        hasTimepointConstraint (Qua _ _ p) = hasTimepointConstraint p
        hasTimepointConstraint _ = False

        isTimepoint t = t `elem` getFormulaActsTmps fm

    -- check if a formula has timepoint comparisons/eqs in the premise
    -- (temporal constraints in the conclusion are ok for ProVerif)
    hasLessOrTmpEqInPremise fm = go False fm
      where
        go inConclusion (Qua _ _ p) = go inConclusion p  -- preserve inConclusion state through quantifiers
        go False (Conn Imp p q) = hasLessOrTmpEqAnywhere p || go True q
        go inConclusion (Conn And p q) = go inConclusion p || go inConclusion q
        go inConclusion (Conn Or p q) = go inConclusion p || go inConclusion q
        go inConclusion (Not p) = go inConclusion p
        go True _ = False  -- We're in conclusion, temporal constraints are OK
        go False (Ato a) = case a of
          Less _ _ -> True
          EqE t1 _ -> t1 `elem` getFormulaActsTmps fm
          _ -> False
        go False _ = False

    -- check if a formula has timepoint comparisons/eqs anywhere
    hasLessOrTmpEqAnywhere fm2 =
      foldFormula
        ( \a -> case a of
            Less _ _ -> True
            EqE t1 _ -> t1 `elem` getFormulaActsTmps fm2
            _ -> False
        )
        (const False)
        (const False)
        (\_ p q -> p || q)
        (\_ _ p -> p)
        fm2

    -- Get all timepoint variables from actions in a formula
    getFormulaActsTmps = foldFormula extractActionTimepoint (const []) id (\_ p q -> p ++ q) (\_ _ p -> p)
      where
        extractActionTimepoint a = case a of
          Action tf _ -> [tf]
          _ -> []

-- | Translate a restriction to ProVerif format
ppRestr :: S.Set String -> TypingEnvironment -> Restriction -> Doc
ppRestr ruleIdEvents te rstr =
  timepointComment
    $$ text "(*" <> text rstr._rstrName <> text "*)"
    $$ case tryRewriteNegatedRestriction fm of
         Just rewritten ->
           -- Successfully rewrote the negated restriction
           text "(* Original: " <> prettyLNFormula rstr._rstrFormula <> text " *)"
           $$ Precise.evalFresh (ppRestrictFormulaR R (ridNamesFor rewritten) ruleIdEvents te rewritten "") (avoidPrecise rewritten)
         Nothing ->
           -- Check for unsupported patterns
           if hasNestedImplicationInConjunction fm
           then text "(* " <> prettyLNFormula rstr._rstrFormula <> text " *)"
                $$ text "(* Formula has nested implications inside conjunctions (e.g., A => ((B => C) & D))."
                $$ text "   This pattern cannot be soundly transformed to ProVerif's supported fragment."
                $$ text "   The formula is outside the supported ProVerif fragment. *)"
                $$ text ""
           else if hasVariableCaptureInNestedImplication fm
           then text "(* " <> prettyLNFormula rstr._rstrFormula <> text " *)"
                $$ text "(* Formula has variable capture in nested quantified implications (e.g., A(x) => (All x. B => C))."
                $$ text "   Flattening would change the semantics. *)"
                $$ text ""
           else if hasProblematicNegation fm
           then text "(* " <> prettyLNFormula fm <> text " *)"
                $$ text "(* Restriction has negated event which is not supported in ProVerif. *)"
                $$ text ""
           else Precise.evalFresh (ppRestrictFormulaR R (ridNamesFor fm) ruleIdEvents te fm "") (avoidPrecise fm)
  where
    -- Apply transformations for restrictions:
    -- 1. First simplify (converts A => F to Not A)
    -- 2. Then eliminate temporal equalities by unifying the equated timepoints
    --    (must happen before constraints are moved to the conclusion)
    -- 3. Then move constraints to conclusion
    -- 4. Then move negated actions to conclusion: (A & not(B)) => C -> A => (C | B)
    -- 5. Then expand negated timepoint comparisons
    -- 6. Then flatten nested implications: A => (B => C) -> (A & B) => C
    --    (ProVerif doesn't allow nested implications in restrictions)
    -- 7. Finally pull negations to top (converts All x. Not A to Not (Ex x. A))
    -- This order is important: simplify first so A => F becomes Not A,
    -- then pullNegationsToTop can pull that Not to the top level
    simplifiedFormula =
      transformWithPullNots
        $ simplifyFormula
        $ flattenNestedImplications
        $ expandNegatedTimepointComparisons
        $ moveNegatedActionsToConclusion
        $ moveConstraintsToConclusion
        $ eliminateTemporalEqualities
        $ simplifyFormula rstr._rstrFormula
    needsRuleId = formulaHasSharedTimepoints simplifiedFormula
    timepointComment = if needsRuleId
                       then text "(* Timepoints in restriction have been split *)"
                       else text ""
    fm = if needsRuleId
         then makeTimeVarsDistinct simplifiedFormula
         else simplifiedFormula
    -- Per-occurrence rule-id variables (and rule-id equalities for surviving
    -- temporal equalities, e.g. uniqueness restrictions on instrumented
    -- events); split-timepoint restrictions keep the shared "rid" scheme.
    ridNamesFor f = if needsRuleId then M.empty else ridOccurrenceNames ruleIdEvents f

    -- Check if a formula has a problematic negation (negated event at top level)
    hasProblematicNegation (Not f) = hasEventAnywhere f
    hasProblematicNegation _ = False

    hasEventAnywhere (Ato (Action _ _)) = True
    hasEventAnywhere (Not f) = hasEventAnywhere f
    hasEventAnywhere (Conn _ f1 f2) = hasEventAnywhere f1 || hasEventAnywhere f2
    hasEventAnywhere (Qua _ _ f) = hasEventAnywhere f
    hasEventAnywhere _ = False

    -- Try to rewrite negated restrictions to positive form
    -- Pattern: not((A@i & B@j) & (i ≠ j)) → (A@i & B@j) => (i = j)
    -- Pattern: not(Ex... (A@i & A@j) & (i ≠ j)) → All... (A@i & A@j) => (i = j)
    tryRewriteNegatedRestriction :: LNFormula -> Maybe LNFormula
    tryRewriteNegatedRestriction (Not fm') = tryRewriteNegatedBody fm'
    tryRewriteNegatedRestriction _ = Nothing

    -- Try to rewrite the body of a negated formula
    tryRewriteNegatedBody :: LNFormula -> Maybe LNFormula
    -- not(Ex x. P) -> All x. not(P) ... but we need to rewrite not(P) further
    tryRewriteNegatedBody (Qua Ex v f) = do
      rewritten <- tryRewriteNegatedBody f
      Just $ Qua All v rewritten
    -- Pattern: not((P) & (i ≠ j)) -> P => (i = j)
    -- Note: inequality (i ≠ j) is represented as Not (EqE i j)
    tryRewriteNegatedBody (Conn And premise (Not (Ato (EqE t1 t2)))) =
      Just $ Conn Imp premise (Ato (EqE t1 t2))
    tryRewriteNegatedBody _ = Nothing

-- | Printer for reuse/src lemmas as ProVerif axioms.
-- | Different than ppLemma in that it ignores timepoints and does transformations custom to these lemmas.
ppAxiomLemma :: S.Set String -> TypingEnvironment -> Lemma ProofSkeleton -> Doc
ppAxiomLemma ruleIdEvents te l =
  timepointComment
    $$ text "(*"
    <> text l._lName
    <> text " [reuse/source lemma translated as axiom]"
    <> text "*)"
    $$ if hasNestedImplicationInConjunction fm
       then text "(* " <> prettyLNFormula l._lFormula <> text " *)"
            $$ text "(* Formula has nested implications inside conjunctions (e.g., A => ((B => C) & D))."
            $$ text "   This pattern cannot be soundly transformed to ProVerif's supported fragment."
            $$ text "   The formula is outside the supported ProVerif fragment. *)"
            $$ text ""
       else if hasVariableCaptureInNestedImplication fm
       then text "(* " <> prettyLNFormula l._lFormula <> text " *)"
            $$ text "(* Formula has variable capture in nested quantified implications (e.g., A(x) => (All x. B => C))."
            $$ text "   Flattening would change the semantics. *)"
            $$ text ""
       else if hasNegatedEventInFormula fm
       then text "(* " <> prettyLNFormula l._lFormula <> text " *)"
            $$ text "(* Axiom has negated event (not(...event...)) which is not supported in ProVerif. *)"
            $$ text ""
       else Precise.evalFresh (ppRestrictFormulaR RSL ridNames ruleIdEvents te fm "") (avoidPrecise fm)
  where
    -- Per-occurrence rule-id variables, as for restrictions.
    ridNames = if needsRuleId then M.empty else ridOccurrenceNames ruleIdEvents fm
    -- Apply same transformations as for restrictions
    -- Order matters:
    -- 1. First eliminate temporal equalities by unifying the equated timepoints
    --    (must happen before constraints are moved to the conclusion)
    -- 2. Then move negated actions from premise to conclusion BEFORE pullNots
    --    (pullNots combines negations via De Morgan, making individual movement impossible)
    -- 3. Then move constraints to conclusion
    -- 4. Then apply pullNots to normalize negations
    -- 5. Then flatten nested implications: A => (B => C) -> (A & B) => C
    -- 6. Then expand negated timepoint comparisons: not(i < j) -> (j < i) | (i = j)
    -- 7. Finally simplify
    simplifiedFormula =
      simplifyFormula
        $ flattenNestedImplications
        $ expandNegatedTimepointComparisons
        $ transformWithPullNots
        $ moveConstraintsToConclusion
        $ moveNegatedActionsToConclusion
        $ eliminateTemporalEqualities l._lFormula
    needsRuleId = formulaHasSharedTimepoints simplifiedFormula
    timepointComment = if needsRuleId
                       then text "(* Timepoints in lemma have been split *)\n"
                       else text ""
    fm = if needsRuleId
         then makeTimeVarsDistinct simplifiedFormula
         else simplifiedFormula

-- Check if a formula is of the form "All x1 .. xn tA. A(x1 ... xn)@tA ==> not (Ex y1 ... yn tB. B(y1 ... yn)@tB)"
isAllActionsImpliesNotExists :: LNFormula -> Bool
isAllActionsImpliesNotExists (Qua All _ body) = isAllActionsImpliesNotExists body
isAllActionsImpliesNotExists (Conn Imp p (Not q)) = onlyActionAtoms p && hasOnlyExistentials q
  where
    hasOnlyExistentials (Qua Ex _ body') = hasOnlyExistentials body'
    hasOnlyExistentials (Ato a) = isActionAtom a
    hasOnlyExistentials _ = False
    -- Check if formula contains only action atoms (possibly connected by conjunctions)
    onlyActionAtoms (Ato at) = isActionAtom at
    onlyActionAtoms (Conn And p1 p2) = onlyActionAtoms p1 && onlyActionAtoms p2
    onlyActionAtoms _ = False
isAllActionsImpliesNotExists _ = False

-- Check if a formula is of the form "All x1 .. xn tA. A(x1 ... xn)@tA ==> Ex y1 ... yn tB. B(y1 ... yn)@tB & tB < tA"
-- If so, remove the less (it's implicit as we translate to a basic correspondence).
allImplExLessWoTmps :: LNFormula -> LNFormula
allImplExLessWoTmps (Qua All x p) = Qua All x $ allImplExLessWoTmps p
allImplExLessWoTmps (Conn Imp (Ato (Action tA fA)) q) = Conn Imp (Ato (Action tA fA)) $ case q of
  (Qua Ex x p) -> Qua Ex x $ hasOnlyExistentials p
  f -> f
  where
    hasOnlyExistentials (Qua Ex x p) = Qua Ex x $ hasOnlyExistentials p
    hasOnlyExistentials f@(Conn And (Ato (Action tB fB)) (Ato (Less tB' tA'))) = if tA == tA' && tB == tB' then Ato (Action tB fB) else f
    hasOnlyExistentials f = f
allImplExLessWoTmps f = f

-- | Check if a formula contains a negated action that will produce not(event(...)) in ProVerif.
-- This is used for lemmas/queries where the formula to translate has a negation that can't be
-- stripped (unlike Not (Qua Ex ...) which is handled specially).
--
-- The key patterns that produce invalid ProVerif:
-- - Not (Ato (Action ...)) - bare negated action
-- - Not (Qua All _ body) where body contains actions - renders as not(event(...))
hasNegatedActionInFormula :: LNFormula -> Bool
hasNegatedActionInFormula (Not (Ato (Action _ _))) = True
hasNegatedActionInFormula (Not (Qua All _ body)) = containsAction body
  where
    containsAction (Ato (Action _ _)) = True
    containsAction (Qua All _ b) = containsAction b
    containsAction (Qua Ex _ b) = containsAction b
    containsAction (Conn _ p q) = containsAction p || containsAction q
    containsAction _ = False
-- Recurse through quantifiers and connectives to find nested negated actions
hasNegatedActionInFormula (Qua _ _ body) = hasNegatedActionInFormula body
hasNegatedActionInFormula (Conn _ p q) = hasNegatedActionInFormula p || hasNegatedActionInFormula q
hasNegatedActionInFormula _ = False

-- | Check if a formula has a negated action that cannot be translated to ProVerif.
-- The pattern Not (Qua Ex ...) at the TOP level is fine - it becomes a reachability query
-- with a "leading negation" comment. What we need to reject is negated actions
-- INSIDE a query body, like: A ==> not(Ex x. B(x)@i) where the negation is in the conclusion
-- of an implication, or bare Not (Ato (Action _ _)).
--
-- NOTE: For queries, Not (Qua Ex _ body) is VALID and handled by renderFormula which
-- strips the Not and emits the inner existential as a reachability query.
hasTopLevelNegatedAction :: LNFormula -> Bool
hasTopLevelNegatedAction (Not (Ato (Action _ _))) = True
-- Not (Qua Ex ...) at the very top level is fine - it's handled as a leading negation query
-- We only need to check inside quantifiers or connectives
hasTopLevelNegatedAction (Qua All _ body) = hasTopLevelNegatedAction body
hasTopLevelNegatedAction (Qua Ex _ body) = hasTopLevelNegatedAction body
hasTopLevelNegatedAction (Conn And p q) = hasTopLevelNegatedAction p || hasTopLevelNegatedAction q
hasTopLevelNegatedAction (Conn Or p q) = hasTopLevelNegatedAction p || hasTopLevelNegatedAction q
-- Check for negated events inside implications (conclusion)
hasTopLevelNegatedAction (Conn Imp _ concl) = hasNegatedEventInConclusion concl
  where
    -- Check if conclusion contains a negated event that ProVerif can't handle
    hasNegatedEventInConclusion (Not (Ato (Action _ _))) = True
    hasNegatedEventInConclusion (Not (Qua Ex _ _)) = True  -- not(Ex ...) in conclusion is problematic
    hasNegatedEventInConclusion (Conn And p q) = hasNegatedEventInConclusion p || hasNegatedEventInConclusion q
    hasNegatedEventInConclusion (Conn Or p q) = hasNegatedEventInConclusion p || hasNegatedEventInConclusion q
    hasNegatedEventInConclusion _ = False
hasTopLevelNegatedAction _ = False

loadRestrictions :: S.Set String -> TranslationContext -> TypingEnvironment -> OpenTheory -> ([Doc], S.Set ProVerifHeader)
loadRestrictions sharedEventTags _ te thy =
  let rs = theoryRestrictions thy
      docs = map (ppRestr sharedEventTags te) rs
      allFacts = concatMap (formulaFacts . L.get rstrFormula) rs
      validFacts =
        [ f | f@(Fact tag _ _) <- allFacts, factTagName tag `notElem` ["OnlyOnce", "DistinctFact"]
        ]
      headers = makeEventHeaders sharedEventTags validFacts
   in (docs, headers)

-- | Detect events that share timepoints in restrictions
detectSharedTimepointEventsRestrictions :: [Restriction] -> S.Set String
detectSharedTimepointEventsRestrictions restrictions =
  S.unions $ map (eventsSharingTimepoints . eliminateTemporalEqualities . _rstrFormula) restrictions
