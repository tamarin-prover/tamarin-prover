{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Sapic processes to Proverif

module Export (
    prettyProVerifTheory,
    prettyProVerifEquivTheory,
    prettyDeepSecTheory
) where
import         Term.Builtin.Rules
import         Term.SubtermRule

import         Theory
import         Theory.Sapic
import         Theory.Module
import         Text.PrettyPrint.Class
import         Theory.Text.Pretty

import         Sapic.Annotation
import         Sapic.States
import         Sapic.Report
import         Sapic.Typing
import         Sapic.Exceptions

import         RuleTranslation

import         System.IO.Unsafe
import         System.IO
import           Control.Monad.Fresh
import           Control.Exception
import qualified Control.Monad.Trans.PreciseFresh as Precise

import qualified Data.Set as S
import qualified Data.Label as L
import qualified Data.Map as M
import Data.List as List

import qualified Data.ByteString.Char8 as BC
import qualified Data.Functor.Identity
import Data.Bifunctor
import Data.Char
import Data.Data
import Data.Maybe

data Translation =
   ProVerif
   | DeepSec
  deriving( Ord, Eq, Typeable, Data )

exportModule :: Translation -> ModuleType
exportModule ProVerif = ModuleProVerif
exportModule DeepSec = ModuleDeepSec

data TranslationContext = TranslationContext
  { trans :: Translation,
    attackerChannel :: Maybe LVar,
    hasBoundStates :: Bool,
    hasUnboundStates :: Bool,
    predicates :: [Predicate]
  }
  deriving (Eq, Ord)
emptyTC :: TranslationContext
emptyTC =
  TranslationContext
    { trans = ProVerif,
      attackerChannel = Nothing,
      hasBoundStates = False,
      hasUnboundStates = False,
      predicates = []
    }

-- Failure function performing an unsafe IO failure
translationFail :: String -> a
translationFail s = unsafePerformIO (fail s)


translationWarning :: String -> a -> a
translationWarning s cont = unsafePerformIO printWarning
  where
    printWarning = do
      hPutStr stderr $ "WARNING: " ++ s
      return cont
                    
------------------------------------------------------------------------------
-- Core Proverif Export
------------------------------------------------------------------------------

proverifTemplate :: Document d => [d] -> [d] -> d -> [d] -> [d] -> [d] -> [d] -> d
proverifTemplate headers queries process macroproc ruleproc lemmas comments =
  vcat headers
    $$ vcat queries
    $$ vcat lemmas
    $$ vcat macroproc
    $$ vcat ruleproc
    $$ text "process"
    $$ nest 4 process
    $--$ vcat (intersperse (text "") comments)

prettyProVerifTheory :: (ProtoLemma LNFormula ProofSkeleton -> Bool) -> (OpenTheory, TypingEnvironment) -> IO Doc
prettyProVerifTheory lemSel (thy, typEnv) = do
  headers <- loadHeaders tc thy typEnv
  headers2 <- checkDuplicates $ (S.toList . filterHeaders $ baseHeaders `S.union` headers `S.union` prochd `S.union` macroprochd) ++ S.toList (filterHeaders ruleHeaders)
  let hd = attribHeaders tc headers2
  return $ proverifTemplate hd queries proc' macroproc ruleproc lemmas comments
  where
    tc = emptyTC {predicates = theoryPredicates thy}
    (proc, prochd, hasBoundState, hasUnboundState) = loadProc tc thy
    (ruleproc, ruleComb, (baseRuleHeaders, destrHeaders, frHeaders, tblHeaders, evHeaders)) = loadRules thy
    baseRuleHeaderSet = S.fromList $ map (uncurry4 Sym) baseRuleHeaders
    destrHeaderSet = S.fromList $ map (uncurry4 Eq) destrHeaders
    frHeaderSet = S.fromList $ map (uncurry4 Sym) frHeaders
    tblHeaderSet = S.fromList $ map (uncurry Table) tblHeaders
    evHeaderSet = S.fromList $ map (uncurry HEvent) evHeaders
    ruleHeaders = baseRuleHeaderSet `S.union` destrHeaderSet `S.union` frHeaderSet `S.union` tblHeaderSet `S.union` evHeaderSet
    proc'
      | null (theoryProcesses thy) = ruleComb
      | null (theoryRules thy) = proc
      | otherwise = proc <-> text "|" <-> ruleComb
    baseHeaders = if hasUnboundState then stateHeaders else S.empty
    queries = loadQueries thy
    lemmas = loadLemmas lemSel tc typEnv thy
    (macroproc, macroprochd) =
      -- if stateM is not empty, we have inlined the process calls, so we don't reoutput them
      if hasBoundState then ([text ""], S.empty) else loadMacroProc tc thy
    uncurry4 f (a,b,c,d) = f a b c d
    comments = [ text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy ]

-- ProVerif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProVerifHeader
  = Type String -- type declaration
  | Sym String String String [String] -- symbol declaration, (symkind,name,type,attr)
  | Fun String String Int String [String] -- symbol declaration, (symkind,name,arity,types,attr)
  | HEvent String String
  | Table String String
  | Eq String String String String -- eqtype, quantif, equation pub/priv
  deriving (Ord, Show, Eq)

stateHeaders :: S.Set ProVerifHeader
stateHeaders =
  S.fromList
    [ Table "tbl_states_handle" "(bitstring,channel)", --the table for linking states identifiers and channels
      Table "tbl_locks_handle" "(bitstring,channel)" --the table for linking locks identifiers and channels
    ]

-- We provide a dedicated DDH builtin.
builtins :: [(String, S.Set ProVerifHeader)]
builtins =
  map
    (second S.fromList)
    [ ( "diffie-hellman",
        [ Sym "const" "g" ":bitstring" [],
          Fun "fun" "exp" 2 "(bitstring,bitstring):bitstring" [],
          Eq "equation" "forall a:bitstring,b:bitstring;" "exp( exp(g,a),b) = exp(exp(g,b),a)" ""
        ]
      ),
      ( "locations-report",
        [ Fun "fun" "rep" 2 "(bitstring,bitstring):bitstring" ["private"]
        ]
      ),
      ( "xor",
        [ Fun "fun" "xor" 2 "(bitstring,bitstring):bitstring" [],
          Fun "fun" "zero" 0 "():bitstring" []
        ]
      ),
      ( "hashing",
        [ Fun "fun" "h" 1 "(bitstring):bitstring" []
        ]
      ),
      ( "asymmetric-encryption",
        [ Fun "fun" "aenc" 2 "(bitstring,bitstring):bitstring" [],
          Fun "fun" "pk" 1 "(bitstring):bitstring" []
        ] --Don't need to define the reduc equations here because they are already read from the theory
      ),
      ( "signing",
        [ Fun "fun" "sign" 2 "(bitstring,bitstring):bitstring" [],
          Fun "fun" "pk" 1 "(bitstring):bitstring" [],
          Fun "fun" "okay" 0 "():bitstring" []
        ]
      ),
      ( "revealing-signing",
        [ Fun "fun" "revealSign" 2 "(bitstring,bitstring):bitstring" [],
          Fun "fun" "revealVerify" 3 "(bitstring,bitstring,bitstring):bitstring" [],
          Fun "fun" "getMessage" 1 "(bitstring):bitstring" [],
          Fun "fun" "pk" 1 "(bitstring):bitstring" [],
          Fun "fun" "okay" 0 "():bitstring" []
        ]
      ),
      ( "symmetric-encryption",
        [ Fun "fun" "senc" 2 "(bitstring,bitstring):bitstring" []
        ]
      )
    ]

-- We filter out some predefined headers that we don't want to redefine.
filterHeaders :: S.Set ProVerifHeader -> S.Set ProVerifHeader
filterHeaders = S.filter (not . isForbidden)
  where
    isForbidden (Fun "fun" "true" _ _ _) = True
    isForbidden (Type "bitstring") = True
    isForbidden (Type "channel") = True
    isForbidden (Type "nat") = True    
    isForbidden _ = False

-- We cannot define a constant and a function with the same name in proverif
checkDuplicates :: MonadFail m => [ProVerifHeader] -> m [ProVerifHeader]
checkDuplicates hd = do
  let names =
        foldl
          ( \acc x -> case x of
              Fun _ n _ _ _ -> n : acc
              Sym _ n _ _ -> n : acc
              HEvent n _ -> n : acc
              Table n _ -> n : acc
              _ -> acc
          )
          []
          hd
   in let conflicts = filter ((> 1) . length) . group $ sort names
       in if null conflicts
            then return hd
            else fail ("The string " <> head (head conflicts) <> " is used for distinct constructs (function name, constant or events). You should rename the constructs.")

ppPubName :: NameId -> Doc
ppPubName (NameId n) = text $ case n of
  "zero" -> "0"
  "one"  -> "1"
  "g"    -> "g"
  _      -> "s" ++ n

-- Loader of the export functions
------------------------------------------------------------------------------
loadQueries :: Theory sig c b p TranslationElement -> [Doc]
loadQueries thy =
  map (text . L.get eText) (lookupExportInfo "queries" thy)


------------------------------------------------------------------------------
-- Core Proverif Equivalence Export
------------------------------------------------------------------------------

proverifEquivTemplate :: Document d => [d] -> [d] -> [d] -> [d] -> [d] -> d
proverifEquivTemplate headers queries equivlemmas macroproc comments =
  vcat headers
    $$ vcat queries
    $$ vcat macroproc
    $$ vcat equivlemmas
    $--$ vcat (intersperse (text "") comments)

prettyProVerifEquivTheory :: (OpenTheory, TypingEnvironment) -> IO Doc
prettyProVerifEquivTheory (thy, typEnv) = do
  headers <- loadHeaders tc thy typEnv
  headers2 <- checkDuplicates . S.toList . filterHeaders $ baseHeaders `S.union` headers `S.union` equivhd `S.union` diffEquivhd `S.union` macroprochd
  let hd = attribHeaders tc headers2
  fproc <- finalproc
  return $ proverifEquivTemplate hd queries fproc macroproc comments
  where
    tc = emptyTC {predicates = theoryPredicates thy}
    (equivlemmas, equivhd, hasBoundState, hasUnboundState) = loadEquivProc tc thy
    (diffEquivlemmas, diffEquivhd, _, diffHasUnboundState) = loadDiffProc tc thy
    baseHeaders = if hasUnboundState || diffHasUnboundState then stateHeaders else S.empty
    finalproc = do
      if length equivlemmas + length diffEquivlemmas > 1
        then fail "Error: Proverif can only support at most one equivalence or diff equivalence query."
        else return $ equivlemmas ++ diffEquivlemmas
    queries = loadQueries thy
    (macroproc, macroprochd) =
      -- if stateM is not empty, we have inlined the process calls, so we don't reoutput them
      if hasBoundState then ([text ""], S.empty) else loadMacroProc tc thy
    comments = [ text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy ]

------------------------------------------------------------------------------
-- Core DeepSec Export
------------------------------------------------------------------------------

deepsecTemplate :: Document d => [d] -> [d] -> [d] -> [d] -> [d] -> d
deepsecTemplate headers macroproc requests equivlemmas comments =
  vcat headers
    $$ vcat macroproc
    $$ vcat requests
    $$ vcat equivlemmas
    $--$ vcat (intersperse (text "") comments)

emptyTypeEnv :: TypingEnvironment
emptyTypeEnv = TypingEnvironment {vars = M.empty, events = M.empty, funs = M.empty}

prettyDeepSecTheory :: OpenTheory -> IO Doc
prettyDeepSecTheory thy = do
  headers <- loadHeaders tc thy emptyTypeEnv
  let hd =
        attribHeaders tc $
          S.toList
            ( headers
                `S.union` macroprochd
                `S.union` equivhd
            )
  return $ deepsecTemplate hd macroproc requests equivlemmas comments
  where
    tc = emptyTC {trans = DeepSec}
    requests = loadRequests thy
    (macroproc, macroprochd) = loadMacroProc tc thy
    (equivlemmas, equivhd, _, _) = loadEquivProc tc thy
    comments = [ text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy ]

-- Loader of the export functions
------------------------------------------------------------------------------
loadRequests :: Theory sig c b p TranslationElement -> [Doc]
loadRequests thy =
  map (text . L.get eText) (lookupExportInfo "requests" thy)

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

auxppTerm :: Show v => (Lit Name v -> Doc) -> VTerm Name v -> (Doc, S.Set ProVerifHeader)
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
    ppTerms sepa n lead finish = fcat
      . (text lead :)
          . (++ [text finish])
              . map (nest n) . punctuate (text sepa) . map ppTerm
    ppFun f ts =
      text (ppFunSym f ++ "(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm tm = case viewTerm tm of
      Lit (Con (Name PubName n)) ->
        if show n `elem` ["g", "one", "zero"]
          then S.empty
          -- The 's' is just prepended here instead of using sanitizeSymbol, because that function
          -- only does the prepending for reserved keywords and symbols starting with a digit. For
          -- free bitstrings however, we ALWAYS want the leading 's', to also avoid clashes with
          -- function names, rule names, event names etc. We could also do it like that for variables
          -- and function names (where we use sanitizeSymbol now), but I thought if we did it in all
          -- other places it might not be needed there, and I thought it would be better to leave as
          -- much as possible of the original naming as it is
          else S.singleton (Sym "free" ("s" ++ show n) ":bitstring" [])
      Lit  _    -> S.empty
      FApp _ ts -> foldl (\x y -> x `S.union` getHdTerm y) S.empty ts

-- pretty print a SapicTerm, collecting the constant that need to be declared
-- matchVars is the set of vars that correspond to pattern matching
-- isPattern enables the pattern match printing, which adds types to variables, and = to constants.
auxppSapicTerm :: TranslationContext -> S.Set LVar -> Bool -> SapicTerm -> (Doc, S.Set ProVerifHeader)
auxppSapicTerm tc mVars isPattern = auxppTerm ppLit
  where
    ppLit v = case v of
      Con (Name FreshName n) -> text . sanitizeSymbol 'a' $ show n
      Con (Name PubName n) | isPattern -> text "=" <> text ("s" ++ show n)
      Con (Name PubName n) -> ppPubName n
      Var (SapicLVar lvar@(LVar n LSortPub _) _)
        | S.member lvar mVars ->
          translationWarning ("Pattern matching on public variable "++n++" makes Tamarin and Proverif behaviours diverge.") $
          text "=" <> ppLVar lvar
      Var (SapicLVar lvar@(LVar n LSortFresh _) _)
        | S.member lvar mVars ->
          translationWarning ("Pattern matching on fresh variable "++n++" makes Tamarin and Proverif behaviours diverge.") $
          text "=" <> ppLVar lvar
      Var (SapicLVar lvar@(LVar n LSortNat _) _)
        | S.member lvar mVars ->
          translationWarning ("Pattern matching on natural variable "++n++" makes Tamarin and Proverif behaviours diverge.") $
          text "=" <> ppLVar lvar          
      Var (SapicLVar lvar _)
        | S.member lvar mVars -> text "=" <> ppLVar lvar
      l | isPattern -> ppTypeLit tc l
      Var (SapicLVar lvar _)  -> ppLVar lvar
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
        sh = foldl S.union S.empty shs

-- pretty print an Action, collecting the constant and events that need to be declared. It also returns a boolean, specifying if the printout can serve as the end of a process or not.
ppAction :: ProcessAnnotation LVar -> TranslationContext -> LSapicAction -> (Doc, S.Set ProVerifHeader, Bool)
ppAction ProcessAnnotation {isStateChannel = Nothing} tc (New v) =
  (text "new " <> ppTypeVar tc v, S.empty, True)
ppAction ProcessAnnotation {pureState = False, isStateChannel = Just t} tc (New v@(SapicLVar lvar _)) =
  ( extras $
      text "new " <> channel <> text "[assumeCell];"
        $$ text "new lock_" <> channel <> text "[assumeCell];"
        -- we also declare the corresponding lock channel, and initialize it
        $$ text "out(lock_" <> ppLVar lvar <> text ",0) |",
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
            $$ text "insert tbl_states_handle(" <> pt <> text ", " <> ppLVar lvar <> text ");"
            $$ text "insert tbl_locks_handle(" <> pt <> text ", lock_" <> ppLVar lvar <> text ");"
        else x
ppAction ProcessAnnotation {pureState = True, isStateChannel = Just _} tc (New v) =
  ( text "new " <> ppTypeVar tc v <> text "[assumeCell]",
    S.empty,
    True
  )
ppAction _ TranslationContext {trans = ProVerif} Rep = (text "!", S.empty, False)
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
  ( text "in(" <> pt1 <> text "," <> text pt2var <> text ");"
      $$ text "let (" <> pt2 <> text ")=" <> text pt2var <> text " in",
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
ppAction _ tc@TranslationContext {trans = ProVerif} (Event (Fact tag m ts)) = (text "event " <> pa, sh, True) -- event Headers are definde globally inside loadHeaders
  where
    (pa, sh) = ppFact tc (Fact tag m ts)
ppAction _ TranslationContext {trans = DeepSec} (Event _) = (text "", S.empty, False)
-- For pure states, we do not put locks and unlocks
ppAction ProcessAnnotation {pureState = True} TranslationContext {trans = ProVerif} (Lock _) =
  (text "", S.empty, False)
-- If there is a state channel, we simply use it
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} TranslationContext {trans = ProVerif} (Lock _) =
  ( text "in(lock_" <> ppLVar lvar <> text "," <> text "counterlock" <> ppLVar lvar <> text ":nat)",
    S.empty,
    True
  )
-- If there is no state channel, we must use the table
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans = ProVerif} (Lock t) =
  ( text "get tbl_locks_handle(" <> pt <> text "," <> text ptvar <> text ") in"
      $$ text "in(" <> text ptvar <> text " , counter" <> text ptvar <> text ":nat)",
    sh,
    True
  )
  where
    freevars = S.fromList $ map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = auxppSapicTerm tc freevars True t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)
ppAction ProcessAnnotation {pureState = True} TranslationContext {trans = ProVerif} (Unlock _) =
  (text "", S.empty, False)
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} TranslationContext {trans = ProVerif} (Unlock _) =
  ( text "out(lock_" <> ppLVar lvar <> text "," <> text "counterlock" <> ppLVar lvar <> text "+1" <> text ") | ",
    S.empty,
    False
  )
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans = ProVerif} (Unlock t) =
  (text "out(" <> text ptvar <> text " , counter" <> text ptvar <> text "+1) | ", sh, False)
  where
    (pt, sh) = ppSapicTerm tc t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)
ppAction ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = _} tc@TranslationContext {trans = ProVerif} (Insert _ c) =
  ( text "out(" <> ppLVar lvar <> text ", " <> pc <> text ") |",
    shc,
    False
  )
  where
    (pc, shc) = ppSapicTerm tc c

-- Should never happen
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = True} TranslationContext {trans = ProVerif} (Insert _ _) =
  (text "TRANSLATIONERROR", S.empty, True)
-- ppAction ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=False} tc@TranslationContext{trans=ProVerif} (Insert _ c) =
--       (text "in(" <> pt <> text ", " <> pt <> text "_dump:bitstring);"
--        $$ text "out(" <> pt <> text ", " <> pc <> text ") |"
--       , shc, False)
--   where
--     pt = ppLVar lvar
--     (pc, shc) = ppSapicTerm tc c

-- must rely on the table
ppAction ProcessAnnotation {stateChannel = Nothing, pureState = False} tc@TranslationContext {trans = ProVerif} (Insert t t2) =
  ( text "in(" <> text ptvar <> text ", " <> text dumpvar <> text ":bitstring);"
      $$ text "out(" <> text ptvar <> text " , " <> pt2 <> text ") | ",
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
  ( text "let " <> pt1 <> text "=" <> pt2 <> text " in"
      $$ ppl,
    sh1 `S.union` sh2 `S.union` pshl
  )
  where
    (ppl, pshl) = ppSapic tc pl
    (pt1, sh1) = auxppSapicTerm tc (S.map toLVar mvars) True t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic tc (ProcessComb (Let t1 t2 mvars) _ pl pr) =
  ( text "let " <> pt1 <> text "=" <> pt2 <> text " in"
      $$ ppl
      $$ text "else " <> ppr,
    sh1 `S.union` sh2 `S.union` pshl `S.union` pshr
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
  ( text name
      <> parens (fsep (punctuate comma ppts)),
    foldl S.union S.empty shs
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
ppSapic tc (ProcessComb (CondEq t1 t2) _ pl (ProcessNull _)) = (text "let (=" <> pt1 <> text ")=" <> pt2 <> text " in " $$ nest 4 (parens ppl), sh1 `S.union` sh2 `S.union` pshl)
  where
    (ppl, pshl) = ppSapic tc pl
    (pt1, sh1) = ppSapicTerm tc t1
    (pt2, sh2) = ppSapicTerm tc t2
ppSapic tc (ProcessComb (CondEq t1 t2) _ pl pr) = (text "let (=" <> pt1 <> text ")=" <> pt2 <> text " in " $$ nest 4 (parens ppl) $$ text "else" <> nest 4 (parens ppr), sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
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
ppSapic _ (ProcessComb (Lookup _ _) ProcessAnnotation {stateChannel = Nothing, pureState = True} _ (ProcessNull _)) = translationFail "Unexpected error -> please report with an issue on the github."
ppSapic tc (ProcessComb (Lookup _ c) ProcessAnnotation {stateChannel = Just (AnVar lvar), pureState = False} pl (ProcessNull _)) =
  ( text "in(" <> pt <> text ", " <> pc <> text ");"
      $$ text "out(" <> pt <> text ", " <> pc2 <> text ") |"
      $$ ppl,
    pshl
  )
  where
    pt = ppLVar lvar
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    (ppl, pshl) = ppSapic tc pl
ppSapic tc (ProcessComb (Lookup t c) ProcessAnnotation {stateChannel = Nothing, pureState = False} pl (ProcessNull _)) =
  ( text "get tbl_states_handle(" <> pt <> text "," <> text ptvar <> text ") in"
      $$ text "in(" <> text ptvar <> text " , " <> pc <> text ");"
      $$ text "out(" <> text ptvar <> text " , " <> pc2 <> text ") |"
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
  ( text "get tbl_states_handle(" <> pt <> text "," <> text ptvar <> text ") in"
      $$ nest
             4
             ( parens
                 ( text "in(" <> text ptvar <> text " , " <> pc <> text ");"
                     $$ text "out(" <> text ptvar <> text " , " <> pc2 <> text ") | "
                     $$ ppl
                 )
             )
      $$ text "else"
      $$ nest
             4
             ( parens
                 ( text "new " <> text ptvar <> text ":channel [assumeCell];" --the cell did not exists, we create it !
                     $$ text "insert tbl_states_handle(" <> pt' <> text ", " <> text ptvar <> text ");"
                     $$ text "out(" <> text ptvar <> text ",0) |"
                     $$ ppr
                 )
             ),
    sh `S.union` pshl `S.union` pshr
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
ppSapic tc@TranslationContext {trans = ProVerif} (ProcessAction Rep _ p) = (text "!" $$ parens pp, psh)
  where
    (pp, psh) = ppSapic tc p

-- TODO: have some parameter in the tc for replication numbers
ppSapic tc@TranslationContext {trans = DeepSec} (ProcessAction Rep _ p) = (text "!^3" <> parens pp, psh)
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
     in let finald =
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
   in case L.get pVars p of
        -- TODO bugfix, this is probably wrong when the macro does not have any parameter
        Nothing -> (docs, hd `S.union` heads)
        Just pvars ->
          let (new_text, new_heads) = ppSapic tc3 mainProc
           in let vrs = text "(" <> fsep (punctuate comma (map (ppTypeVar tc3) pvars)) <> text ")"
               in let headers = headersOfType $ map extractType pvars
                   in let macro_def =
                            text "let " <> text (L.get pName p) <> vrs <> text "="
                              $$ nest 4 new_text <> text "."
                       in (macro_def : docs, hd `S.union` new_heads `S.union` heads `S.union` headers)
  where
    mainProc = makeAnnotations thy $ L.get pBody p
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

loadEquivProcs :: TranslationContext -> OpenTheory -> [(PlainProcess, PlainProcess)] -> ([Doc], S.Set ProVerifHeader, Bool, Bool)
loadEquivProcs _ _ [] = ([], S.empty, False, False)
loadEquivProcs tc thy ((p1, p2) : q) =
  let (docs, heads, hadBoundStates, hadUnboundStates) = loadEquivProcs tc3 thy q
   in let (new_text1, new_heads1) = ppSapic tc3 mainProc1
       in let (new_text2, new_heads2) = ppSapic tc3 mainProc2
           in let macro_def =
                    case trans tc of
                      ProVerif ->
                        text "equivalence"
                          $$ nest 4 new_text1
                          $$ nest 4 new_text2
                      DeepSec ->
                        text "query session_equiv("
                          $$ nest 4 new_text1 <> text ","
                          $$ nest 4 new_text2 <> text ")."
               in (macro_def : docs, hd `S.union` new_heads1 `S.union` new_heads2 `S.union` heads, hasBoundSt || hadBoundStates, hasUnboundSt || hadUnboundStates)
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
mergeType :: Eq a => Maybe a -> Maybe a -> Maybe a
mergeType t Nothing = t
mergeType Nothing t = t
mergeType _ t = t

mergeEnv :: M.Map LVar SapicType -> M.Map LVar SapicType -> M.Map LVar SapicType
mergeEnv = M.mergeWithKey (\_ t1 t2 -> Just $ mergeType t1 t2) id id

typeVarsEvent :: Ord k => TypingEnvironment -> FactTag -> [Term (Lit c k)] -> M.Map k SapicType
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

ppProtoAtom :: (HighlightDocument d, Ord k, Show k, Show c) => TypingEnvironment -> Bool -> (s (Term (Lit c k)) -> d) -> (Term (Lit c k) -> d) -> ProtoAtom s (Term (Lit c k)) -> (d, M.Map k SapicType)
ppProtoAtom te _ _ ppT (Action v f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | (tag == KUFact) || isKLogFact f  -- treat KU() and K() facts the same
      = (ppFactL "attacker" ts <> opAction <> ppT v, M.empty)
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
ppProtoAtom _ _ _ ppT (Subterm u v) = (ppT u <-> opLess <-> ppT v, M.empty)
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

ppLFormula :: (MonadFresh m, Ord c, HighlightDocument b, Functor syn) => TypingEnvironment -> (TypingEnvironment -> Bool -> ProtoAtom syn (Term (Lit c LVar)) -> (b, M.Map LVar SapicType)) -> ProtoFormula syn (String, LSort) c LVar -> m ([LVar], (b, M.Map LVar SapicType))
ppLFormula te ppAt =
  pp
  where
    pp (Ato a) = return ([], ppAt te False (toLAt a))
    pp (TF True) = return ([], (operator_ "true", M.empty)) -- "T"
    pp (TF False) = return ([], (operator_ "false", M.empty)) -- "F"
    pp (Not (Ato a@(EqE _ _))) = return ([], ppAt te True (toLAt a))
    pp (Not p) = do
      (vs, (p', envp)) <- pp p
      return (vs, (operator_ "not" <> opParens p', envp)) -- text "¬" <> parens (pp a)
      -- return $ operator_ "not" <> opParens p' -- text "¬" <> parens (pp a)
    pp (Conn op p q) = do
      (vsp, (p', envp)) <- pp p
      (vsq, (q', envq)) <- pp q
      return (vsp ++ vsq, (sep [opParens p' <-> ppOp op, opParens q'], mergeEnv envp envq))
      where
        ppOp And = text "&&"
        ppOp Or = text "||"
        ppOp Imp = text "==>"
        ppOp Iff = opIff
    pp fm@(Qua {}) =
      scopeFreshness $ do
        (vs, _, fm') <- openFormulaPrefix fm
        (vsp, d') <- pp fm'
        return (vs ++ vsp, d')

isPropFormula :: LNFormula -> Bool
isPropFormula (Qua {}) = False
isPropFormula (Ato _) = True
isPropFormula (TF _) = True
isPropFormula (Not (Ato (EqE _ _))) = True
isPropFormula (Not _) = True
isPropFormula (Conn _ p q) = isPropFormula p && isPropFormula q

ppQueryFormula :: (MonadFresh m, Functor s) => TypingEnvironment -> ProtoFormula s (String, LSort) Name LVar -> [LVar] -> m Doc
ppQueryFormula te fm extravs = do
  (vs, (p, typeVars)) <- ppLFormula te ppNAtom fm
  return $
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

ppRestrictFormula :: TypingEnvironment -> ProtoFormula Unit2 (String, LSort) Name LVar -> Precise.FreshT Data.Functor.Identity.Identity Doc
ppRestrictFormula te =
  pp
  where
    pp (Not fm@(Qua Ex _ _)) = do
      (vs, _, fm') <- openFormulaPrefix fm
      return
        ( if isPropFormula fm'
            then ppOk fm' vs
            else ppFail fm
        )
    pp fm@(Qua Ex _ _) = do
      (vs, _, fm') <- openFormulaPrefix fm
      return
        ( if isPropFormula fm'
            then ppOk fm' vs
            else ppFail fm
        )
    pp fm@(Qua All _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      pp2 fm fm'
    pp fm = return $ ppFail fm
    ppOk = ppQueryFormulaEx te
    ppFail fm = text "(*" <> prettyLNFormula fm <> text "*)"

    pp2 fm_original fm | isPropFormula fm = return $ ppOk fm_original []
    pp2 fm_original (Conn Imp p fm) | isPropFormula p = do
      isExDisj <- disjunct_ex fm
      return
        ( if isExDisj
            then ppOk fm_original []
            else ppFail fm_original
        )

    -- pp2 fm_original (Conn Imp p fm@(Qua Ex _ _)) | isPropFormula p  = do
    --             (_,_,fm') <- openFormulaPrefix fm
    --             return $ (if isPropFormula fm' then
    --                         ppOk fm_original []
    --                       else
    --                         ppFail fm_original)
    -- pp2 fm_original (Conn Imp p (Conn Or fm@(Qua Ex _ _)  fm2@(Qua Ex _ _))) | isPropFormula p  = do
    --             (_,_,fm') <- openFormulaPrefix fm
    --             (_,_,fm2') <- openFormulaPrefix fm2
    --             return $ (if isPropFormula fm' && isPropFormula fm2' then
    --                         ppOk fm_original []
    --                       else
    --                         ppFail fm_original)

    pp2 fm_original _ = return $ ppFail fm_original

    disjunct_ex fm@(Qua Ex _ _) = do
      (_, _, fm') <- openFormulaPrefix fm
      return $ isPropFormula fm'
    disjunct_ex (Conn Or fm@(Qua Ex _ _) fm2) = do
      (_, _, fm') <- openFormulaPrefix fm
      b <- disjunct_ex fm2
      return $ b && isPropFormula fm'
    disjunct_ex (Conn Or fm2 fm@(Qua Ex _ _)) = do
      (_, _, fm') <- openFormulaPrefix fm
      b <- disjunct_ex fm2
      return $ b && isPropFormula fm'
    disjunct_ex _ = return False

ppLemma :: TypingEnvironment -> Lemma ProofSkeleton -> Doc
ppLemma te p =
  text "(*" <> text (L.get lName p) <> text "*)"
    $$ Precise.evalFresh (ppRestrictFormula te fm) (avoidPrecise fm)
  where
    fm = L.get lFormula p

loadLemmas :: (ProtoLemma LNFormula ProofSkeleton -> Bool) -> TranslationContext -> TypingEnvironment -> OpenTheory -> [Doc]
loadLemmas lemSel tc te thy = map (ppLemma te) proverifLemmas
  where
    thyLemmas = theoryLemmas thy
    transformWithPullnots l = case pullnots (L.get lFormula l) of
      Left fm' -> 
        translationWarning ("Lemma " ++ L.get lName l ++ "\n" ++ render (prettyLNFormula (L.get lFormula l)) ++" cannot be rewritten s.t. it has only 1 ¬, the result is:\n" ++ render (prettyLNFormula fm') ++ "!\n\n") 
        $ L.set lFormula fm' l
      Right fm' -> L.set lFormula fm' l
    proverifLemmas = map transformWithPullnots $
      filter
        ( \lem ->
            lemSel lem && case concat [ls | LemmaModule ls <- L.get lAttributes lem] of
              [] -> True
              ls -> exportModule (trans tc) `elem` ls
        )
        thyLemmas

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

-- Load the proverif headers from the OpenTheory
loadHeaders :: TranslationContext -> OpenTheory -> TypingEnvironment -> IO (S.Set ProVerifHeader)
loadHeaders tc thy typeEnv = do
  eqHeaders <- mapM (headersOfRule tc typeEnv) (S.toList sigRules)
  return $ typedHeaderOfFunSym `S.union` headerBuiltins' `S.union` foldl (flip S.union) S.empty eqHeaders `S.union` eventHeaders
  where
    sig = L.get sigpMaudeSig (L.get thySignature thy)
    -- all builtins are contained in Sapic Element
    thyBuiltins = theoryBuiltins thy
    headerBuiltins =
      foldl
        ( \y x -> case List.lookup x builtins of
            Nothing -> case x of
              "multiset"         -> translationFail "Multiset is not supported in ProVerif. If you want to model natural numbers, you can use the dedicated Tamarin builtin."
              "bilinear-pairing" -> translationFail "Bilinear pairings are not supported in ProVerif."
              _                  -> y
            Just t -> y `S.union` t
        )
        S.empty
        thyBuiltins

    -- all user declared function symbols have typinginfos
    userDeclaredFunctions = theoryFunctionTypingInfos thy
    typedHeaderOfFunSym = foldl (\y x -> headerOfFunSym x `S.union` y) S.empty userDeclaredFunctions

    -- builtin headers need to be filtered, to make sure we don't redefine a user-defined function
    headerBuiltins' = S.filter builtinFilter headerBuiltins
    builtinFilter (Fun _ name _ _ _) = any (equalName name) typedHeaderOfFunSym
    builtinFilter _ = True
    equalName name (Fun _ name' _ _ _) = name /= name'
    equalName _ _ = False

    -- events headers
    eventHeaders = M.foldrWithKey (\tag types acc -> HEvent ('e' : factTagName tag) ("(" ++ makeArgtypes types ++ ")") `S.insert` acc) S.empty (events typeEnv)
    -- generating headers for equations
    sigRules = stRules sig

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
      freesrTyped = map (\v -> (v, M.lookup v $ vars tye)) freesr
      hrule =
        Eq
          prefix
          ( "forall "
              ++ render (fsep (punctuate comma (map ppFreeTyped freesrTyped)))
              ++ ";"
          )
          ( render $
              sep
                [ nest 2 plhs,
                  text "=" <-> prhs
                ]
          )
          suffix

  return $ S.singleton hrule `S.union` lsh `S.union` rsh
  where
    ppFreeTyped (v, Nothing) = ppLVar v <> text ":bitstring"
    ppFreeTyped (v, Just s) = ppLVar v <> text ":" <> text (ppType s)

prettyProVerifHeader :: ProVerifHeader -> Doc
prettyProVerifHeader (Type s) = text "type " <> text s <> text "."
prettyProVerifHeader (HEvent s ty) = text "event " <> text s <> text ty <> text "."
prettyProVerifHeader (Table s ty) = text "table " <> text s <> text ty <> text "."
prettyProVerifHeader (Eq eqtype quant eq pub) = text eqtype <> text " " <> text quant <> text " " <> text eq <> text pub <> text "."
prettyProVerifHeader (Sym symkind name symtype []) = text symkind <> text " " <> text name <> text symtype <> text "."
prettyProVerifHeader (Sym symkind name symtype attr) = text symkind <> text " " <> text name <> text symtype <> text "[" <> fsep (punctuate comma (map text attr)) <> text "]" <> text "."
prettyProVerifHeader (Fun "" _ _ _ _) = text ""
prettyProVerifHeader (Fun fkind name _ symtype []) = text fkind <> text " " <> text name <> text symtype <> text "."
prettyProVerifHeader (Fun fkind name _ symtype attr) =
  text fkind <> text " " <> text name <> text symtype <> text "[" <> fsep (punctuate comma (map text attr)) <> text "]" <> text "."

prettyDeepSecHeader :: ProVerifHeader -> Doc
prettyDeepSecHeader (Type _) = text "" -- no types in deepsec
prettyDeepSecHeader (Eq "reduc" _ eq _) = text "reduc" <> text " " <> text eq <> text "."
prettyDeepSecHeader (Eq eqtype _ eq _) = error $ "Deepsec does not support equations ATM: " ++ eqtype ++ " " ++ eq
prettyDeepSecHeader (HEvent _ _) = text ""
prettyDeepSecHeader (Table _ _) = text ""
-- drop symtypes in symbol declarations
prettyDeepSecHeader (Sym symkind name _ []) = text symkind <> text " " <> text name <> text "."
prettyDeepSecHeader (Sym symkind name _ attr) =
  if "private" `elem` attr
    then text symkind <> text " " <> text name <> text "[private]" <> text "."
    else text symkind <> text " " <> text name <> text "."
-- only keep arity for fun declarations
prettyDeepSecHeader (Fun "" _ _ _ _) = text ""
prettyDeepSecHeader (Fun fkind name arity _ []) =
  text fkind <> text " " <> text name
    <> text "/"
    <> text (show arity)
    <> text "."
prettyDeepSecHeader (Fun fkind name arity _ attr) =
  if "private" `elem` attr
    then
      text fkind <> text " " <> text name
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
  ( -- MonadThrow m,PlainProcess
    MonadFresh m
    -- , Monoid (m (AnProcess ProcessAnnotation))
    -- ,Foldable (AnProcess ProcessAnnotation)
  ) =>
  LProcess (ProcessAnnotation LVar) ->
  m LVar
mkAttackerChannel _ = freshLVar attChanName LSortMsg

mkAttackerContext :: TranslationContext -> LProcess (ProcessAnnotation LVar) -> (TranslationContext, S.Set ProVerifHeader)
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
  _ ->  translationFail "Unexpected error -> please report with an issue on the github."

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

-- | Pulling out nots.
pullnots :: LNFormula -> Either LNFormula LNFormula
pullnots fm = if pulledNots $ pullnots' fm then Right $ pullnots' fm else Left $ pullnots' fm
  where
    pulledNots lfm = case lfm of
      (Not p) -> pulledNots' p
      _ -> False
      where
        pulledNots' lfm' = case lfm' of
          Not _         -> False
          Conn _ p q    -> pulledNots' p && pulledNots' q
          Qua _ _ p     -> pulledNots' p
          _             -> True

    pullStep fm' = case fm' of
      Conn And (Not p) (Not q)  -> Not $ p .||. q
      Conn Or (Not p) (Not q)   -> Not $ p .&&. q
      Conn Imp p (Not q)        -> Not $ p .&&. q
      Conn c p q                -> Conn c (pullStep p) (pullStep q)
      Qua All x (Not p)         -> Not $ Qua Ex x p
      Qua Ex x (Not p)          -> Not $ Qua All x p
      Qua qua x p               -> Qua qua x $ pullStep p
      Not (Not p)               -> p
      Not p                     -> Not $ pullStep p
      _                         -> fm'
    pullnots' f = if f /= pullStep f then pullnots' (pullStep f) else f