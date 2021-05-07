{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns               #-}
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
    prettyDeepSecTheory

) where

import         Term.Builtin.Rules
import         Term.SubtermRule

import         Theory
import         Theory.Sapic
import         Text.PrettyPrint.Class
import         Theory.Text.Pretty

import         Sapic.Annotation
import         Sapic.States
import         Sapic.Report
import         Sapic.Typing

import           Control.Monad.Fresh
import qualified Control.Monad.Trans.PreciseFresh as Precise

import qualified Data.Set as S
import qualified Data.Label as L
import qualified Data.Map as M
import Data.List as List

import qualified Data.ByteString.Char8 as BC
import qualified Data.Functor.Identity
import Data.Char
import Data.Data

------------------------------------------------------------------------------
-- Core Proverif Export
------------------------------------------------------------------------------

proverifTemplate :: Document d => [d] -> [d] -> d -> [d] -> [d] -> d
proverifTemplate headers queries process macroproc lemmas =
  vcat headers
  $$
  vcat queries
  $$
  vcat lemmas
  $$
  vcat macroproc
  $$
  text "process"
  $$
  nest 4 process


prettyProVerifTheory :: (OpenTheory, TypingEnvironment) -> IO (Doc)
prettyProVerifTheory (thy, typEnv) = do
  headers <- loadHeaders tc thy typEnv
  let hd = attribHeaders tc $ S.toList (filterHeaders $  base_headers `S.union` headers
                                          `S.union` prochd `S.union` macroprochd)
  return $ proverifTemplate hd queries proc macroproc lemmas
  where
    tc = emptyTC{predicates = theoryPredicates thy }
    (proc, prochd, hasBoundState) = loadProc tc thy
    base_headers = if hasBoundState then state_headers else S.empty
    queries = loadQueries thy
    lemmas = loadLemmas thy
    (macroproc, macroprochd) =
      -- if stateM is not empty, we have inlined the process calls, so we don't reoutput them
      if hasBoundState then ([text ""], S.empty) else loadMacroProc tc thy

data Translation =
   Proverif
   | DeepSec
  deriving( Ord, Eq, Typeable, Data )


data TranslationContext = TranslationContext
  { trans :: Translation,
    attackerChannel :: Maybe LVar,
    hasBoundStates :: Bool,
    hasUnboundStates :: Bool,
    predicates :: [Predicate] }
    deriving (Eq, Ord)


emptyTC :: TranslationContext
emptyTC = TranslationContext{trans = Proverif,
                              attackerChannel = Nothing,
                              hasBoundStates = False,
                              hasUnboundStates = False,
                              predicates = []}

-- Proverif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProverifHeader =
   Type String  -- type declaration
  | Sym String String String [String] -- symbol declaration, (symkind,name,type,attr)
  | Fun String String Int String [String] -- symbol declaration, (symkind,name,arity,types,attr)
  | HEvent String
  | Eq String String String -- eqtype, quantif, equation
  deriving (Ord, Show, Eq)


state_headers :: S.Set ProverifHeader
state_headers = S.fromList [
  HEvent "table tbl_states_handle(bitstring,channel).", --the table for linking states identifiers and channels
  HEvent "table tbl_locks_handle(bitstring,channel)." --the table for linking locks identifiers and channels
  ]

-- We provide a dedicated DDH builtin.
builtins :: [(String, S.Set ProverifHeader)]
builtins = map (\(x,y) -> (x, S.fromList y)) [
  ("diffie-hellman", [
      Sym "const" "g" ":bitstring" [],
      Fun "fun" "exp" 2 "(bitstring,bitstring):bitstring" [],
      Eq "equation" "forall a:bitstring,b:bitstring;" "exp( exp(g,a),b) = exp(exp(g,b),a)"
      ]
  )
  ]

-- We filter out some predefined headers that we don't want to redefine.
filterHeaders :: S.Set ProverifHeader -> S.Set ProverifHeader
filterHeaders s = S.filter (not . isForbidden) s
  where isForbidden (Fun "fun" "true" _ _ _) = True
        isForbidden (Type "bitstring") = True
        isForbidden _ = False

pairPRules :: S.Set ProverifHeader
pairPRules = S.fromList  [Eq "reduc" "forall a:bitstring,b:bitstring;" "fst((a,b))=a",
   Eq  "reduc" "forall a:bitstring,b:bitstring;" "snd((a,b))=b"]

ppPubName :: NameId -> Doc
ppPubName (NameId "zero") = text "0"
ppPubName (NameId "one") = text "1"
ppPubName (NameId t) = text t

builtins_rules :: S.Set CtxtStRule
builtins_rules = S.empty
  -- foldl S.union S.empty [pairRules, symEncRules, asymEncRules, signatureRules, locationReportRules]

-- Loader of the export functions
------------------------------------------------------------------------------
loadQueries :: Theory sig c b p SapicElement -> [Doc]
loadQueries thy = [text $ get_text (lookupExportInfo "queries" thy)]
  where get_text Nothing = ""
        get_text (Just m) = L.get eText m


------------------------------------------------------------------------------
-- Term Printers
------------------------------------------------------------------------------

ppLVar :: LVar -> Doc
ppLVar (LVar n _ 0) = text n
ppLVar (LVar n _ i) = text $ n <> "_" <> (show i)

ppUnTypeVar :: SapicLVar -> Doc
ppUnTypeVar (SapicLVar lvar  _) = ppLVar lvar

ppType :: Maybe String -> String
ppType Nothing = "bitstring"
ppType (Just s) = s


ppTypeVar :: TranslationContext -> SapicLVar -> Doc
ppTypeVar tc v@(SapicLVar lvar ty) = case trans tc of
  Proverif -> ppLVar lvar <> text ":" <> text (ppType ty)
  DeepSec -> ppUnTypeVar v

ppTypeLit :: (Show c) => TranslationContext -> Lit c SapicLVar -> Doc
ppTypeLit tc (Var v) = ppTypeVar tc v
ppTypeLit _ (Con c) = text $ show c

-- pretty print an LNTerm, collecting the constant that need to be declared
-- a boolean b allows to add types to variables (for input bindings)
-- matchVars is the set of vars that correspond to pattern matching
-- isPattern enables the pattern match printing, which adds types to variables, and = to constants.
auxppSapicTerm :: TranslationContext ->  S.Set LVar -> Bool -> SapicTerm -> (Doc, S.Set ProverifHeader)
auxppSapicTerm tc mVars isPattern t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
        Lit  (Con (Name FreshName n))             ->  (text $ show n) <> text "test"
        Lit  (Con (Name PubName n)) | isPattern   -> text "=" <> (text $ show n)
        Lit  (Con (Name PubName n))               ->  ppPubName n
        Lit  (Var (SapicLVar (lvar) _ ))
          | S.member lvar mVars                  -> text "=" <> ppLVar lvar
        Lit  v                    |    isPattern          -> ppTypeLit tc v
        Lit  (Var (SapicLVar (lvar)  _ ))  -> ppLVar lvar
        Lit  v                                    -> (text $ show v)
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> text "exp(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq _)      [t1,t2] | isPair tm    -> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq (f, _)) []                     -> text (BC.unpack f)
        FApp (NoEq (f, _)) ts                     -> ppFun f ts
        FApp (C EMap)      ts                     -> ppFun emapSymString ts
        FApp List          ts                     -> ppFun (BC.pack"LIST") ts

    ppACOp Mult  = "*"
    ppACOp Union = "+"
    ppACOp Xor   = "⊕"
    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts
    ppFun f ts =
      text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm tm =  case viewTerm tm of
        Lit  (Con (Name PubName n))               ->
          if List.elem (show n) ["g","one","zero"] then
            S.empty
          else
            S.singleton   (Sym "free" (show n) ":bitstring" [])
        Lit  (_)                                  -> S.empty
        FApp (NoEq f) [t1] | f == fstSym -> (getHdTerm t1) `S.union` pairPRules
        FApp (NoEq f) [t1] | f == sndSym -> (getHdTerm t1) `S.union` pairPRules
        FApp _ ts                     -> foldl (\x y -> x `S.union` (getHdTerm y)) S.empty ts

ppSapicTerm :: TranslationContext -> SapicTerm -> (Doc, S.Set ProverifHeader)
ppSapicTerm tc = auxppSapicTerm tc S.empty False

-- TODO: we should generalise functionality so pppSapicTerm and pppLNTerm share
-- the code they have in common
pppLNTerm :: TranslationContext -> Bool -> LNTerm -> (Doc, S.Set ProverifHeader)
pppLNTerm _ b t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
        Lit  (Con (Name FreshName n))             -> text $ show n
        Lit  (Con (Name PubName n))               -> ppPubName n
        Lit  (tm2)              | b               -> text $ show tm2 <> ":bitstring"
        Lit  (Var (lvar))                         -> ppLVar lvar
        Lit  (tm2)                                -> text $ show tm2
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
--        FApp (NoEq _)      _       | isPair tm -> ppTerms ", " 1 "(" ")" (split tm)
        FApp (NoEq _)      [t1,t2] | isPair tm    -> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq (f, _)) []                     -> text (BC.unpack f)
        FApp (NoEq (f, _)) ts                     -> ppFun f ts
        FApp (C EMap)      ts                     -> ppFun emapSymString ts
        FApp List          ts                     -> ppFun (BC.pack"LIST") ts

    ppACOp Mult  = "*"
    ppACOp Union = "+"
    ppACOp Xor   = "⊕"
    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts
    ppFun f ts =
      text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm tm =  case viewTerm tm of
        Lit  (Con (Name PubName n))               ->
          if show n=="g" then
            S.empty
          else
            S.singleton   (Sym "free" (show n) ":bitstring" [])
        Lit  (_)                                  -> S.empty
        FApp _ ts                     -> foldl (\x y -> x `S.union` (getHdTerm y)) S.empty ts

ppLNTerm :: TranslationContext -> LNTerm -> (Doc, S.Set ProverifHeader)
ppLNTerm tc = pppLNTerm tc False

-- pretty print a Fact, collecting the constant that need to be declared
ppFact :: TranslationContext -> Fact SapicTerm -> (Doc, S.Set ProverifHeader)
ppFact tc (Fact tag _ ts)
  | factTagArity tag /= length ts = sppFact ("MALFORMED-" ++ show tag) ts
  | otherwise                     = sppFact (showFactTag tag) ts
  where
    sppFact name ts2 =
      (nestShort' (name ++ "(") ")" . fsep . punctuate comma $ pts, sh)
      where (pts, shs) = unzip $ map (ppSapicTerm tc) ts2
            sh = foldl S.union S.empty shs

-- pretty print an Action, collecting the constant and events that need to be declared. It also returns a boolean, specifying if the printout can serve as the end of a process or not.
ppAction ::  ProcessAnnotation LVar -> TranslationContext -> LSapicAction -> (Doc, S.Set ProverifHeader, Bool)
ppAction ProcessAnnotation{isStateChannel = Nothing} tc (New v) =
   (text "new " <> (ppTypeVar tc v), S.empty, True)

ppAction ProcessAnnotation{pureState=False, isStateChannel = Just t} tc (New v@(SapicLVar lvar _ )) =
     (extras $
       text "new " <> channel <> text "[assumeCell];"
       $$ text "new lock_" <> channel <> text "[assumeCell];"
     -- we also declare the corresponding lock channel, and initialize it
       $$ text "out(lock_" <> ppLVar lvar <> text ",0)"
     ,  if hasUnboundStates tc then sht else S.empty, True)
  where channel = ppTypeVar tc v
        (pt, sht) = ppSapicTerm tc t
        extras x = if hasUnboundStates tc then x
          $$ text "insert tbl_states_handle(" <> pt <> text", " <> ppLVar lvar <> text ");"
          $$ text "insert tbl_locks_handle(" <> pt <> text", lock_" <> ppLVar lvar <> text ");"
          else x

ppAction ProcessAnnotation{pureState=True, isStateChannel = Just _} tc (New v) =
     (text "new " <> (ppTypeVar tc v) <> text "[assumeCell]"
     , S.empty, True)

ppAction _ TranslationContext{trans=Proverif} Rep  = (text "!", S.empty, False)
ppAction _ TranslationContext{trans=DeepSec} Rep  = (text "", S.empty, False)

ppAction _ tc@TranslationContext{trans=Proverif} (ChIn t1 t2 mvars)  = (text "in(" <> pt1 <> text "," <> pt2 <> text ")"
                                       , sh1 `S.union` sh2, True)
  where (pt1, sh1) = getAttackerChannel tc t1
        (pt2, sh2) = auxppSapicTerm tc (S.map toLVar mvars) True t2

ppAction _ tc@TranslationContext{trans=DeepSec} (ChIn t1 t2@(LIT (Var (SapicLVar _ _))) mvars )  = (text "in(" <> pt1 <> text "," <> pt2 <> text ")"
                                       , sh1 `S.union` sh2, True)
  where (pt1, sh1) =  getAttackerChannel tc t1
        (pt2, sh2) = auxppSapicTerm tc (S.map toLVar mvars) True t2

-- pattern matching on input for deepsec is not supported
ppAction _ tc@TranslationContext{trans=DeepSec} (ChIn t1 t2 mvars)  = (text "in(" <> pt1 <> text "," <> text pt2var <> text ");"
                                  $$ text  "let (" <> pt2 <> text ")=" <> text pt2var <> text " in"
                                       , sh1 `S.union` sh2, False)
  where (pt1, sh1) =  getAttackerChannel tc t1
        (pt2, sh2) = auxppSapicTerm tc (S.map toLVar mvars) True t2
        pt2var = "fresh" ++ stripNonAlphanumerical (render pt2)

ppAction _ tc (ChOut t1 t2 )  = (text "out(" <> pt1 <> text "," <> pt2 <> text ")", sh1 `S.union` sh2, True)
  where (pt1, sh1) =  getAttackerChannel tc t1
        (pt2, sh2) = ppSapicTerm tc t2

ppAction _ tc@TranslationContext{trans=Proverif} (Event (Fact tag m ts) )  = (text "event " <> pa, sh, True) -- event Headers are definde globally inside loadHeaders
  where (pa, sh) = ppFact tc (Fact tag m ts)

ppAction _ TranslationContext{trans=DeepSec} (Event _ )  = (text "Unsupported event", S.empty, True)


-- For pure states, we do not put locks and unlocks
ppAction ProcessAnnotation{pureState=True} TranslationContext{trans=Proverif} (Lock _) =
    (text "", S.empty, False)

-- If there is a state channel, we simply use it
ppAction ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=False} TranslationContext{trans=Proverif} (Lock _) =
  (text "in(lock_" <> ppLVar lvar <> text "," <>  text "counterlock" <> ppLVar lvar <> text ":nat)"
                              , S.empty, True)

-- If there is no state channel, we must use the table
ppAction ProcessAnnotation{stateChannel = Nothing, pureState=False} tc@TranslationContext{trans=Proverif} (Lock t) =
    (text "get tbl_locks_handle(" <> pt <> text "," <> text ptvar <> text ") in"
     $$ text "in(" <> text ptvar <> text" , counter" <> text ptvar <> text ":nat)", sh, True)
  where
    freevars = S.fromList $  map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = auxppSapicTerm tc freevars True t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)

ppAction ProcessAnnotation{pureState=True} TranslationContext{trans=Proverif} (Unlock _) =
    (text "", S.empty, False)
ppAction ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=False} TranslationContext{trans=Proverif} (Unlock _) =
  (text "out(lock_" <> ppLVar lvar <> text "," <>  text "counterlock" <> ppLVar lvar <> text "+1" <> text ")"
  , S.empty, True)

ppAction ProcessAnnotation{stateChannel = Nothing, pureState=False} tc@TranslationContext{trans=Proverif} (Unlock t) =
    (text "out(" <> text ptvar <> text" , counter" <> text ptvar <> text "+1)", sh, True)
  where
    (pt, sh) = ppSapicTerm tc t
    ptvar = "lock_" ++ stripNonAlphanumerical (render pt)

ppAction ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=True} tc@TranslationContext{trans=Proverif} (Insert _ c) =
      (text "out(" <> ppLVar lvar <> text ", " <> pc <> text ")"
      , shc, True)
  where
    (pc, shc) = ppSapicTerm tc c

-- Should never happen
ppAction ProcessAnnotation{stateChannel = Nothing, pureState=True} TranslationContext{trans=Proverif} (Insert _ _) =
  (text "TRANSLATIONERROR", S.empty, True)

ppAction ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=False} tc@TranslationContext{trans=Proverif} (Insert _ c) =
      (text "in(" <> pt <> text ", " <> pt <> text "_dump:bitstring);"
       $$ text "out(" <> pt <> text ", " <> pc <> text ")"
      , shc, True)
  where
    pt = ppLVar lvar
    (pc, shc) = ppSapicTerm tc c

-- must rely on the table
ppAction ProcessAnnotation{stateChannel = Nothing, pureState=False} tc@TranslationContext{trans=Proverif} (Insert t t2) =
    (text "in(" <> text ptvar <> text ", " <> pt <> text "_dump:bitstring);"
     $$ text "out(" <> text ptvar <> text" , " <> pt2 <> text ")", sh `S.union` sh2, True)
  where
    (pt, sh) = ppSapicTerm tc t
    (pt2, sh2) = ppSapicTerm tc t2
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)


ppAction _  _ _  = (text "Action not supported for translation", S.empty, True)

ppSapic :: TranslationContext -> LProcess (ProcessAnnotation LVar) -> (Doc, S.Set ProverifHeader)
ppSapic _ (ProcessNull _) = (text "0", S.empty) -- remove zeros when not needed
ppSapic tc (ProcessComb Parallel _ pl pr)  = ( (nest 2 (parens ppl)) $$ text "|" $$ (nest 2 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
ppSapic tc (ProcessComb NDC _ pl pr)  = ( (nest 4 (parens ppl)) $$ text "+" <> (nest 4 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
ppSapic tc (ProcessComb (Let t1 t2 mvars) _ pl (ProcessNull _))  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                               ,sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (pt1, sh1) = auxppSapicTerm tc (S.map toLVar mvars) True t1
                                           (pt2, sh2) = ppSapicTerm tc t2

ppSapic tc (ProcessComb (Let t1 t2 mvars) _ pl pr)  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                                 $$ text "else" <> ppr
                                               ,sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
                                           (pt1, sh1) = auxppSapicTerm tc (S.map toLVar mvars) True t1
                                           (pt2, sh2) = ppSapicTerm tc t2

-- if the process call does not have any argument, we just inline
ppSapic tc (ProcessComb (ProcessCall _ _ []) _ pl _)  =   (ppl, pshl)
                                     where (ppl, pshl) = ppSapic tc pl

-- if there are state or lock channels created by addStateChannels, we must inline
ppSapic tc@TranslationContext{hasBoundStates = True} (ProcessComb (ProcessCall _ _ _) _ pl _)  =
   (ppl, pshl)
  where (ppl, pshl) = ppSapic tc pl

ppSapic tc (ProcessComb (ProcessCall name _ ts) _ _ _)  =
      (text name <>
       parens (fsep (punctuate comma ppts ))
      ,
       foldl S.union S.empty shs)
  where pts = map (ppSapicTerm tc) ts
        (ppts, shs) = unzip pts

ppSapic tc (ProcessComb (Cond a)  _ pl pr)  =
 addElseBranch ( text "if " <> pa <> text " then" $$ (nest 4 (parens ppl)), sh `S.union` pshl)
  where (ppl, pshl) = ppSapic tc pl
        (pa, sh) = ppFact' a
        ppFact' (Ato (Syntactic (Pred (Fact (ProtoFact _ "Smaller" _) _ [v1, v2 ]))))
          | Lit (Var (Free vn1)) <- viewTerm v1,
            Lit (Var (Free vn2)) <- viewTerm v2 = (text $ show vn1 <> "<" <> show vn2, S.empty )
        ppFact' p =
          case expandFormula (predicates tc) (toLFormula p) of
            Left _ -> (text "undefined predicate in condition ", S.empty )
            Right form -> (snd $ Precise.evalFresh (ppLFormula ppNAtom form) (avoidPrecise form) , S.empty)
        addElseBranch (d, s) = case pr of
          ProcessNull _ -> (d, s)
          _ -> let (ppr, pshr) = ppSapic tc pr in
            (d $$ text "else"  $$ (nest 4 (parens ppr)) , s `S.union` pshr)

ppSapic tc (ProcessComb (CondEq t1 t2)  _ pl (ProcessNull _))  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) , sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (pt1, sh1) = ppSapicTerm tc t1
                                           (pt2, sh2) = ppSapicTerm tc t2


ppSapic tc (ProcessComb (CondEq t1 t2)  _ pl pr)  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) $$ text "else" <> (nest 4 (parens ppr)), sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
                                           (pt1, sh1) = ppSapicTerm tc t1
                                           (pt2, sh2) = ppSapicTerm tc t2

ppSapic tc (ProcessComb (Lookup _ c ) ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=True} pl (ProcessNull _))  =
  (text "in(" <> pt <> text ", " <> pc  <> text ");" $$ ppl
                                                      , pshl)
  where
        pt = ppLVar lvar
        pc = ppTypeVar tc c
        (ppl, pshl) = ppSapic tc pl

-- Should never happen
ppSapic _ (ProcessComb (Lookup _ _ ) ProcessAnnotation{stateChannel = Nothing, pureState=True} _ (ProcessNull _))  =
  (text "TRANSLATIONERROR", S.empty)


ppSapic tc (ProcessComb (Lookup _ c ) ProcessAnnotation{stateChannel = Just (AnVar lvar), pureState=False} pl (ProcessNull _)) =
  (text "in(" <> pt <> text ", " <> pc  <> text ");"
   $$ text "out(" <> pt <> text ", " <> pc2  <> text ");"
   $$ ppl
       , pshl)
  where
        pt = ppLVar lvar
        pc = ppTypeVar tc c
        pc2 = ppUnTypeVar c
        (ppl, pshl) = ppSapic tc pl

ppSapic tc (ProcessComb (Lookup t c ) ProcessAnnotation{stateChannel = Nothing, pureState=False} pl (ProcessNull _)) =
      (text "get tbl_states_handle(" <> pt <> text "," <> text ptvar <> text ") in"
     $$ text "in(" <> text ptvar <> text" , " <> pc <> text ");"
     $$ text "out(" <> text ptvar <> text" , " <> pc2 <> text ");"
     $$ ppl
    , sh `S.union` pshl)
  where
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    freevars = S.fromList $  map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = auxppSapicTerm tc freevars True t
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    (ppl, pshl) = ppSapic tc pl


ppSapic tc (ProcessComb (Lookup t c ) ProcessAnnotation{stateChannel = Nothing, pureState=False} pl pr) =
    (text "get tbl_states_handle(" <> pt <> text "," <> text ptvar <> text ") in"
     $$ (nest 4 (parens (
      text "in(" <> text ptvar <> text" , " <> pc <> text ");"
     $$ text "out(" <> text ptvar <> text" , " <> pc2 <> text ");"
     $$ ppl)))
     $$ text "else"
     $$ (nest 4 (parens (
                    text "new " <> text ptvar <> text ":channel [assumeCell];" --the cell did not exists, we create it !
                    $$ text "insert tbl_states_handle(" <> pt' <> text", " <> text ptvar <> text ");"
                    $$ text "out(" <> text ptvar <> text ",0);"
                    $$ ppr
                    )))
    , sh `S.union` pshl `S.union` pshr)
  where
    pc = ppTypeVar tc c
    pc2 = ppUnTypeVar c
    freevars = S.fromList $  map (\(SapicLVar lvar _) -> lvar) $ freesSapicTerm t
    (pt, sh) = auxppSapicTerm tc freevars True t
    (pt', _) = ppSapicTerm tc t
    ptvar = "stateChannel" ++ stripNonAlphanumerical (render pt)
    (ppl, pshl) = ppSapic tc pl
    (ppr, pshr) = ppSapic tc pr

ppSapic _ (ProcessComb (Lookup _ _ ) _ _ _) =
  (text "TRANSLATION ERROR, lookup with else branch unsupported", S.empty)


ppSapic tc@TranslationContext{trans=Proverif} (ProcessAction Rep _ p)  = (text "!" $$ parens pp, psh)
                                   where (pp, psh) = ppSapic tc p
ppSapic tc@TranslationContext{trans=DeepSec} (ProcessAction Rep _ p)  = (text "" <> parens pp, psh)
                                   where (pp, psh) = ppSapic tc p
ppSapic tc  (ProcessAction a an (ProcessNull _))  = if unNeedZero then (pa, sh)
                                                    else (pa <> text "0", sh)
                                     where (pa, sh, unNeedZero) = ppAction an tc a
ppSapic tc  (ProcessAction a an p)  = if needSep then  (pa <> text ";" $$ pp , sh `S.union` psh)
                                      else  (pa $$ pp , sh `S.union` psh)
                                     where (pa, sh, needSep) = ppAction an tc a
                                           (pp, psh) = ppSapic tc p

addAttackerReportProc :: TranslationContext -> OpenTheory -> Doc -> Doc
addAttackerReportProc tc thy p =
  text "(" $$ p $$ text ")| in(" <> att <> text ",(x:bitstring,y:bitstring)); if " <> formula <> text " then out(" <> att  <> text ", rep(x,y))"
  where att = fst $ getAttackerChannel tc Nothing
        reportPreds = List.find (\(Predicate (Fact tag _ _) _) -> showFactTag tag == "Report")
          $ theoryPredicates thy
        (_,formula) = case reportPreds of
                     Nothing -> ([], text "Translation Error, no Report predicate provided")
                     Just (Predicate _ form) -> Precise.evalFresh (ppLFormula ppNAtom form) (avoidPrecise form)

loadProc :: TranslationContext -> OpenTheory -> (Doc, S.Set ProverifHeader, Bool)
loadProc tc thy = case theoryProcesses thy of
  []  -> (text "", S.empty, False)
  [pr] -> let (d,headers) = ppSapic tc2 p in
          let finald =
                  if (List.find (\x -> x=="locations-report") $ theoryBuiltins thy) == Nothing
                  then d
                  else addAttackerReportProc tc2 thy d
          in
           (finald,S.union hd headers, fst hasStates)

   where p = makeAnnotations thy pr
         hasStates =  hasBoundUnboundStates p
         (tc2, hd) = mkAttackerContext tc{hasBoundStates = fst hasStates, hasUnboundStates = snd hasStates} p
  _  -> (text "Multiple sapic processes detected, error", S.empty, False)


loadMacroProc :: TranslationContext -> OpenTheory -> ([Doc], S.Set ProverifHeader)
loadMacroProc tc thy = loadMacroProcs tc thy (theoryProcessDefs thy)

loadMacroProcs :: TranslationContext -> OpenTheory -> [ProcessDef] ->  ([Doc], S.Set ProverifHeader)
loadMacroProcs _ _ [] = ([text ""], S.empty)
loadMacroProcs tc thy (p:q) =
      let (docs,  heads) = loadMacroProcs tc3 thy q in
        case L.get pVars p of
          [] -> (docs, hd `S.union` heads)
          pvars ->
            let (new_text, new_heads) = ppSapic tc3 mainProc in
            let vrs  = text "(" <> (fsep (punctuate comma (map (ppTypeVar tc3) pvars ))) <> text ")"in
             let macro_def = text "let " <> (text $ L.get pName p) <> vrs <> text "=" $$
                             (nest 4 new_text) <> text "." in
               (macro_def : docs, hd `S.union` new_heads `S.union` heads)
  where
    mainProc = makeAnnotations thy $ L.get pBody p
    hasStates = hasBoundUnboundStates mainProc
    (tc2,hd) = case attackerChannel tc of
          -- we set up the attacker channel if it does not already exists
          Nothing -> mkAttackerContext tc mainProc
          Just _ -> (tc, S.empty)
    tc3 = tc2{hasBoundStates = fst hasStates, hasUnboundStates = snd hasStates}

------------------------------------------------------------------------------
-- Printer for Lemmas
------------------------------------------------------------------------------


showFactAnnotation :: FactAnnotation -> [Char]
showFactAnnotation an = case an of
    SolveFirst     -> "+"
    SolveLast      -> "-"
    NoSources      -> "no_precomp"

ppProtoAtom :: (HighlightDocument d, Show a) =>  (s a -> d) -> (a -> d) -> ProtoAtom s a -> d
ppProtoAtom _ ppT  (Action v (Fact tag an ts))
  | factTagArity tag /= length ts = ppFactL ("MALFORMED-" ++ show tag) ts <> ppAnn an
  | tag == KUFact = ppFactL ("attacker") ts <> ppAnn an  <> opAction <> ppT v
  | otherwise                     =
        text "event(" <> ppFactL (showFactTag tag) ts <> text ")" <> ppAnn an  <> opAction <> ppT v
  where
    ppFactL n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppT t
    ppAnn ann = if S.null ann then text "" else
        brackets . fsep . punctuate comma $ map (text . showFactAnnotation) $ S.toList ann


ppProtoAtom ppS _ (Syntactic s) = ppS s
ppProtoAtom _ ppT (EqE l r) =
    sep [ppT l <-> opEqual, ppT r]

    -- sep [ppNTerm l <-> text "≈", ppNTerm r]
ppProtoAtom _ ppT (Less u v) = ppT u <-> opLess <-> ppT v
ppProtoAtom _ _ (Last i)   = operator_ "last" <> parens (text (show i))


ppAtom :: (LNTerm -> Doc) -> ProtoAtom s LNTerm -> Doc
ppAtom = ppProtoAtom (const emptyDoc)

-- only used for Proverif queries display
-- the Bool is set to False when we must negate the atom
ppNAtom :: ProtoAtom s LNTerm -> Doc
ppNAtom = ppAtom (fst . (ppLNTerm emptyTC))

mapLits :: (Ord a, Ord b) => (a -> b) -> Term a -> Term b
mapLits f t = case viewTerm t of
    Lit l     -> lit . f $ l
    FApp o as -> fApp o (map (mapLits f) as)

ppLFormula :: (MonadFresh m, Ord c, HighlightDocument b, Functor syn) => (ProtoAtom syn (Term (Lit c LVar)) -> b) -> ProtoFormula syn (String, LSort) c LVar -> m ([LVar], b)
ppLFormula ppAt =
    pp
  where
    extractFree (Free v)  = v
    extractFree (Bound i) = error $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

    pp (Ato a)    = return ([],  ppAt (fmap (mapLits (fmap extractFree)) a))
    pp (TF True)  = return ([], operator_ "true")    -- "T"
    pp (TF False) = return ([], operator_ "false")    -- "F"

    pp (Not p)    = do
      (vs,p') <- pp p
      return (vs, operator_ "not" <> opParens p') -- text "¬" <> parens (pp a)
      -- return $ operator_ "not" <> opParens p' -- text "¬" <> parens (pp a)

    pp (Conn op p q) = do
        (vsp,p') <- pp p
        (vsq,q') <- pp q
        return (vsp ++ vsq, sep [opParens p' <-> ppOp op, opParens q'])
      where
        ppOp And = text "&&"
        ppOp Or  = text "||"
        ppOp Imp = text "==>"
        ppOp Iff = opIff

    pp fm@(Qua _ _ _) =
        scopeFreshness $ do
            (vs, _, fm') <- openFormulaPrefix fm
            (vsp,d') <- pp fm'
            return (vs++vsp,d')

isPropFormula :: LNFormula -> Bool
isPropFormula (Qua _ _ _ ) = False
isPropFormula (Ato _) = True
isPropFormula (TF _) = True
isPropFormula (Not _) = False
isPropFormula (Conn _ p q) = isPropFormula p && isPropFormula q

ppQueryFormula :: (MonadFresh m, Functor s) => ProtoFormula s (String, LSort) Name LVar -> [LVar] -> m Doc
ppQueryFormula fm extravs = do
  (vs,p) <- ppLFormula ppNAtom fm
  return $
    sep [text "query " <>  fsep (punctuate comma (map ppTimeTypeVar (extravs++vs))) <> text ";",
         nest 1 p,
         text "."]

ppTimeTypeVar :: LVar -> Doc
ppTimeTypeVar lvar@(LVar _ LSortNode _ ) = ppLVar lvar <> text ":time"
ppTimeTypeVar lvar = ppLVar lvar <> text ":bitstring"


ppQueryFormulaEx :: LNFormula -> [LVar] -> Doc
ppQueryFormulaEx fm vs =
    Precise.evalFresh (ppQueryFormula fm vs) (avoidPrecise fm)
ppRestrictFormula :: ProtoFormula Unit2 (String, LSort) Name LVar -> Precise.FreshT Data.Functor.Identity.Identity Doc
ppRestrictFormula =
  pp
  where
    pp (Not fm@(Qua Ex _ _)) = do
           (vs,_,fm') <- openFormulaPrefix fm
           return $ (if isPropFormula fm' then
                        ppOk fm' vs
                      else
                        ppFail fm)
    pp fm@(Qua All _ _) = do
                (_,_,fm') <- openFormulaPrefix fm
                pp2 fm fm'

    pp fm  =  return $ ppFail fm
    ppOk = ppQueryFormulaEx
    ppFail fm =  text "(*" <> prettyLNFormula fm <> text "*)"

    pp2 fm_original fm | isPropFormula fm = return $ ppOk fm_original []

    pp2 fm_original (Conn Imp p fm@(Qua Ex _ _)) | isPropFormula p  = do
                (_,_,fm') <- openFormulaPrefix fm
                return $ (if isPropFormula fm' then
                            ppOk fm_original []
                          else
                            ppFail fm_original)
    pp2 fm_original (Conn Imp p (Conn Or fm@(Qua Ex _ _)  fm2@(Qua Ex _ _))) | isPropFormula p  = do
                (_,_,fm') <- openFormulaPrefix fm
                (_,_,fm2') <- openFormulaPrefix fm2
                return $ (if isPropFormula fm' && isPropFormula fm2' then
                            ppOk fm_original []
                          else
                            ppFail fm_original)


    pp2 fm_original _ = return $ ppFail fm_original

ppLemma :: Lemma ProofSkeleton -> Doc
ppLemma p = text "(*" <> text (L.get lName p) <> text "*)"
            $$ Precise.evalFresh (ppRestrictFormula fm) (avoidPrecise fm)
  where fm = L.get lFormula p

loadLemmas :: OpenTheory -> [Doc]
loadLemmas thy = map ppLemma (theoryLemmas thy)


------------------------------------------------------------------------------
-- Header Generation
------------------------------------------------------------------------------

headersOfType :: [SapicType] -> S.Set ProverifHeader
headersOfType types = S.fromList $ foldl (\y x -> case x of
                                           Nothing -> y
                                           Just s -> Type s : y) [] types
-- TODOS do not declare type bitstring

headerOfFunSym :: SapicFunSym-> S.Set ProverifHeader
headerOfFunSym  ((f,(k,pub,Constructor)),inTypes, outType) =
  Fun "fun" (BC.unpack f) k ("(" ++ (make_argtypes inTypes) ++ "):" ++ ppType outType) (priv_or_pub pub) `S.insert`  headersOfType (outType : inTypes)
  where priv_or_pub Public = []
        priv_or_pub Private =  ["private"]

headerOfFunSym _ = S.empty

-- Load the proverif headers from the OpenTheory
loadHeaders :: TranslationContext -> OpenTheory -> TypingEnvironment -> IO (S.Set ProverifHeader)
loadHeaders tc thy typeEnv = do
  eqHeaders <- mapM (headersOfRule tc typeEnv) (S.toList sigRules)
  return $ typedHeaderOfFunSym `S.union` headerBuiltins `S.union` (foldl (\acc x -> x `S.union` acc) S.empty eqHeaders) `S.union` eventHeaders
  where sig = (L.get sigpMaudeSig (L.get thySignature thy))
        -- all builtins are contained in Sapic Element
        thyBuiltins = theoryBuiltins thy
        headerBuiltins = foldl (\y x -> case List.lookup x builtins of
                                   Nothing -> y
                                   Just t -> y `S.union` t) S.empty thyBuiltins

        -- all user declared function symbols have typinginfos
        userDeclaredFunctions = theoryFunctionTypingInfos thy
        typedHeaderOfFunSym = foldl (\y x->  headerOfFunSym x `S.union` y) S.empty userDeclaredFunctions


        -- events headers
        eventHeaders = M.foldrWithKey (\tag types acc -> HEvent ("event " ++ showFactTag tag ++ "("++ make_argtypes  types ++  ").") `S.insert` acc) S.empty (events typeEnv)
        -- generating headers for equations
        sigRules = stRules sig S.\\ builtins_rules


toSapicLVar:: LVar -> SapicLVar
toSapicLVar v = SapicLVar v Nothing

toSapicTerm:: LNTerm -> SapicTerm
toSapicTerm = fmap f
    where
        f (Con c) = Con c
        f (Var v) = Var $ toSapicLVar v

headersOfRule :: TranslationContext -> TypingEnvironment -> CtxtStRule -> IO (S.Set ProverifHeader)
headersOfRule tc typeEnv r |  (lhs `RRule` rhs) <- ctxtStRuleToRRule r = do
   tye <- typeTermsWithEnv typeEnv (map toSapicTerm [lhs, rhs])
   let (plhs,lsh) = ppLNTerm tc lhs
       (prhs,rsh) = ppLNTerm tc rhs
       prefix = case viewTerm lhs of
            FApp (NoEq (_, (_,_,Destructor))) _ -> "reduc"
            _ -> "equation"
       freesr = List.union (frees lhs) (frees rhs)
       freesrTyped = map (\v -> (v, M.lookup v $ vars tye)) freesr
       hrule = Eq  prefix  ("forall " ++
                             render (fsep (punctuate comma (map ppFreeTyped freesrTyped)))
                       ++
                       ";")
                       (render $ sep [ nest 2 $ plhs
                           , text "=" <-> prhs ])

   return $ (S.singleton hrule)  `S.union` lsh `S.union` rsh
     where
       ppFreeTyped (v, Nothing) = ppLVar v <> text ":bitstring"
       ppFreeTyped (v, Just s) = ppLVar v <> text ":" <> text (ppType s)




prettyProverifHeader :: ProverifHeader -> Doc
prettyProverifHeader (Type s) = text "type " <> text s <> text "."
prettyProverifHeader (HEvent s) = text s
prettyProverifHeader (Eq eqtype quant eq) = text eqtype <> text " " <> text quant <>  text " " <> text eq <>  text "."
prettyProverifHeader (Sym symkind name symtype []) = text symkind <> text " " <> text name <> text symtype  <> text "."
prettyProverifHeader (Sym symkind name symtype attr) = text symkind <> text " " <> text name <> text symtype <> text "[" <> fsep (punctuate comma (map text attr)) <> text "]"  <> text "."

prettyProverifHeader  (Fun "" _ _ _ _ ) = text ""
prettyProverifHeader (Fun fkind name _ symtype [] ) =  text fkind <> text " " <> text name <> text symtype  <> text "."
prettyProverifHeader (Fun fkind name _ symtype attr ) =
   text fkind <> text " " <> text name <> text symtype <> text "[" <> fsep (punctuate comma (map text attr)) <> text "]"  <> text "."

prettyDeepSecHeader :: ProverifHeader -> Doc
prettyDeepSecHeader (Type _) = text "" -- no types in deepsec
prettyDeepSecHeader (Eq eqtype _ eq) = text eqtype <> text " " <> text eq <>  text "."
prettyDeepSecHeader (HEvent _) = text ""
-- drop symtypes in symbol declarations
prettyDeepSecHeader (Sym symkind name _ []) = text symkind <> text " " <> text name <> text "."
prettyDeepSecHeader (Sym symkind name _ attr) =
  if List.elem "private" attr then
    text symkind <> text " " <> text name <> text "[private]"  <> text "."
  else
    text symkind <> text " " <> text name  <> text "."

  -- only keep arity for fun declarations
prettyDeepSecHeader  (Fun "" _ _ _ _ ) = text ""
prettyDeepSecHeader  (Fun fkind name arity _ [] ) =  text fkind <> text " " <> text name
  <> text "/"  <> text (show arity)  <> text "."

prettyDeepSecHeader  (Fun fkind name arity _ attr ) =
  if List.elem "private" attr then
    text fkind <> text " " <> text name
    <> text "/" <> text (show arity) <> text "[private]"  <> text "."
  else
    text fkind <> text " " <> text name <> text "/" <> text (show arity)  <> text "."



attribHeaders :: TranslationContext -> [ProverifHeader] -> [Doc]
attribHeaders tc hd =
  sym ++ fun ++ eq
  where (eq,fun,sym) = splitHeaders hd
        pph = case trans tc of
          Proverif -> prettyProverifHeader
          DeepSec -> prettyDeepSecHeader
        splitHeaders [] = ([],[],[])
        splitHeaders (x:xs)
          | Sym _ _ _ _ <- x = (e1,f1,(pph x):s1)
          | Fun _ _ _ _ _<- x =  (e1,(pph x):f1,s1)
          | Eq _ _ _ <- x =  ((pph x):e1,f1,s1)
          | HEvent _ <- x =  ((pph x):e1,f1,s1)
          | Type _ <- x = (e1,f1,(pph x):s1)
          where (e1,f1,s1) = splitHeaders xs


mkAttackerChannel :: (-- MonadThrow m,PlainProcess
                   MonadFresh m
                 -- , Monoid (m (AnProcess ProcessAnnotation))
                  -- ,Foldable (AnProcess ProcessAnnotation)
                )
                    => LProcess (ProcessAnnotation LVar) -> m LVar
mkAttackerChannel _ = (freshLVar "att" LSortMsg)

mkAttackerContext :: TranslationContext -> LProcess (ProcessAnnotation LVar) -> (TranslationContext, S.Set ProverifHeader)
mkAttackerContext tc p =
  (tc{attackerChannel = Just attackerVar}, S.singleton hd)
  where
    attackerVar@(LVar n _ _)  = (evalFresh (mkAttackerChannel p) 0)
    hd =  (Sym "free" n ":channel" [])


-- given an optional channel name and a translation context, returns the corresponding printer
getAttackerChannel :: TranslationContext
                   -> Maybe SapicTerm -> (Doc, S.Set ProverifHeader)
getAttackerChannel tc t1 =  case (t1, attackerChannel tc) of
          (Just tt1, _) -> ppSapicTerm tc tt1
          (Nothing, Just (LVar n _ _ )) ->  (text n,S.empty)
          _ -> (text "TRANSLATION ERROR", S.empty)

------------------------------------------------------------------------------
-- Some utility functions
------------------------------------------------------------------------------

make_argtypes :: [SapicType] -> String
make_argtypes [] = ""
make_argtypes [x] = ppType x
make_argtypes (x:t) = ppType x ++ "," ++ (make_argtypes t)

stripNonAlphanumerical :: [Char] -> [Char]
stripNonAlphanumerical = filter (\x -> isAlpha x)

-- return the annotated process
makeAnnotations :: OpenTheory -> PlainProcess -> LProcess (ProcessAnnotation LVar)
makeAnnotations thy p = res
  where p' = report $ toAnProcess p
        res = annotatePureStates p'
        report pr = if (List.find (\x -> x=="locations-report") $ theoryBuiltins thy) == Nothing then
                     pr
                   else
                     translateTermsReport pr
------------------------------------------------------------------------------
-- Core DeepSec Export
------------------------------------------------------------------------------

deepsecTemplate :: Document d => [d] -> [d] ->  [d]  -> d
deepsecTemplate headers macroproc requests =
  vcat headers
  $$
  vcat macroproc
  $$
  vcat requests

prettyDeepSecTheory :: OpenTheory -> IO (Doc)
prettyDeepSecTheory thy = do
  headers <- loadHeaders tc thy emptyEnv
  let hd = attribHeaders tc $ S.toList (headers
                                       `S.union` macroprochd)
  return $ deepsecTemplate hd macroproc requests
  where
        tc = emptyTC{trans = DeepSec}
        emptyEnv = TypingEnvironment {vars = M.empty, events = M.empty, funs = M.empty}
        requests = loadRequests thy
        (macroproc, macroprochd) = loadMacroProc tc thy

        -- Loader of the export functions
------------------------------------------------------------------------------
loadRequests :: Theory sig c b p SapicElement -> [Doc]
loadRequests thy = [text $ get_text (lookupExportInfo "requests" thy)]
  where get_text Nothing = ""
        get_text (Just m) = L.get eText m
