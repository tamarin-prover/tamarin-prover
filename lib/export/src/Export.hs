{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}
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

import         Term.Builtin.Signature
import         Term.Builtin.Rules
import         Term.SubtermRule


import         Theory
import         Theory.Sapic
import         Text.PrettyPrint.Class
import           Theory.Text.Pretty

import           Control.Monad.Fresh
import qualified Control.Monad.Trans.PreciseFresh as Precise

import qualified Data.Set as S
import qualified Data.Label as L
import Data.List as List
import qualified Data.Map as M
import qualified Data.ByteString.Char8 as BC
import qualified Data.Functor.Identity
import Data.Char
import Data.Data

import States

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


prettyProVerifTheory :: OpenTheory -> Doc
prettyProVerifTheory thy =  proverifTemplate hd queries proc macroproc lemmas
  where
    tc = TranslationContext {trans = Proverif,
                             attackerChannel = Nothing,
                             stateMap = M.empty,
                             pureStates = S.empty}
    hd = attribHeaders tc $ S.toList (base_headers `S.union` (loadHeaders tc thy)
                                       `S.union` prochd `S.union` macroprochd)
    (proc, prochd, stateM) = loadProc tc thy
    queries = loadQueries thy
    lemmas = loadLemmas thy
    (macroproc, macroprochd) =
      -- if stateM is not empty, we have inlined the process calls, so we don't reoutput them
      if stateM == M.empty then loadMacroProc tc thy else ([text ""], S.empty)

data Translation =
   Proverif
   | DeepSec
  deriving( Ord, Eq, Typeable, Data )


data TranslationContext = TranslationContext
  { trans :: Translation,
    attackerChannel :: Maybe LVar,
    stateMap :: StateMap,
    pureStates :: S.Set SapicTerm
  }
    deriving (Eq, Ord, Data)

-- Proverif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProverifHeader =
   Type String  -- type declaration
  | Sym String String String [String] -- symbol declaration, (symkind,name,type,attr)
  | Fun String String Int String [String] -- symbol declaration, (symkind,name,arity,types,attr)
  | HEvent String
  | Eq String String String -- eqtype, quantif, equation
  -- | Type String -- will  be used to define types
  deriving (Ord, Show, Eq)

-- We declare some base headers. Notably, we need a dedicated attacker channel.
base_headers :: S.Set ProverifHeader
base_headers = S.fromList [
  Fun "fun" "flock" 1 "(bitstring):channel" ["private"],
  Fun "fun" "fcell" 1 "(bitstring):channel" ["private"],
  HEvent "event Lock(bitstring).",
  HEvent "event Unlock(bitstring).",
  HEvent "event CellRead(bitstring).",
  HEvent "event CellWrite(bitstring)."
  ]

-- The corresponding headers for each Tamarin builtin. If the functions of the builtin are inside the signature, we add the corresponding headers to the output.
builtins :: [(NoEqFunSig, S.Set ProverifHeader)]
builtins = map (\(x,y) -> (x, S.fromList y)) [
  (hashFunSig, [Fun "fun" "hash" 1 "(bitstring):bitstring" []] ),
  (signatureFunSig, [
      Fun "fun" "sign" 2 "(bitstring,skey):bitstring" [],
      Type "pkey",
      Fun "fun" "pk" 1 "(skey):pkey" [],
      Eq "reduc" "forall m:bitstring,sk:skey;" "verify(sign(m,sk),m,pk(sk)) = true"
      ]
  ),
  (S.fromList [expSym], [
      Sym "const" "g" ":bitstring" [],
      Fun "fun" "exp" 2 "(bitstring,bitstring):bitstring" [],
      Eq "equation" "forall a:bitstring,b:bitstring;" "exp( exp(g,a),b) = exp(exp(g,b),a)"
      ]
  ),
  (symEncFunSig, [
      Type "skey",
      Fun "fun" "senc" 2 "(bitstring,skey):bitstring" [],
      Eq "reduc" "forall m:bitstring,sk:skey;" "sdec(senc(m,sk),sk) = m"]
  ),
  -- (pairFunSig,  [Eq "reduc" "forall a:bitstring,b:bitstring;" "fst((a,b))=a",
  -- Eq  "reduc" "forall a:bitstring,b:bitstring;" "snd((a,b))=b"]
  -- ),
  (asymEncFunSig, [
      Type "skey",
      Type "pkey",
      Fun "fun" "aenc" 2 "(bitstring,pkey):bitstring" [],
      Fun "fun" "pk" 1 "(skey):pkey" [],
      Eq "reduc" "forall m:bitstring,sk:skey;" "adec(aenc(m,pk(sk)),sk) = m"]
  )
  ]


ppPubName :: NameId -> Doc
ppPubName (NameId "zero") = text "0"
ppPubName (NameId "one") = text "1"
ppPubName (NameId t) = text t

builtins_rules :: S.Set CtxtStRule
builtins_rules = foldl S.union S.empty [pairRules, symEncRules, asymEncRules, signatureRules]

-- Loader of the export functions
------------------------------------------------------------------------------
loadQueries :: Theory sig c b p SapicElement -> [Doc]
loadQueries thy = [text $ get_text (lookupExportInfo "queries" thy)]
  where get_text Nothing = ""
        get_text (Just m) = L.get eText m


------------------------------------------------------------------------------
-- Term Printers
------------------------------------------------------------------------------

ppUnTypeVar :: SapicLVar -> Doc
ppUnTypeVar (SapicLVar (LVar n _ _ )  _) = text n

ppTypeVar :: TranslationContext -> SapicLVar -> Doc
ppTypeVar tc v = case trans tc of
  Proverif -> auxppTypeVar v
  DeepSec -> ppUnTypeVar v
  where auxppTypeVar (SapicLVar (LVar n _ _ )  Nothing) = text n <> text ":bitstring"
        auxppTypeVar (SapicLVar (LVar n _ _ ) (Just t)) = text n <> text ":" <> (text t)


ppTypeLit :: (Show c) => TranslationContext -> Lit c SapicLVar -> Doc
ppTypeLit tc (Var v) = ppTypeVar tc v
ppTypeLit _ (Con c) = text $ show c

-- pretty print an LNTerm, collecting the constant that need to be declared
-- a boolean b allows to add types to variables (for input bindings)
-- matchVars is the set of vars that correspond to pattern matching
-- isPattern enables the pattern match printing, which adds types to variables, and = to constants.
auxppSapicTerm :: TranslationContext ->  S.Set SapicLVar -> Bool -> SapicTerm -> (Doc, S.Set ProverifHeader)
auxppSapicTerm tc mVars isPattern t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
        Lit  (Con (Name FreshName n))             ->  (text $ show n) <> text "test"
        Lit  (Con (Name PubName n)) | isPattern   -> text "=" <> (text $ show n)
        Lit  (Con (Name PubName n))               ->  ppPubName n
        Lit  (Var v@(SapicLVar (LVar n _ _) _ ))
          | S.member v mVars                  -> text "=" <> text n
        Lit  v                    |    isPattern          -> ppTypeLit tc v
        Lit  (Var (SapicLVar (LVar n _ _)  _ ))  -> (text n)
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
        Lit  (Var (LVar tm2 _ _ ))                -> text tm2
        Lit  (tm2)                                -> text $ show tm2
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
--        FApp (NoEq _)      _       | isPair tm -> ppTerms ", " 1 "(" ")" (split tm)
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

-- pretty print an Action, collecting the constant and events that need to be declared
ppAction ::  ProcessParsedAnnotation -> TranslationContext -> LSapicAction -> (Doc, S.Set ProverifHeader)
ppAction _ tc (New v@(SapicLVar (LVar n _ _) _ )) =
 if List.elem v (M.elems $ stateMap tc) then -- the new declaration corresponds to a state channel
   if pureTerms == S.empty then
     (text "new " <> (ppTypeVar tc v) <> text "[assumeCell];"
       $$ text "new lock_" <> (ppTypeVar tc v) <> text "[assumeCell];"
     -- we also declare the corresponding lock channel, and initialize it
       $$ text "out(lock_" <> (text n) <> text ",0);"
     , S.empty)
   else
     (text "new " <> (ppTypeVar tc v) <> text "[assumeCell];"
     , S.empty)
  else
   (text "new " <> (ppTypeVar tc v) <> text ";", S.empty)
 where correspondingTerms = M.keys $ M.filter (\name -> name == v) (stateMap tc)
       pureTerms = S.fromList correspondingTerms `S.intersection`  pureStates tc

ppAction _ TranslationContext{trans=Proverif} Rep  = (text "!", S.empty)
ppAction _ TranslationContext{trans=DeepSec} Rep  = (text "", S.empty)

ppAction an tc@TranslationContext{trans=Proverif} (ChIn t1 t2 )  = (text "in(" <> pt1 <> text "," <> pt2 <> text ");"
                                       , sh1 `S.union` sh2)
  where (pt1, sh1) = getAttackerChannel tc t1
        (pt2, sh2) = auxppSapicTerm tc (matchVars an) True t2

ppAction an tc@TranslationContext{trans=DeepSec} (ChIn t1 t2@(LIT (Var (SapicLVar _ _))) )  = (text "in(" <> pt1 <> text "," <> pt2 <> text ");"
                                       , sh1 `S.union` sh2)
  where (pt1, sh1) =  getAttackerChannel tc t1
        (pt2, sh2) = auxppSapicTerm tc (matchVars an) True t2

-- pattern matching on input for deepsec is not supported
ppAction an tc@TranslationContext{trans=DeepSec} (ChIn t1 t2 )  = (text "in(" <> pt1 <> text "," <> text pt2var <> text ");"
                                  $$ text  "let (" <> pt2 <> text ")=" <> text pt2var <> text " in"
                                       , sh1 `S.union` sh2)
  where (pt1, sh1) =  getAttackerChannel tc t1
        (pt2, sh2) = auxppSapicTerm tc (matchVars an) True t2
        pt2var = "fresh" ++ stripNonAlphanumerical (render pt2)

ppAction _ tc (ChOut t1 t2 )  = (text "out(" <> pt1 <> text "," <> pt2 <> text ");", sh1 `S.union` sh2)
  where (pt1, sh1) =  getAttackerChannel tc t1
        (pt2, sh2) = ppSapicTerm tc t2

ppAction _ tc@TranslationContext{trans=Proverif} (Event (Fact tag m ts) )  = (text "event " <> pa <> text ";", sh `S.union` (S.singleton (HEvent ("event " ++ (showFactTag tag) ++ "(" ++ make_args (length ts) ++ ")."))))
  where (pa, sh) = ppFact tc (Fact tag m ts)

ppAction _ TranslationContext{trans=DeepSec} (Event _ )  = (text "", S.empty)


ppAction _ tc@TranslationContext{trans=Proverif} (Lock t) =
  if t `S.member` pureStates tc then
    (text "", S.empty)
  else
    (text "in(lock_" <> text pt <> text "," <> text ptcounter <> text ":nat);"
--                              $$ text "event Lock((" <> text pt <> text "," <> text ptcounter <> text "));"
                              , S.empty)
  where -- (pt, sh) = ppSapicTerm tc t
        pt = getStateChannel tc t
        ptcounter = "counterlock" ++ stripNonAlphanumerical pt -- improve name of counter, fresh variable and propagate the name

ppAction _ tc@TranslationContext{trans=Proverif} (Unlock t) =
  if t `S.member` pureStates tc then
    (text "", S.empty)
  else
    (
  -- text "event Unlock((" <> pt <> text "," <> text ptcounter <> text "));" $$ -- do not make event as tuple, but need to infer
                                  text "out(lock_" <> text pt <> text "," <> text ptcounter <> text ");"
                                , S.empty)
  where -- (pt, sh) = ppSapicTerm tc t
    pt = getStateChannel tc t
    ptcounter = "counterlock" ++ stripNonAlphanumerical pt ++ "+1"


ppAction _ tc@TranslationContext{trans=Proverif} (Insert t c) =
    if t `S.member` pureStates tc then
      (text "out(" <> text pt <> text ", " <> pc <> text ");"
      , shc)
  else
      (text "in(" <> text pt <> text ", " <> text pt <> text "_dump:bitstring);"
       $$ text "out(" <> text pt <> text ", " <> pc <> text ");"
      , shc)

  where
    pt = getStateChannel tc t
--    (pt, sh) = ppSapicTerm tc t
    (pc, shc) = ppSapicTerm tc c
--        ptcounter = "countercell" ++ stripNonAlphanumerical (render pt)

ppAction _  _ _  = (text "Action not supported for translation", S.empty)

ppSapic :: TranslationContext -> PlainProcess -> (Doc, S.Set ProverifHeader)
ppSapic _ (ProcessNull _) = (text "0", S.empty) -- remove zeros when not needed
ppSapic tc (ProcessComb Parallel _ pl pr)  = ( (nest 2 (parens ppl)) $$ text "|" $$ (nest 2 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
ppSapic tc (ProcessComb NDC _ pl pr)  = ( (nest 4 (parens ppl)) $$ text "+" <> (nest 4 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
ppSapic tc (ProcessComb (Let t1 t2) an pl (ProcessNull _))  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                               ,sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (pt1, sh1) = auxppSapicTerm tc (matchVars an) True t1
                                           (pt2, sh2) = ppSapicTerm tc t2

ppSapic tc (ProcessComb (Let t1 t2) an pl pr)  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                                 $$ text "else" <> ppr
                                               ,sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
                                           (pt1, sh1) = auxppSapicTerm tc (matchVars an) True t1
                                           (pt2, sh2) = ppSapicTerm tc t2

-- if the process call does not have any argument, we just inline
ppSapic tc (ProcessComb (ProcessCall _ _ []) _ pl _)  =   (ppl, pshl)
                                     where (ppl, pshl) = ppSapic tc pl

-- if there are state or lock channels created by addStateChannels, we must inline
ppSapic tc (ProcessComb (ProcessCall name _ ts) _ pl _)  =
  if stateMap tc == M.empty then
      (text name <>
       parens (fsep (punctuate comma ppts ))
      ,
       foldl S.union S.empty shs)
  else
     (ppl, pshl)
  where pts = map (ppSapicTerm tc) ts
        (ppts, shs) = unzip pts
        (ppl, pshl) = ppSapic tc pl




-- ROBERTBROKEIT: a is now a SapicFormula. A special case is a single atom with
-- syntactic sugar for predicates, but this contains BVars, which first need to
-- be translated to Vars
ppSapic tc (ProcessComb (Cond a)  _ pl _)  =
  ( text "if " <> pa <> text " then" $$ (nest 4 (parens ppl)), sh `S.union` pshl)
  where (ppl, pshl) = ppSapic tc pl
        (pa, sh) = ppFact' a
        ppFact' (Ato (Syntactic (Pred _))) = (text "non-predicate conditions not yet supported also not supported ;) ", S.empty )
                                                    --- note though that we can get a printout by converting to LNFormula, like this ppFact (toLNFormula formula)
        ppFact' _                          = (text "non-predicate conditions not yet supported", S.empty)

ppSapic tc (ProcessComb (CondEq t1 t2)  _ pl (ProcessNull _))  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) , sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (pt1, sh1) = ppSapicTerm tc t1
                                           (pt2, sh2) = ppSapicTerm tc t2

-- ROBERTBROKEIT: commented out ... isn't this clashing with the previous defiition.
-- ppSapic (ProcessComb (Cond a)  _ pl (ProcessNull _))  =
--   ( text "if" <> pa $$ (nest 4 (parens ppl)), sh `S.union` pshl)
--   where (ppl, pshl) = ppSapic pl
--         (pa , sh  ) = ppFact a

ppSapic tc (ProcessComb (CondEq t1 t2)  _ pl pr)  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) $$ text "else" <> (nest 4 (parens ppr)), sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic tc pl
                                           (ppr, pshr) = ppSapic tc pr
                                           (pt1, sh1) = ppSapicTerm tc t1
                                           (pt2, sh2) = ppSapicTerm tc t2

ppSapic tc (ProcessComb (Lookup t c )  _ pl (ProcessNull _))  =
  if t `S.member` pureStates tc then
  (text "in(" <> text pt <> text ", " <> pc  <> text ");" $$ ppl
                                                      , pshl)
  else
  (text "in(" <> text pt <> text ", " <> pc  <> text ");"
   $$ text "out(" <> text pt <> text ", " <> pc2  <> text ");"
   $$ ppl
                                                      , pshl)

  where -- (pt, sh) = ppSapicTerm tc t
        pt = getStateChannel tc t
        pc = ppTypeVar tc c
        pc2 = ppUnTypeVar c
--        ptcounter = "countercell" ++ stripNonAlphanumerical (render pt)
        (ppl, pshl) = ppSapic tc pl





ppSapic tc@TranslationContext{trans=Proverif} (ProcessAction Rep _ p)  = (text "!" $$ parens pp, psh)
                                   where (pp, psh) = ppSapic tc p
ppSapic tc@TranslationContext{trans=DeepSec} (ProcessAction Rep _ p)  = (text "" <> parens pp, psh)
                                   where (pp, psh) = ppSapic tc p
ppSapic tc  (ProcessAction a an (ProcessNull _))  = (pa <> text "0", sh)
                                     where (pa, sh) = ppAction an tc a
ppSapic tc  (ProcessAction a an p)  = (pa $$ pp , sh `S.union` psh)
                                     where (pa, sh) = ppAction an tc a
                                           (pp, psh) = ppSapic tc p

loadProc :: TranslationContext -> OpenTheory -> (Doc, S.Set ProverifHeader, StateMap)
loadProc tc thy = case theoryProcesses thy of
  []  -> (text "", S.empty, M.empty)
  [p] -> let (d,headers) = ppSapic tc3 proc in
           (d,S.union hd headers, stateM)
   where (tc2, hd) = mkAttackerContext tc p
         (proc, stateM) = addStatesChannels p
         pStates = getPureStates p (S.fromList $ M.keys stateM)
         tc3 = tc2{stateMap=stateM, pureStates = pStates}
  _  -> (text "Multiple sapic processes detected, error", S.empty, M.empty)


loadMacroProc :: TranslationContext -> OpenTheory -> ([Doc], S.Set ProverifHeader)
loadMacroProc tc thy = loadMacroProcs tc (theoryProcessDefs thy)

loadMacroProcs :: TranslationContext -> [ProcessDef] ->  ([Doc], S.Set ProverifHeader)
loadMacroProcs _ [] = ([text ""], S.empty)
loadMacroProcs tc  (p:q) =
      let (docs,  heads) = loadMacroProcs tc2 q in
        case L.get pVars p of
          [] -> (docs, hd `S.union` heads)
          pvars ->
            let (new_text, new_heads) = ppSapic tc2 (L.get pBody p) in
            let vars  = text "(" <> (fsep (punctuate comma (map (ppTypeVar tc2) pvars ))) <> text ")"in
             let macro_def = text "let " <> (text $ L.get pName p) <> vars <> text "=" $$
                             (nest 4 new_text) <> text "." in
               (macro_def : docs, hd `S.union` new_heads `S.union` heads)
  where (tc2,hd) = case attackerChannel tc of
          -- we set up the attacker channel if it does not already exists
          Nothing -> mkAttackerContext tc (L.get pBody p)
          Just _ -> (tc, S.empty)

------------------------------------------------------------------------------
-- Printer for Lemmas
------------------------------------------------------------------------------


showFactAnnotation :: FactAnnotation -> [Char]
showFactAnnotation an = case an of
    SolveFirst     -> "+"
    SolveLast      -> "-"
    NoSources      -> "no_precomp"

ppProtoAtom :: (HighlightDocument d, Show a) => (s a -> d) -> (a -> d) -> ProtoAtom s a -> d
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
ppNAtom ::  ProtoAtom s LNTerm -> Doc
ppNAtom  = ppAtom (fst . (ppLNTerm TranslationContext{trans=Proverif,
                                                      attackerChannel = Nothing,
                                                      stateMap = M.empty,
                                                      pureStates = S.empty}))

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

ppTimeTypeVar :: Document p => LVar-> p
ppTimeTypeVar (LVar n LSortNode _ ) = text n <> text ":time"
ppTimeTypeVar (LVar n _ _ ) = text n <> text ":bitstring"


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

make_fun :: (BC.ByteString, Int) -> Bool -> ProverifHeader
make_fun (f,k) ispriv = Fun "fun " (BC.unpack f) k ("(" ++ (make_args k) ++ "):bitstring") arg
 where arg = if ispriv then ["private"] else []


headerOfFunSym :: [SapicFunSym] -> NoEqSym -> ProverifHeader
headerOfFunSym []  (_,(_,_,Destructor)) = Fun "" "" 0 "" []
headerOfFunSym []  (f,(k,Public,Constructor))  =  make_fun (f,k) False
headerOfFunSym []  (f,(k,Private,Constructor)) =  make_fun (f,k) True
headerOfFunSym  (((f,(k,Public,Constructor)),inTypes,Just outType):remainder)  fs2@(f2,(k2,Public,_)) =
  if f2==f && k2 == k then
    Fun "fun " (BC.unpack f) k ("(" ++ (make_argtypes inTypes) ++ "):" ++ outType) []
  else headerOfFunSym remainder fs2
headerOfFunSym  (((f,(k,Private,Constructor)),inTypes,Just outType):remainder)  fs2@(f2,(k2,Private,_)) =
  if f2==f && k2 == k then
    Fun "fun " (BC.unpack f) k ("(" ++ (make_argtypes inTypes) ++ "):" ++ outType) ["private"]
  else headerOfFunSym remainder fs2

headerOfFunSym  (_:remainder)  fs2 =
   headerOfFunSym remainder fs2


-- Load the proverif headers from the OpenTheory
loadHeaders :: TranslationContext -> OpenTheory -> S.Set ProverifHeader
loadHeaders tc thy =
  (S.map  typedHeaderOfFunSym funSymsNoBuiltin) `S.union` funSymsBuiltins `S.union` (S.foldl (\x y -> x `S.union` (headersOfRule tc y)) S.empty sigRules)
  where sig = (L.get sigpMaudeSig (L.get thySignature thy))
        -- generating headers for function symbols, both for builtins and user defined functions
        sigFunSyms = funSyms sig
        sigStFunSyms = stFunSyms sig
        funSymsBuiltins = ((foldl (\x (y,z) -> if S.isSubsetOf (S.map NoEq y) sigFunSyms then  x `S.union` z else x )) S.empty builtins)
        funSymsNoBuiltin = sigStFunSyms S.\\ ((foldl (\x (y, _) -> x `S.union` y)) S.empty builtins)
        typedHeaderOfFunSym = headerOfFunSym (theoryFunctionTypingInfos thy)
        -- generating headers for equations
        sigRules = stRules sig S.\\ builtins_rules

headersOfRule :: TranslationContext -> CtxtStRule -> S.Set ProverifHeader
headersOfRule tc r = case ctxtStRuleToRRule r of
  (lhs `RRule` rhs) ->
    (S.singleton hrule)  `S.union` lsh `S.union` rsh
    where (plhs,lsh) = ppLNTerm tc lhs
          (prhs,rsh) = ppLNTerm tc rhs
          hrule = Eq  prefix  ("forall " ++
                       make_frees (map show freesr)  ++
                       ";")
                       (render $ sep [ nest 2 $ plhs
                           , text "=" <-> prhs ])
          freesr = List.union (frees lhs) (frees rhs)
          make_frees [] = ""
          make_frees [x] = x ++ ":bitstring"
          make_frees (x:xs) =  x ++ ":bitstring," ++ (make_frees xs)
          prefix = case viewTerm lhs of
            FApp (NoEq (_, (_,_,Destructor))) _ -> "reduc"
            _ -> "equation"




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


mkAttackerChannel :: (-- MonadThrow m,
                   MonadFresh m
                 -- , Monoid (m (AnProcess ProcessAnnotation))
                  -- ,Foldable (AnProcess ProcessAnnotation)
                )
                    => PlainProcess -> m LVar
mkAttackerChannel _ = (freshLVar "attacker" LSortMsg)

mkAttackerContext :: TranslationContext -> PlainProcess -> (TranslationContext, S.Set ProverifHeader)
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

getStateChannel :: TranslationContext -> SapicTerm -> String
getStateChannel tc t =
   case channel of
     Nothing -> "TRANSLATION ERROR"
     Just (SapicLVar (LVar channelname _ _) _) -> channelname
  where channel = M.lookup t (stateMap tc)

------------------------------------------------------------------------------
-- Some utility functions
------------------------------------------------------------------------------

make_argtypes :: [SapicType] -> String
make_argtypes [] = ""
make_argtypes [Just t] = t
make_argtypes ((Just p):t) = p ++ "," ++ (make_argtypes t)
make_argtypes _ = "Error: ill-defined type"

make_args :: Int -> String
make_args 0 = ""
make_args 1 = "bitstring"
make_args n = "bitstring,"++(make_args (n-1))


stripNonAlphanumerical :: [Char] -> [Char]
stripNonAlphanumerical = filter (\x -> isAlpha x)
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


prettyDeepSecTheory :: OpenTheory -> Doc
prettyDeepSecTheory thy =  deepsecTemplate hd macroproc requests
  where
        tc = TranslationContext{trans = DeepSec,
                                attackerChannel = Nothing,
                                stateMap = M.empty,
                                pureStates = S.empty}
        hd = attribHeaders tc $ S.toList (base_headers `S.union` (loadHeaders tc thy)
                                       `S.union` macroprochd)
        requests = loadRequests thy
        (macroproc, macroprochd) = loadMacroProc tc thy

        -- Loader of the export functions
------------------------------------------------------------------------------
loadRequests :: Theory sig c b p SapicElement -> [Doc]
loadRequests thy = [text $ get_text (lookupExportInfo "requests" thy)]
  where get_text Nothing = ""
        get_text (Just m) = L.get eText m
