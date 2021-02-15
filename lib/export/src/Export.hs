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
import qualified Data.ByteString.Char8 as BC
import qualified Data.Functor.Identity
import Data.Char

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
  where hd = attribHeaders Proverif $ S.toList (base_headers `S.union` (loadHeaders Proverif thy)
                                       `S.union` prochd `S.union` macroprochd)
        (proc, prochd) = loadProc thy
        queries = loadQueries thy
        lemmas = loadLemmas thy
        (macroproc, macroprochd) = loadMacroProc Proverif thy

data Translation =
   Proverif
   | DeepSec

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
  Sym "free" "attacker_channel" ":channel" [],
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

ppTypeVar :: Translation -> SapicLVar -> Doc
ppTypeVar trans v = case trans of
  Proverif -> auxppTypeVar v
  DeepSec -> auxppUnTypeVar v
  where auxppTypeVar (SapicLVar (LVar n _ _ )  Nothing) = text n <> text ":bitstring"
        auxppTypeVar (SapicLVar (LVar n _ _ ) (Just t)) = text n <> text ":" <> (text t)
        auxppUnTypeVar (SapicLVar (LVar n _ _ )  _) = text n


ppTypeLit :: (Show c) => Translation -> Lit c SapicLVar -> Doc
ppTypeLit trans (Var v) = ppTypeVar trans v
ppTypeLit _ (Con c) = text $ show c

-- pretty print an LNTerm, collecting the constant that need to be declared
-- a boolean b allows to add types to variables (for input bindings)
auxppSapicTerm :: Translation -> Bool -> Bool -> SapicTerm -> (Doc, S.Set ProverifHeader)
auxppSapicTerm trans b0 b t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
        Lit  (Con (Name FreshName n))             ->  (text $ show n) <> text "test"
        Lit  (Con (Name PubName n))     | b0      -> text "=" <> (text $ show n)
        Lit  (Con (Name PubName n))               ->  ppPubName n
        Lit  (Var (SapicLVar (LVar n _ _) _ )) -> text "=" <> text n ---- TODO need to handle pattern matched variables based on the new set up
        Lit  v                    |    b          -> ppTypeLit trans v
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
    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split tm                          = [tm]

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

pppSapicTerm :: Translation -> Bool -> SapicTerm -> (Doc, S.Set ProverifHeader)
pppSapicTerm trans = auxppSapicTerm trans False

ppSapicTerm :: Translation -> SapicTerm -> (Doc, S.Set ProverifHeader)
ppSapicTerm trans = pppSapicTerm trans False



-- TODO: we should generalise functionality so pppSapicTerm and pppLNTerm share
-- the code they have in common
pppLNTerm :: Translation -> Bool -> LNTerm -> (Doc, S.Set ProverifHeader)
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
    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split tm                          = [tm]

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

ppLNTerm :: Translation -> LNTerm -> (Doc, S.Set ProverifHeader)
ppLNTerm trans = pppLNTerm trans False

-- pretty print a Fact, collecting the constant that need to be declared
ppFact :: Translation -> Fact SapicTerm -> (Doc, S.Set ProverifHeader)
ppFact trans (Fact tag _ ts)
  | factTagArity tag /= length ts = sppFact ("MALFORMED-" ++ show tag) ts
  | otherwise                     = sppFact (showFactTag tag) ts
  where
    sppFact name ts2 =
      (nestShort' (name ++ "(") ")" . fsep . punctuate comma $ pts, sh)
      where (pts, shs) = unzip $ map (ppSapicTerm trans) ts2
            sh = foldl S.union S.empty shs

-- pretty print an Action, collecting the constant and events that need to be declared
ppAction :: Translation -> LSapicAction -> (Doc, S.Set ProverifHeader)
ppAction trans (New v@(SapicLVar (LVar _ _ _) _ )) = (text "new " <> (ppTypeVar trans v) <> text ";", S.empty)

ppAction Proverif Rep  = (text "!", S.empty)
ppAction DeepSec Rep  = (text "", S.empty)

ppAction Proverif (ChIn t1 t2 )  = (text "in(" <> pt1 <> text "," <> pt2 <> text ");"
                                       , sh1 `S.union` sh2)
  where (pt1, sh1) = case t1 of
          Just tt1 -> ppSapicTerm Proverif tt1
          Nothing ->  (text "attacker_channel",S.empty)
        (pt2, sh2) = auxppSapicTerm Proverif True True t2

ppAction DeepSec (ChIn t1 t2@(LIT (Var (SapicLVar _ _))) )  = (text "in(" <> pt1 <> text "," <> pt2 <> text ");"
                                       , sh1 `S.union` sh2)
  where (pt1, sh1) = case t1 of
          Just tt1 -> ppSapicTerm DeepSec tt1
          Nothing ->  (text "attacker_channel",S.empty)
        (pt2, sh2) = auxppSapicTerm DeepSec True True t2

-- pattern matching on input for deepsec is not supported
ppAction DeepSec (ChIn t1 t2 )  = (text "in(" <> pt1 <> text "," <> text pt2var <> text ");"
                                  $$ text  "let (" <> pt2 <> text ")=" <> text pt2var <> text " in"
                                       , sh1 `S.union` sh2)
  where (pt1, sh1) = case t1 of
          Just tt1 -> ppSapicTerm DeepSec tt1
          Nothing ->  (text "attacker_channel",S.empty)
        (pt2, sh2) = auxppSapicTerm DeepSec True True t2
        pt2var = "fresh" ++ stripNonAlphanumerical (render pt2)

ppAction trans (ChOut (Just t1) t2 )  = (text "out(" <> pt1 <> text "," <> pt2 <> text ");", sh1 `S.union` sh2)
  where (pt1, sh1) = ppSapicTerm trans t1
        (pt2, sh2) = ppSapicTerm trans t2
ppAction trans (ChOut Nothing t2 )  = (text "out(attacker_channel," <> pt2 <> text ");", sh2)
  where (pt2, sh2) = ppSapicTerm trans t2

ppAction Proverif (Event (Fact tag m ts) )  = (text "event " <> pa <> text ";", sh `S.union` (S.singleton (HEvent ("event " ++ (showFactTag tag) ++ "(" ++ make_args (length ts) ++ ")."))))
  where (pa, sh) = ppFact Proverif (Fact tag m ts)

ppAction DeepSec (Event _ )  = (text "", S.empty)


ppAction Proverif (Lock t) =  (text "in(flock(" <> pt <> text ")," <> text ptcounter <> text ":nat);"
                              $$ text "event Lock((" <> pt <> text "," <> text ptcounter <> text "));"
                              , sh)
  where (pt, sh) = ppSapicTerm Proverif t
        ptcounter = "counterlock" ++ stripNonAlphanumerical (render pt) -- improve name of counter, fresh variable and propagate the name

ppAction Proverif (Unlock t) =  ( text "event Unlock((" <> pt <> text "," <> text ptcounter <> text "));" -- do not make event as tuple, but need to infer
                                  $$ text "out(flock(" <> pt <> text ")," <> text ptcounter <> text ");"
                                , sh)
  where (pt, sh) = ppSapicTerm Proverif t
        ptcounter = "counterlock" ++ stripNonAlphanumerical (render pt)++ "+1"


ppAction Proverif (Insert t c) = (text "event CellWrite((" <> pt <> text "," <> pc
--                              <> text "," <> text ptcounter
                              <> text "));"
                              $$ text "out(fcell(" <> pt <> text "), " <> pc
--                                  <> text "," <> text ptcounter
                                  <> text ");"
                                , sh `S.union` shc)
  where (pt, sh) = ppSapicTerm Proverif t
        (pc, shc) = ppSapicTerm Proverif c
--        ptcounter = "countercell" ++ stripNonAlphanumerical (render pt)

ppAction _ _  = (text "Action not supported for translation", S.empty)

ppSapic :: Translation -> LProcess ann -> (Doc, S.Set ProverifHeader)
ppSapic _ (ProcessNull _) = (text "0", S.empty) -- remove zeros when not needed
ppSapic trans (ProcessComb Parallel _ pl pr)  = ( (nest 2 (parens ppl)) $$ text "|" $$ (nest 2 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic trans pl
                                           (ppr, pshr) = ppSapic trans pr
ppSapic trans (ProcessComb NDC _ pl pr)  = ( (nest 4 (parens ppl)) $$ text "+" <> (nest 4 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic trans pl
                                           (ppr, pshr) = ppSapic trans pr
ppSapic trans (ProcessComb (Let t1 t2) _ pl (ProcessNull _))  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                               ,sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic trans pl
                                           (pt1, sh1) = auxppSapicTerm trans True True t1
                                           (pt2, sh2) = ppSapicTerm trans t2

ppSapic trans (ProcessComb (Let t1 t2) _ pl pr)  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                                 $$ text "else" <> ppr
                                               ,sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic trans pl
                                           (ppr, pshr) = ppSapic trans pr
                                           (pt1, sh1) = auxppSapicTerm trans True True t1
                                           (pt2, sh2) = ppSapicTerm trans t2

ppSapic trans (ProcessComb (ProcessCall _ _ []) _ pl _)  =   (ppl, pshl)
                                     where (ppl, pshl) = ppSapic trans pl

ppSapic trans (ProcessComb (ProcessCall name _ ts) _ _ _)  = (text name <>
                                                        parens (fsep (punctuate comma ppts ))
                                                       ,
                                                       foldl S.union S.empty shs)
                                     where pts = map (ppSapicTerm trans) ts
                                           (ppts, shs) = unzip pts



-- ROBERTBROKEIT: a is now a SapicFormula. A special case is a single atom with
-- syntactic sugar for predicates, but this contains BVars, which first need to
-- be translated to Vars
ppSapic trans (ProcessComb (Cond a)  _ pl _)  =
  ( text "if " <> pa <> text " then" $$ (nest 4 (parens ppl)), sh `S.union` pshl)
  where (ppl, pshl) = ppSapic trans pl
        (pa, sh) = ppFact' a
        ppFact' (Ato (Syntactic (Pred _))) = (text "non-predicate conditions not yet supported also not supported ;) ", S.empty )
                                                    --- note though that we can get a printout by converting to LNFormula, like this ppFact (toLNFormula formula)
        ppFact' _                          = (text "non-predicate conditions not yet supported", S.empty)

ppSapic trans (ProcessComb (CondEq t1 t2)  _ pl (ProcessNull _))  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) , sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic trans pl
                                           (pt1, sh1) = ppSapicTerm trans t1
                                           (pt2, sh2) = ppSapicTerm trans t2

-- ROBERTBROKEIT: commented out ... isn't this clashing with the previous defiition.
-- ppSapic (ProcessComb (Cond a)  _ pl (ProcessNull _))  =
--   ( text "if" <> pa $$ (nest 4 (parens ppl)), sh `S.union` pshl)
--   where (ppl, pshl) = ppSapic pl
--         (pa , sh  ) = ppFact a

ppSapic trans (ProcessComb (CondEq t1 t2)  _ pl pr)  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) $$ text "else" <> (nest 4 (parens ppr)), sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic trans pl
                                           (ppr, pshr) = ppSapic trans pr
                                           (pt1, sh1) = ppSapicTerm trans t1
                                           (pt2, sh2) = ppSapicTerm trans t2

ppSapic trans (ProcessComb (Lookup t c )  _ pl (ProcessNull _))  = (text "in(fcell(" <> pt <> text "), " <> pc
--                                                                    <> text "," <> text ptcounter <> text ":bitstring"
                                                                    <> text ");"
                                                       $$ text "event CellRead( (" <> pt <> text "," <> pc'
--                                                       <> text "," <> text ptcounter
                                                       <> text "));"
                                                       $$ ppl
                                                      , sh `S.union` pshl)
  where (pt, sh) = ppSapicTerm Proverif t
        pc = ppTypeVar Proverif c
        pc' = ppTypeVar DeepSec c
--        ptcounter = "countercell" ++ stripNonAlphanumerical (render pt)
        (ppl, pshl) = ppSapic trans pl





ppSapic Proverif (ProcessAction Rep _ p)  = (text "!" $$ parens pp, psh)
                                   where (pp, psh) = ppSapic Proverif p
ppSapic DeepSec (ProcessAction Rep _ p)  = (text "" <> parens pp, psh)
                                   where (pp, psh) = ppSapic DeepSec p
ppSapic trans  (ProcessAction a _ (ProcessNull _))  = (pa <> text "0", sh)
                                     where (pa, sh) = ppAction trans a
ppSapic trans  (ProcessAction a _ p)  = (pa $$ pp , sh `S.union` psh)
                                     where (pa, sh) = ppAction trans a
                                           (pp, psh) = ppSapic trans p

loadProc :: OpenTheory -> (Doc, S.Set ProverifHeader)
loadProc thy = case theoryProcesses thy of
  []  -> (text "", S.empty)
  [p] -> ppSapic Proverif p
  _  -> (text "Multiple sapic processes detected, error", S.empty)


loadMacroProc :: Translation -> OpenTheory -> ([Doc], S.Set ProverifHeader)
loadMacroProc trans thy = load (theoryProcessDefs thy)
  where
    load [] = ([text ""], S.empty)
    load (p:q) =
      let (docs, heads) = load q in
        case L.get pVars p of
          [] -> (docs, heads)
          pvars ->
            let (new_text, new_heads) = ppSapic trans (L.get pBody p) in
            let vars  = text "(" <> (fsep (punctuate comma (map (ppTypeVar trans) pvars ))) <> text ")"in
             let macro_def = text "let " <> (text $ L.get pName p) <> vars <> text "=" $$
                             (nest 4 new_text) <> text "." in
               (macro_def : docs, new_heads `S.union` heads)


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
ppNAtom :: ProtoAtom s LNTerm -> Doc
ppNAtom  = ppAtom (fst . (ppLNTerm Proverif))

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
loadHeaders :: Translation -> OpenTheory -> S.Set ProverifHeader
loadHeaders trans thy =
  (S.map  typedHeaderOfFunSym funSymsNoBuiltin) `S.union` funSymsBuiltins `S.union` (S.foldl (\x y -> x `S.union` (headersOfRule trans y)) S.empty sigRules)
  where sig = (L.get sigpMaudeSig (L.get thySignature thy))
        -- generating headers for function symbols, both for builtins and user defined functions
        sigFunSyms = funSyms sig
        sigStFunSyms = stFunSyms sig
        funSymsBuiltins = ((foldl (\x (y,z) -> if S.isSubsetOf (S.map NoEq y) sigFunSyms then  x `S.union` z else x )) S.empty builtins)
        funSymsNoBuiltin = sigStFunSyms S.\\ ((foldl (\x (y, _) -> x `S.union` y)) S.empty builtins)
        typedHeaderOfFunSym = headerOfFunSym (theoryFunctionTypingInfos thy)
        -- generating headers for equations
        sigRules = stRules sig S.\\ builtins_rules

headersOfRule :: Translation -> CtxtStRule -> S.Set ProverifHeader
headersOfRule trans r = case ctxtStRuleToRRule r of
  (lhs `RRule` rhs) ->
    (S.singleton hrule)  `S.union` lsh `S.union` rsh
    where (plhs,lsh) = ppLNTerm trans lhs
          (prhs,rsh) = ppLNTerm trans rhs
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



attribHeaders :: Translation -> [ProverifHeader] -> [Doc]
attribHeaders trans hd =
  sym ++ fun ++ eq
  where (eq,fun,sym) = splitHeaders hd
        pph = case trans of
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
  where hd = attribHeaders DeepSec $ S.toList (base_headers `S.union` (loadHeaders DeepSec thy)
                                       `S.union` macroprochd)
        requests = loadRequests thy
        (macroproc, macroprochd) = loadMacroProc DeepSec thy

        -- Loader of the export functions
------------------------------------------------------------------------------
loadRequests :: Theory sig c b p SapicElement -> [Doc]
loadRequests thy = [text $ get_text (lookupExportInfo "requests" thy)]
  where get_text Nothing = ""
        get_text (Just m) = L.get eText m
