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
    prettyProVerifTheory

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

------------------------------------------------------------------------------
-- Core Export
------------------------------------------------------------------------------

template :: Document d => [d] -> [d] -> d -> [d] -> d
template headers queries process lemmas =
  vcat headers
  $$
  vcat queries
  $$
  vcat lemmas
  $$
  text "process"
  $$
  nest 4 process


prettyProVerifTheory :: OpenTheory -> Doc
prettyProVerifTheory thy =  template hd queries proc lemmas
  where hd = attribHeaders $ S.toList (base_headers `S.union` (loadHeaders thy) `S.union` prochd)
        (proc, prochd) = loadProc thy
        queries = loadQueries thy
        lemmas = loadLemmas thy

-- Proverif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProverifHeader =
  Sym String
  | Fun String
  | Eq String
  -- | Type String -- will  be used to define types
  deriving (Ord, Show, Eq)

-- We declare some base headers. Notably, we need a dedicated attacker channel.
base_headers :: S.Set ProverifHeader
base_headers = S.fromList [
  Sym ("free attacker_channel:channel.")
  ]

-- The corresponding headers for each Tamarin builtin. If the functions of the builtin are inside the signature, we add the corresponding headers to the output.
builtins :: [(NoEqFunSig, S.Set ProverifHeader)]
builtins = map (\(x,y) -> (x, S.fromList y)) [
  (hashFunSig, [Fun "fun hash(bitstring):bitstring."] ),
  (signatureFunSig, [
      Fun "fun sign(bitstring,bitstring):bitstring.",
      Fun "fun pk(bitstring):bitstring.",
      Eq "reduc forall m:bitstring,sk:bitstring; verify(sign(m,sk),m,pk(sk)) = true."
      ]
  ),
  (S.fromList [expSym], [
      Sym "const g:bitstring.",
      Fun "fun exp(bitstring,bitstring):bitstring.",
      Eq "equation forall a:bitstring,b:bitstring; exp( exp(g,a),b) = exp(exp(g,b),a)."
      ]
  ),
  (symEncFunSig, [
      Sym "type skey.",
      Fun "fun senc(bitstring,skey):bitstring.",
      Eq "reduc forall m:bitstring,sk:skey; sdec(senc(m,sk),sk) = m."]
  ),
  (pairFunSig,  [Eq "reduc forall a:bitstring,b:bitstring; fst((a,b))=a.",
  Eq  "reduc forall a:bitstring,b:bitstring; snd((a,b))=b."]
  ),
  (asymEncFunSig, [
      Sym "type skey.",
      Sym "type pkey.",
      Fun "fun aenc(bitstring,pkey):bitstring.",
      Fun "fun pk(skey):pkey.",
      Eq "reduc forall m:bitstring,sk:skey; adec(aenc(m,pk(sk)),sk) = m."]
  )
  ]

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

ppTypeVar :: Document p => SapicLVar -> p
ppTypeVar (SapicLVar (LVar n _ _ )  Nothing _) = text n <> text ":bitstring"
ppTypeVar (SapicLVar (LVar n _ _ ) (Just t) _) = text n <> text ":" <> (text t)


ppTypeLit :: (Show c, Document p) => Lit c SapicLVar -> p
ppTypeLit (Var v) = ppTypeVar v
ppTypeLit (Con c) = text $ show c

-- pretty print an LNTerm, collecting the constant that need to be declared
-- a boolean b allows to add types to variables (for input bindings)
auxppSapicTerm :: Bool -> Bool -> SapicTerm -> (Doc, S.Set ProverifHeader)
auxppSapicTerm b0 b t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
        Lit  (Con (Name FreshName n))             ->  (text $ show n) <> text "test"
        Lit  (Con (Name PubName n))     | b0      -> text "=" <> (text $ show n)
        Lit  (Con (Name PubName n))               -> text $ show n
        Lit  (Var (SapicLVar (LVar n _ _) _ True)) -> text "=" <> text n
        Lit  v                    |    b          -> ppTypeLit v
        Lit  (Var (SapicLVar (LVar n _ _)  _ _))  -> (text n)
        Lit  v                                    -> (text $ show v)
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> text "exp(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq _)      _       | isPair tm -> ppTerms ", " 1 "(" ")" (split tm)
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
            S.singleton   (Sym ("free " ++ show n ++":bitstring."))
        Lit  (_)                                  -> S.empty
        FApp _ ts                     -> foldl (\x y -> x `S.union` (getHdTerm y)) S.empty ts

pppSapicTerm :: Bool -> SapicTerm -> (Doc, S.Set ProverifHeader)
pppSapicTerm = auxppSapicTerm False

ppSapicTerm :: SapicTerm -> (Doc, S.Set ProverifHeader)
ppSapicTerm = pppSapicTerm False

-- TODO: we should generalise functionality so pppSapicTerm and pppLNTerm share
-- the code they have in common
pppLNTerm :: Bool -> LNTerm -> (Doc, S.Set ProverifHeader)
pppLNTerm b t = (ppTerm t, getHdTerm t)
  where
    ppTerm tm = case viewTerm tm of
        Lit  (Con (Name FreshName n))             -> text $ show n
        Lit  (Con (Name PubName n))               -> text $ show n
        Lit  (tm2)              | b               -> text $ show tm2 <> ":bitstring"
        Lit  (Var (LVar tm2 _ _ ))                -> text tm2
        Lit  (tm2)                                -> text $ show tm2
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq _)      _       | isPair t -> ppTerms ", " 1 "(" ")" (split tm)
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
            S.singleton   (Sym ("free " ++ show n ++":bitstring."))
        Lit  (_)                                  -> S.empty
        FApp _ ts                     -> foldl (\x y -> x `S.union` (getHdTerm y)) S.empty ts

ppLNTerm :: LNTerm -> (Doc, S.Set ProverifHeader)
ppLNTerm = pppLNTerm False

-- pretty print a Fact, collecting the constant that need to be declared
ppFact :: Fact SapicTerm -> (Doc, S.Set ProverifHeader)
ppFact (Fact tag _ ts)
  | factTagArity tag /= length ts = sppFact ("MALFORMED-" ++ show tag) ts
  | otherwise                     = sppFact (showFactTag tag) ts
  where
    sppFact name ts2 =
      (nestShort' (name ++ "(") ")" . fsep . punctuate comma $ pts, sh)
      where (pts, shs) = unzip $ map ppSapicTerm ts2
            sh = foldl S.union S.empty shs

-- pretty print an Action, collecting the constant and events that need to be declared
ppAction :: LSapicAction -> (Doc, S.Set ProverifHeader)
ppAction (New v@(SapicLVar (LVar _ _ _) _ _)) = (text "new " <> (ppTypeVar v), S.empty)
ppAction Rep  = (text "!", S.empty)
ppAction (ChIn (Just t1) t2 )  = (text "in(" <> pt1 <> text "," <> pt2 <> text ")", sh1 `S.union` sh2)
  where (pt1, sh1) = ppSapicTerm t1
        (pt2, sh2) = auxppSapicTerm True True t2
ppAction (ChIn Nothing t2 )  = (text "in(attacker_channel," <> pt2 <> text ")", sh2)
  where (pt2, sh2) = auxppSapicTerm True True t2

ppAction (ChOut (Just t1) t2 )  = (text "out(" <> pt1 <> text "," <> pt2 <> text ")", sh1 `S.union` sh2)
  where (pt1, sh1) = ppSapicTerm t1
        (pt2, sh2) = ppSapicTerm t2
ppAction (ChOut Nothing t2 )  = (text "out(attacker_channel," <> pt2 <> text ")", sh2)
  where (pt2, sh2) = ppSapicTerm t2
ppAction (Event (Fact tag m ts) )  = (text "event " <> pa, sh `S.union` (S.singleton (Eq ("event " ++ (showFactTag tag) ++ "(" ++ make_args (length ts) ++ ")."))))
  where (pa, sh) = ppFact (Fact tag m ts)
ppAction _  = (text "Action not supported for translation", S.empty)

ppSapic :: LProcess ann -> (Doc, S.Set ProverifHeader)
ppSapic (ProcessNull _) = (text "0", S.empty)
ppSapic (ProcessComb Parallel _ pl pr)  = ( (nest 2 (parens ppl)) $$ text "|" $$ (nest 2 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
ppSapic (ProcessComb NDC _ pl pr)  = ( (nest 4 (parens ppl)) $$ text "+" <> (nest 4 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
ppSapic (ProcessComb (Let t1 t2) _ pl (ProcessNull _))  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                               ,sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic pl
                                           (pt1, sh1) = auxppSapicTerm True True t1
                                           (pt2, sh2) = ppSapicTerm t2

ppSapic (ProcessComb (Let t1 t2) _ pl pr)  =   ( text "let "  <> pt1 <> text "=" <> pt2 <> text " in"
                                                 $$ ppl
                                                 $$ text "else" <> ppr
                                               ,sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
                                           (pt1, sh1) = auxppSapicTerm True True t1
                                           (pt2, sh2) = ppSapicTerm t2

ppSapic (ProcessComb (ProcessCall _ _ []) _ pl _)  =   (ppl, pshl)
                                     where (ppl, pshl) = ppSapic pl


-- ROBERTBROKEIT: a is now a SapicFormula. A special case is a single atom with
-- syntactic sugar for predicates, but this contains BVars, which first need to
-- be translated to Vars
ppSapic (ProcessComb (Cond a)  _ pl (ProcessNull _))  =
  ( text "if " <> pa <> text " then" $$ (nest 4 (parens ppl)), sh `S.union` pshl)
  where (ppl, pshl) = ppSapic pl
        (pa, sh) = ppFact' a
        ppFact' (Ato (Syntactic (Pred _))) = (text "non-predicate conditions not yet supported also not supported ;) ", S.empty )
                                                    --- note though that we can get a printout by converting to LNFormula, like this ppFact (toLNFormula formula)
        ppFact' _                          = (text "non-predicate conditions not yet supported", S.empty)

ppSapic (ProcessComb (CondEq t1 t2)  _ pl (ProcessNull _))  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) , sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic pl
                                           (pt1, sh1) = ppSapicTerm t1
                                           (pt2, sh2) = ppSapicTerm t2

-- ROBERTBROKEIT: commented out ... isn't this clashing with the previous defiition.
-- ppSapic (ProcessComb (Cond a)  _ pl (ProcessNull _))  =
--   ( text "if" <> pa $$ (nest 4 (parens ppl)), sh `S.union` pshl)
--   where (ppl, pshl) = ppSapic pl
--         (pa , sh  ) = ppFact a

ppSapic (ProcessComb (CondEq t1 t2)  _ pl pr)  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) $$ text "else" <> (nest 4 (parens ppr)), sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
                                           (pt1, sh1) = ppSapicTerm t1
                                           (pt2, sh2) = ppSapicTerm t2

ppSapic (ProcessComb (Lookup t v )  _ pl pr)  = (text "lookup " <> pt1 <> text " as " <> (text $ show v) $$ (nest 4 (parens ppl)) $$ text "else" <> (nest 4 (parens ppr)), sh1 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
                                           (pt1, sh1) = ppSapicTerm t



ppSapic (ProcessAction Rep _ p)  = (text "!" <> parens pp, psh)
                                   where (pp, psh) = ppSapic p
ppSapic  (ProcessAction a _ (ProcessNull _))  = (pa, sh)
                                     where (pa, sh) = ppAction a
ppSapic  (ProcessAction a _ p)  = (pa <> text ";" $$ pp , sh `S.union` psh)
                                     where (pa, sh) = ppAction a
                                           (pp, psh) = ppSapic p

loadProc :: OpenTheory -> (Doc, S.Set ProverifHeader)
loadProc thy = case theoryProcesses thy of
  []  -> (text "", S.empty)
  [p] -> ppSapic p
  _  -> (text "Multiple sapic processes detected, error", S.empty)




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

ppNAtom :: ProtoAtom s LNTerm -> Doc
ppNAtom  = ppAtom (fst . ppLNTerm)

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

headerOfFunSym :: [SapicFunSym] -> NoEqSym -> ProverifHeader

headerOfFunSym []  (_,(_,_,Destructor)) = Fun ("")
headerOfFunSym []  (f,(k,Public,Constructor))  =  Fun (make_str (f,k) ++ ".")
headerOfFunSym []  (f,(k,Private,Constructor)) =  Fun ((make_str (f,k))  ++ " [private].")



headerOfFunSym  (((f,(k,Public,Constructor)),inTypes,Just outType):remainder)  fs2@(f2,(k2,Public,_)) =
  if f2==f && k2 == k then
    Fun ("fun " ++ BC.unpack f ++ "(" ++ (make_argtypes inTypes) ++ "):" ++ outType ++ ".")
  else headerOfFunSym remainder fs2
headerOfFunSym  (((f,(k,Private,Constructor)),inTypes,Just outType):remainder)  fs2@(f2,(k2,Private,_)) =
  if f2==f && k2 == k then
    Fun ("fun " ++ BC.unpack f ++ "(" ++ (make_argtypes inTypes) ++ "):" ++ outType ++ "[private].")
  else headerOfFunSym remainder fs2

headerOfFunSym  (_:remainder)  fs2 =
   headerOfFunSym remainder fs2


-- Load the proverif headers from the OpenTheory
loadHeaders :: OpenTheory -> S.Set ProverifHeader
loadHeaders thy =
  (S.map  typedHeaderOfFunSym funSymsNoBuiltin) `S.union` funSymsBuiltins `S.union` (S.foldl (\x y -> x `S.union` (headersOfRule y)) S.empty sigRules)
  where sig = (L.get sigpMaudeSig (L.get thySignature thy))
        -- generating headers for function symbols, both for builtins and user defined functions
        sigFunSyms = funSyms sig
        sigStFunSyms = stFunSyms sig
        funSymsBuiltins = ((foldl (\x (y,z) -> if S.isSubsetOf (S.map NoEq y) sigFunSyms then  x `S.union` z else x )) S.empty builtins)
        funSymsNoBuiltin = sigStFunSyms S.\\ ((foldl (\x (y, _) -> x `S.union` y)) S.empty builtins)
        typedHeaderOfFunSym = headerOfFunSym (theoryFunctionTypingInfos thy)
        -- generating headers for equations
        sigRules = stRules sig S.\\ builtins_rules

headersOfRule :: CtxtStRule -> S.Set ProverifHeader
headersOfRule r = case ctxtStRuleToRRule r of
  (lhs `RRule` rhs) ->
    (S.singleton hrule)  `S.union` lsh `S.union` rsh
    where (plhs,lsh) = ppLNTerm lhs
          (prhs,rsh) = ppLNTerm rhs
          hrule = Eq  (prefix <> " forall " ++
                       make_frees (map show freesr)  ++
                       ";" ++
                       (render $ sep [ nest 2 $ plhs
                           , text "=" <-> prhs ])++".")
          freesr = List.union (frees lhs) (frees rhs)
          make_frees [] = ""
          make_frees [x] = x ++ ":bitstring"
          make_frees (x:xs) =  x ++ ":bitstring," ++ (make_frees xs)
          prefix = case viewTerm lhs of
            FApp (NoEq (_, (_,_,Destructor))) _ -> "reduc"
            _ -> "equation"


attribHeaders :: [ProverifHeader] -> [Doc]
attribHeaders hd =
  sym ++ fun ++ eq
  where (eq,fun,sym) = splitHeaders hd
        splitHeaders [] = ([],[],[])
        splitHeaders (x:xs)
          | Sym s <- x = (e1,f1,(text s):s1)
          | Fun s <- x =  (e1,(text s):f1,s1)
          | Eq s <- x =  ((text s):e1,f1,s1)
          where (e1,f1,s1) = splitHeaders xs



------------------------------------------------------------------------------
-- Some utility functions
------------------------------------------------------------------------------

make_str :: (BC.ByteString, Int) -> [Char]
make_str (f,k) = "fun " ++ BC.unpack f ++ "(" ++ (make_args k) ++ "):bitstring"

make_argtypes :: [SapicType] -> String
make_argtypes [] = ""
make_argtypes [Just t] = t
make_argtypes ((Just p):t) = p ++ "," ++ (make_argtypes t)
make_argtypes _ = "Error: ill-defined type"

make_args :: Int -> String
make_args 0 = ""
make_args 1 = "bitstring"
make_args n = "bitstring,"++(make_args (n-1))
