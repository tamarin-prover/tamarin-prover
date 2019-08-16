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


import         Text.StringTemplate
import         Theory
import         Theory.Sapic
import         Text.PrettyPrint.Highlight

import qualified Text.PrettyPrint.Highlight as H

import qualified Data.Set as S
import qualified Data.Label as L
import Data.List as List
import qualified Data.ByteString.Char8 as BC


template = newSTMP $ unlines [
  "$headers;separator='\n'$",
  "",
  "$reduc;separator='\n'$",
  "",
  "$queries;separator='\n'$",
  "",
  "process",
  "    $process$",
  ""
  ] :: StringTemplate String

-- Proverif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProverifHeader =
  Sym String
  | Fun String
  | Eq String
  -- | Type String -- will  be used to define types
  deriving (Ord, Show, Eq)

-- We declare some base headers. Notably, we need a dedicated attacker channel.
base_headers = S.fromList [
  Sym ("free attacker_channel:channel.")
  ]
  
-- The corresponding headers for each Tamarin builtin. If the functions of the builtin are inside the signature, we add the corresponding headers to the output.
builtins = map (\(x,y) -> (x, S.fromList y)) [
  (hashFunSig, [Fun "fun hash(bitstring):bitstring."] ),
  (signatureFunSig, [
      Fun "fun sign(bitstring,bitstring):bitstring.",
      Fun "fun pk(bitstring):bitstring.",
      Eq "reduc forall m:bitstring,sk:bitstring; verify(sign(m,sk),m,pk(sk)) = true."
      ]
  ),
  (S.fromList [ expSym, oneSym], [
      Sym "const g:bitstring.",
      Fun "fun exp(bitstring,bitstring):bitstring",
      Eq "equation forall a:bitstring,b:bitstring; exp( exp(g,a),b) = exp(exp(g,b),a)."
      ]
  ),
  (asymEncFunSig, [
      Fun "fun senc(bitstring,bitstring):bitstring.",
      Eq "reduc forall m:bitstring,sk:bitstring; sdec(senc(m,sk),sk) = m."]
  ),
  (pairFunSig,  [Eq "reduc forall a:bitstring,b:bitstring; fst((a,b))=a.",
  Eq  "reduc forall a:bitstring,b:bitstring; snd((a,b))=b."]
  )
  ]


builtins_rules = foldl S.union S.empty [pairRules, symEncRules, asymEncRules, signatureRules]
  
-- utility function, generate a sequence of type arguments, for events and function declaration
make_args :: Int -> String
make_args 0 = ""
make_args 1 = "bitstring"
make_args n = "bitstring,"++(make_args (n-1))

-- main pp function  
prettyProVerifTheory :: HighlightDocument d => OpenTheory -> d
prettyProVerifTheory thy = text result
  where result = toString tmp
        tmp = setAttribute "process" proc $ setManyAttrib hd template
        hd = attribHeaders $ S.toList (base_headers `S.union` (loadHeaders thy) `S.union` prochd)
        (proc,prochd) = loadProc thy

-- pretty print an LNTerm, collecting the constant that need to be declared         
ppLNTerm :: LNTerm -> (String,S.Set ProverifHeader)
ppLNTerm t = (H.render $ ppTerm t, getHdTerm t)
  where
    ppTerm t = case viewTerm t of
        Lit  (Con (Name FreshName n))             -> text $ show n
        Lit  (Con (Name PubName n))               -> text $  show n
        Lit  (t)                                  -> text $  show t
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)      _       | isPair t -> ppTerms ", " 1 "(" ")" (split t)
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
    split t                          = [t]
  
    ppFun f ts =
      text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm t =  case viewTerm t of
        Lit  (Con (Name PubName n))               -> S.singleton   (Sym ("free " ++ show n ++":bitstring."))
        Lit  (t)                                  -> S.empty
        FApp _ ts                     -> foldl (\x y -> x `S.union` (getHdTerm y)) S.empty ts

-- pretty print a Fact, collecting the constant that need to be declared         
ppFact :: LNFact -> (String, S.Set ProverifHeader)
ppFact (Fact tag _ ts)
  | factTagArity tag /= length ts = sppFact ("MALFORMED-" ++ show tag) ts
  | otherwise                     = sppFact (showFactTag tag) ts
  where
    sppFact name ts = 
      (H.render $ nestShort' (name ++ "(") ")" . fsep . punctuate comma $ map text pts, sh)
      where (pts, shs) = unzip $ map ppLNTerm ts
            sh = foldl S.union S.empty shs

-- pretty print an Action, collecting the constant and events that need to be declared         
ppAction :: SapicAction -> (String, S.Set ProverifHeader)
ppAction (New n) = ("new "++ (show n) ++ ":bitstring", S.empty)
ppAction Rep  = ("!", S.empty)
ppAction (ChIn (Just t1) t2 )  = ("in(" ++ pt1 ++ "," ++ pt2 ++ ")", sh1 `S.union` sh2)
  where (pt1, sh1) = ppLNTerm t1
        (pt2, sh2) = ppLNTerm t2
ppAction (ChIn Nothing t2 )  = ("in(attacker_channel," ++ pt2 ++ ")", sh2)
  where (pt2, sh2) = ppLNTerm t2

ppAction (ChOut (Just t1) t2 )  = ("out(" ++ pt1 ++ "," ++ pt2 ++ ")", sh1 `S.union` sh2)
  where (pt1, sh1) = ppLNTerm t1
        (pt2, sh2) = ppLNTerm t2
ppAction (ChOut Nothing t2 )  = ("out(attacher_channel," ++ pt2 ++ ")", sh2)
  where (pt2, sh2) = ppLNTerm t2
ppAction (Event (Fact tag m ts) )  = ("event " ++ pa, sh `S.union` (S.singleton (Eq ("event " ++ (showFactTag tag) ++ "(" ++ make_args (length ts) ++ ")."))))
  where (pa, sh) = ppFact (Fact tag m ts)
ppAction _  = ("Action not supported for translation", S.empty)

ppComb :: ProcessCombinator -> (String, S.Set ProverifHeader)
ppComb Parallel = ("||", S.empty)
ppComb NDC = ("+", S.empty)
ppComb (Cond a) = ("if "++ pa, sh)
  where (pa, sh) = ppFact a
ppComb (CondEq t1 t2) = ("if "++ pt1 ++ "=" ++ pt2, sh1 `S.union` sh2)
  where (pt1, sh1) = ppLNTerm t1
        (pt2, sh2) = ppLNTerm t2                                          
ppComb (Lookup t v) = ("lookup "++ pt1 ++ " as " ++ show v, sh1)
  where (pt1, sh1) = ppLNTerm t

ppSapic :: AnProcess ann -> (String, S.Set ProverifHeader)
ppSapic  = pfoldMap f 
    where f (ProcessNull _) = ("0 \n", S.empty)
          f (ProcessComb c _ _ _)  = (pc ++ "\n", sh)
                                     where (pc, sh) = ppComb c
          f (ProcessAction Rep _ _)  = ppAction Rep 
          f (ProcessAction a _ _)  = (pa ++ ";", sh)
                                     where (pa, sh) = ppAction a


loadProc :: OpenTheory -> (String, S.Set ProverifHeader)
loadProc thy = case theoryProcesses thy of
  []  -> ("", S.empty)
  [p] -> ppSapic p
  ps  -> ("Multiple sapic processes detected, error", S.empty)

-- Load the proverif headers from the OpenTheory
loadHeaders :: OpenTheory -> S.Set ProverifHeader
loadHeaders thy =
  (S.map  headerOfFunSym funSymsNoBuiltin) `S.union` funSymsBuiltins `S.union` (S.foldl (\x y -> x `S.union` (headersOfRule y)) S.empty sigRules) 
  where sig = (L.get sigpMaudeSig (L.get thySignature thy))
        -- generating headers for function symbols, both for builtins and user defined functions
        sigFunSyms = stFunSyms sig
        funSymsBuiltins = ((foldl (\x (y,z) -> if S.isSubsetOf y sigFunSyms then  x `S.union` z else x )) S.empty builtins)
        funSymsNoBuiltin = sigFunSyms S.\\ ((foldl (\x (y,z) -> x `S.union` y  )) S.empty builtins)
        headerOfFunSym (f,(k,Public)) = Fun (make_str (f,k) ++ ".")
        headerOfFunSym (f,(k,Private)) = Fun ((make_str (f,k))  ++ " [private].")
        make_str (f,k) = "fun " ++ BC.unpack f ++ "(" ++ (make_args k) ++ "):bitstring"
        -- generating headers for equations
        sigRules = stRules sig S.\\ builtins_rules

headersOfRule r = case ctxtStRuleToRRule r of
  (lhs `RRule` rhs) -> (S.singleton hrule)  `S.union` lsh `S.union` rsh          
    where (plhs,lsh) = ppLNTerm lhs 
          (prhs,rsh) = ppLNTerm rhs
          hrule = Eq  ("equation forall" ++
                       make_frees (map show freesr)  ++
                       ";" ++
                       (H.render $ sep [ nest 2 $ text plhs
                           , operator_ "=" <-> (text prhs) ])++".")
          freesr = List.union (frees lhs) (frees rhs)        
          make_frees [] = ""
          make_frees [x] = x ++ ":bitstring"
          make_frees (x:xs) =  x ++ ":bitstring," ++ (make_frees xs)

attribHeaders :: [ProverifHeader] -> [(String, String)]
attribHeaders hd =
  eq ++ fun ++ sym
  where (eq,fun,sym) = splitHeaders hd
        splitHeaders [] = ([],[],[])
        splitHeaders (x:xs)
          | Sym s <- x = (e1,f1,("headers",s):s1)
          | Fun s <- x =  (e1,("headers",s):f1,s1)
          | Eq s <- x =  (("headers", s):e1,f1,s1)
          where (e1,f1,s1) = splitHeaders xs
          
