{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns               #-}
-- |
-- Copyright   : (c) 2022 Julian Biehl
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Julian Biehl <s8jubieh@stud.uni-saarland.de>
-- Portability : GHC only
--
-- Translation from multiset rewrite rules to Proverif

module RuleTranslation (
    loadRules
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

import           Control.Monad.Fresh
import           Control.Exception
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
-- MSR Translation
------------------------------------------------------------------------------

loadRules :: OpenTheory -> ([Doc], Doc, ([(String, String, String, [String])], [(String, String, String, String)], [(String, String, String, [String])], [(String, String)], [(String, String)]))
loadRules thy = case theoryRules thy of
  [] -> ([text ""], text "", ([],[],[],[],[]))
  rules -> (ruleDocs, ruleComb, headers)
           where
            (ruleDocs, destructors) = foldl (\(docs, destrs) r -> let (doc, destrs') = translateOpenProtoRule r thy destrs in (docs++[doc], destrs')) ([], M.empty) rules
            headers = (baseHeaders, desHeaders, frHeaders, tblHeaders, evHeaders)
            baseHeaders = [("free", "publicChannel", ":channel", [])]
            desHeaders = map makeDestructorHeader $ M.toList destructors
            (frHeaders, tblHeaders, evHeaders) =
              foldl (\(fr, tbl, ev) ru -> let (fr', tbl', ev') = makeHeadersFromRule ru in (fr ++ fr', tbl ++ tbl', ev ++ ev')) ([], [], []) rules
            ruleNames = map (\(OpenProtoRule ruE _) -> showRuleName . L.get preName $ L.get rInfo ruE) rules
            ruleComb = text ("( " ++ (intercalate " | " . map (++")") $ map ("!("++) ruleNames) ++ " )")

makeDestructorHeader :: ((String, String), String) -> (String, String, String, String)
makeDestructorHeader ((dDef, atom), dName) =
  let (s1,s2) = break (=='#') dDef
  in
    ("reduc", s1, (dName ++ "(" ++ tail s2 ++ ") = " ++ (showAtom2 atom)), "[private]")

makeHeadersFromRule:: OpenProtoRule -> ([(String, String, String, [String])], [(String, String)], [(String, String)])
makeHeadersFromRule (OpenProtoRule ruE _) = makeHeadersFromProtoRule ruE

makeHeadersFromProtoRule :: Rule ProtoRuleEInfo -> ([(String, String, String, [String])], [(String, String)], [(String, String)])
makeHeadersFromProtoRule ru = 
  (frees, tables, events)
    where
    acts             = filter isNotDiffAnnotation (L.get rActs ru)
    isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0, factAnnotations = S.empty, factTerms = []})
    facts proj     = L.get proj ru
    frees = makeFreeHeaders (facts rPrems) acts (facts rConcs)
    tables = makeTableHeaders (facts rPrems) (facts rConcs)
    events = makeEventHeaders acts

makeFreeHeaders :: [LNFact] -> [LNFact] -> [LNFact] -> [(String, String, String, [String])]
makeFreeHeaders prems acts concls = 
  headers
  where
    getTerms (Fact _ _ ts) = ts
    allTerms = (concat $ map getTerms prems) ++ (concat $ map getTerms acts) ++ (concat $ map getTerms concls)
    bitstrings = foldl (\acc t -> S.union acc $ searchForBitstrings t) (S.empty) (S.toList $ S.fromList allTerms)
    headers = map (\b -> ("free", b, ":bitstring", [])) $ S.toList bitstrings

searchForBitstrings :: (Show l) => Term l -> S.Set String
searchForBitstrings t = case viewTerm t of
    Lit l     -> if (head $ show l) == '\'' && (last $ show l) == '\'' then S.fromList [showAtom $ show l] else S.empty
    FApp _ ts -> foldl (\acc t -> S.union acc $ searchForBitstrings t) (S.empty) ts

makeTableHeaders :: [LNFact] -> [LNFact] -> [(String, String)]
makeTableHeaders prems concls =
  headers
  where
    getFactInfo (Fact tag _ ts) = (showFactName tag, length ts)
    allFactInfos = S.toList $ S.fromList (map getFactInfo prems ++ map getFactInfo concls)
    tableInfos = filter (\(t, _) -> t /= "Fr" && t /= "Out" && t /= "In") allFactInfos
    headers = map (\(t,n) -> (t, "(" ++ (intercalate ", " $ replicate n "bitstring") ++ ")")) tableInfos

makeEventHeaders :: [LNFact] -> [(String, String)]
makeEventHeaders acts = 
  headers
  where
    getFactInfo (Fact tag _ ts) = (showEventName tag, length ts)
    allFactInfos = S.toList $ S.fromList (map getFactInfo acts)
    headers = map (\(t,n) -> (t, "(" ++ (intercalate ", " $ replicate n "bitstring") ++ ")")) allFactInfos

translateOpenProtoRule :: HighlightDocument d => OpenProtoRule -> OpenTheory -> M.Map (String, String) String -> (d, M.Map (String, String) String)
translateOpenProtoRule (OpenProtoRule ruE _) thy de = translateProtoRule (checkTypes ruE thy) de

checkTypes :: Rule ProtoRuleEInfo -> OpenTheory -> Rule ProtoRuleEInfo
checkTypes ru thy = case length incorrectFunctionUsages of
  0 -> ru
  1 -> throw (UnsupportedTypes ("The function " ++ (incorrectFunctionUsages !! 0) ++ ", which is declared with a user-defined type, appears in a rewrite rule. ") :: ExportException)
  _ -> let functions_string = List.intercalate ", " incorrectFunctionUsages
       in
        throw (UnsupportedTypes ("The functions " ++ functions_string ++ ", which are declared with user-defined types, appear in a rewrite rule. ") :: ExportException)
  where
    acts             = filter isNotDiffAnnotation (L.get rActs ru)
    isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0, factAnnotations = S.empty, factTerms = []})
    facts proj     = L.get proj ru
    allFacts = (facts rPrems) ++ acts ++ (facts rConcs)
    allTerms = foldl (\acc (Fact _ _ ts) -> acc ++ ts) [] allFacts
    incorrectFunctionUsages = S.toList . S.fromList $ foldl (\acc t -> acc ++ incorrectTermTypes thy t) [] allTerms

incorrectTermTypes :: (Show l) => OpenTheory -> Term l -> [String]
incorrectTermTypes thy t = case viewTerm t of
    Lit l                 -> []
    FApp (NoEq (f, _)) ts -> (checkFun $ BC.unpack f) ++ (foldl (\acc x -> acc ++ incorrectTermTypes thy x) [] ts)
    FApp _             ts -> foldl (\acc x -> acc ++ incorrectTermTypes thy x) [] ts
    where
      functionInfo = theoryFunctionTypingInfos thy
      checkFun name = foldl (\acc ((f, _), inTypes, outType) -> acc ++ (if (BC.unpack f) == name then typeChecker name inTypes outType else [])) [] functionInfo
      typeChecker name _ (Just _)             = [name]
      typeChecker name [] _                   = []
      typeChecker name (Nothing : ts) outType = typeChecker name ts outType
      typeChecker name (Just _ : ts) _        = [name]

translateProtoRule :: (HighlightDocument d)
                => Rule ProtoRuleEInfo -> M.Map (String, String) String -> (d, M.Map (String, String) String)
translateProtoRule ru de =
    (ruleDoc, destructors)
    where
    acts             = filter isNotDiffAnnotation (L.get rActs ru)
    isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0, factAnnotations = S.empty, factTerms = []})
    facts proj     = L.get proj ru
    (factsDoc,destructors) = translateRule (facts rPrems) acts (facts rConcs) de
    ruleDoc = text "let" <-> (text . showRuleName . L.get preName $ L.get rInfo ru) <-> text "=" $-$
              nest 8
              factsDoc

showRuleName :: ProtoRuleName -> String
showRuleName FreshRule = "rFresh"
showRuleName (StandRule s) = "r" ++ s

translateRule :: (HighlightDocument d) => [LNFact] -> [LNFact] -> [LNFact] -> M.Map (String, String) String -> (d, M.Map (String, String) String)
translateRule prems acts concls destrs = 
    let (docs1, vars1, vars1', destr1) = translatePatterns prems "GET" patternGetsFilter S.empty M.empty destrs
        (docs2, vars2) = translateNonPatterns prems "GET" nonPatternGetsFilter vars1
        (docs3, vars3, _, destr3) = translatePatterns prems "IN" patternInsFilter vars2 vars1' destr1
        (docs4, vars4) = translateNonPatterns prems "IN" nonPatternInsFilter vars3
        (docs5, vars5) = translateNonPatterns prems "NEW" newsFilter vars4
        (docs6, vars6) = translateNonPatterns acts "EVENT" (\x -> True) vars5
        (docs7, vars7) = translateNonPatterns (concls \\ prems) "INSERT" isStorage vars6
        (docs8, _) = translateNonPatterns concls "OUT" outsFilter vars7
      in
    (combineRuleDocs (docs1++docs2++docs3) (docs4++docs5++docs6++docs7++docs8), destr3)

combineRuleDocs :: (HighlightDocument d) => [d] -> [d] -> d
combineRuleDocs rd1 rd2 = case rd2 of
                           [] -> vcat rd1 $-$ text "0."
                           _  -> vcat rd1 $-$ separateRuleDocs rd2
                          where
                            separateRuleDocs [r] = r <> text "."
                            separateRuleDocs (r:rs) = r <> semi $-$ separateRuleDocs rs


isStorage :: LNFact -> Bool
isStorage (Fact tag _ _) = case factTagName tag of
  "Fr"  -> False
  "In"  -> False
  "Out" -> False
  _     -> True

isPattern :: Term l -> Bool
isPattern t = case viewTerm t of
    Lit _ -> False
    _     -> True

hasPattern :: LNFact -> Bool
hasPattern (Fact _ _ ts) = 
  foldl (\acc t -> acc || isPattern t) False ts

patternGetsFilter :: LNFact -> Bool
patternGetsFilter p = (isStorage p) && hasPattern p

nonPatternGetsFilter :: LNFact -> Bool
nonPatternGetsFilter p = (isStorage p) && not (hasPattern p)

patternInsFilter :: LNFact -> Bool
patternInsFilter p@(Fact tag _ _) = (factTagName tag) == "In" && hasPattern p

nonPatternInsFilter :: LNFact -> Bool
nonPatternInsFilter p@(Fact tag _ _) = (factTagName tag) == "In" && not (hasPattern p)

newsFilter :: LNFact -> Bool
newsFilter (Fact tag _ _) = (factTagName tag) == "Fr"

outsFilter :: LNFact -> Bool
outsFilter (Fact tag _ _) = (factTagName tag) == "Out"

translatePatterns :: (HighlightDocument d) => [LNFact] -> String -> (LNFact -> Bool) -> S.Set String -> M.Map String String -> M.Map (String, String) String -> ([d], S.Set String, M.Map String String, M.Map (String, String) String)
translatePatterns facts factType filterFunction vars helperVars destructors =
    let (doclist, finalvars, finalHelperVars, finalDestructors) = foldl (\(d1, v1, v1', destr1) g -> let (d2, v2, v2', destr2) = translate g v1 v1' destr1 in (d1 ++ [d2], (S.union v1 v2), v2', destr2)) ([], vars, helperVars, destructors) patternFacts
      in
    (doclist, finalvars, finalHelperVars, finalDestructors)
    where
      patternFacts = filter filterFunction facts
      translate prem@(Fact _ _ ts) vs hvs destrs = (getDoc, atoms, newHelperVars, newDestructors)
                                             where
                                               (factDoc, newHelperVars) = translatePatternFact prem factType vs hvs
                                               (destrDocList, atoms, newDestructors) = foldl (\(docs,vset,des) t -> let (doc,vset',des') = makeDestructorExpressions vset newHelperVars des t in (docs ++ [doc], vset `S.union` vset', des')) ([], (vs `S.union` literals), destrs) patternTerms
                                               getDoc = factDoc $-$ (vcat $ destrDocList)
                                               patternTerms = filter isPattern ts
                                               literals = S.fromList (foldl (\acc t -> acc ++ getAtoms t) [] (filter (not . isPattern) ts))


translateNonPatterns :: HighlightDocument d => [LNFact] -> String -> (LNFact -> Bool) -> S.Set String -> ([d], S.Set String)
translateNonPatterns facts factType filterFunction vars =
    let (doclist, finalvars) = foldl (\(d1, v1) g -> let (d2, v2) = translate g v1 in (d1 ++ [d2], S.union v1 v2)) ([], vars) nonPatternFacts
     in
    (doclist, finalvars)
    where
      nonPatternFacts = filter filterFunction facts
      translate prem@(Fact _ _ ts) vs = (getDoc, atoms)
                                             where
                                              getDoc = case factType of
                                                "OUT"    -> if checkForNewIDs
                                                              then idConstructor $-$ translateFact prem factType vs
                                                              else translateFact prem factType vs
                                                "INSERT" -> if checkForNewIDs
                                                              then idConstructor $-$ translateFact prem factType vs
                                                              else translateFact prem factType vs
                                                "EVENT"  -> if checkForNewIDs
                                                              then idConstructor $-$ translateFact prem factType vs
                                                              else translateFact prem factType vs
                                                _        -> translateFact prem factType vs
                                              atoms = S.fromList (foldl (\acc t -> acc ++ getAtoms t) [] ts)
                                              checkForNewIDs = if atoms `S.isSubsetOf` vs
                                                                 then False
                                                                 else foldl (\acc a -> acc || ((head a) == '$')) False $ S.difference atoms vs
                                              idConstructor = idExp . S.toList $ S.difference atoms vs
                                              idExp as = vcat . map (\a -> text "in(publicChannel, " <> (text $ showAtom a) <> text ": bitstring);") . filter (\a -> (head a) == '$') $ as


translateFact :: Document d => LNFact -> String -> S.Set String -> d
translateFact (Fact tag _ ts) factType vars = case factType of
    "GET"    -> text "get" <-> text (showFactName tag) <> text "(" <> (fsep . punctuate comma $ map (translateTerm vars True) ts) <> text ") in"
    "IN"     -> if (head $ printTerm vars True (head ts)) == '='
                  then text "in(publicChannel," <-> (translateTerm vars True (head ts)) <> text ")"
                  else text "in(publicChannel," <-> (translateTerm vars True (head ts)) <> text ": bitstring)"
    "NEW"    -> text "new" <-> (translateTerm S.empty False (head ts)) <> text ": bitstring"
    "INSERT" -> text "insert" <-> text (showFactName tag) <> text "(" <> (fsep . punctuate comma $ map (translateTerm S.empty False) ts) <> text ")"
    "OUT"    -> text "out(publicChannel," <-> (translateTerm S.empty False (head ts)) <> text ")"
    "EVENT"  -> text "event" <-> text (showEventName tag) <> text "(" <> (fsep . punctuate comma $ map (translateTerm S.empty False) ts) <> text ")"
    _        -> text "" --should never happen

translatePatternFact :: (Document d) => LNFact -> String -> S.Set String -> M.Map String String -> (d, M.Map String String)
translatePatternFact (Fact tag _ ts) factType vars helperVars =
    (factDoc, newHelperVars)
    where
      (doclist, newHelperVars) = foldl (\(docs, helpers) t -> let (doc, helpers') = translatePatternTerm vars helpers t in (docs ++ [doc], helpers')) ([], helperVars) ts
      factDoc = case factType of
        "GET" -> text "get" <-> text (showFactName tag) <> text "(" <> (fsep . punctuate comma $ doclist) <> text ") in"
        "IN"  -> text "in(publicChannel," <-> (head doclist) <> text ": bitstring);"
        _     -> text "" --should never happen

showAtom :: String -> String
showAtom a = case head a of
  '~'  -> sanitizeAtom . replaceDots $ tail a
  '$'  -> sanitizeAtom . replaceDots $ tail a
  '\'' -> 's' : (replaceDots . init $ tail a)
  _    -> sanitizeAtom $ replaceDots a
  where
    replaceDots a = map (\c -> if c == '.' then '_' else c) a
    reserved_words = ["among", "axiom", "channel", "choice", "clauses", "const", "def", "diff",
      "do", "elimtrue", "else", "equation", "equivalence", "event", "expand", "fail", "for",
      "forall", "foreach", "free", "fun", "get", "if", "implementation", "in", "inj-event",
      "insert", "lemma", "let", "letfun", "letproba", "new", "noninterf", "noselect", "not",
      "nounif", "or", "otherwise", "out", "param", "phase", "pred", "proba", "process",
      "proof", "public_vars", "putbegin", "query", "reduc", "restriction", "secret", "select",
      "set", "suchthat", "sync", "table", "then", "type", "weaksecret", "yield"]
    sanitizeAtom a = if a `List.elem` reserved_words
                       then 'a' : a
                       else a

showAtom2 :: String -> String
showAtom2 a = case head a of
  '~'  -> "var_" ++ (replaceDots $ tail a)
  '$'  -> "var_" ++ (replaceDots $ tail a)
  '\'' -> "var_" ++ (map toLower . replaceDots . init $ tail a)
  _    -> "var_" ++ replaceDots a
  where
    replaceDots a = map (\c -> if c == '.' then '_' else c) a

showFunction :: String -> String
showFunction f
  | f == "true" = "okay"
  | otherwise   = f

showFactName :: FactTag -> String
showFactName tag = if factTagName tag `List.elem` ["Fr", "In", "Out"]
                     then factTagName tag
                     else 't' : factTagName tag

showEventName :: FactTag -> String
showEventName tag = 'e' : factTagName tag

translateTerm :: (Document d, Show l) => S.Set String -> Bool -> Term l -> d
translateTerm vars checkEq t = text $ printTerm vars checkEq t

printTerm :: (Show l) => S.Set String -> Bool -> Term l -> String
printTerm vars checkEq t = case viewTerm t of
    Lit l | checkEq && (S.member (show l) vars || head (show l) == '\'') -> '=' : (showAtom $ show l)
    Lit l                                           -> showAtom $ show l
    FApp (AC Mult)     ts                           -> printAC "mult" ts
    FApp (AC Union)    ts                           -> printAC "union" ts
    FApp (AC Xor)      ts                           -> printAC "xor" ts
    FApp (NoEq (f, _)) ts | (BC.unpack f == "pair") -> printPair ts
    FApp (NoEq (f, _)) ts                           -> (showFunction $ BC.unpack f) ++ printList ts
    FApp (C EMap)      ts                           -> "em" ++ printList ts
    FApp List          ts                           -> printList ts
    where
      printList ts = "(" ++ (intercalate ", " $ map (printTerm vars checkEq) ts) ++ ")"
      printPair [t1,t2] = "(" ++ printTerm vars checkEq t1 ++ ", " ++ printTerm vars checkEq t2 ++ ")"
      printAC op [t1,t2] = op ++ "(" ++ printTerm vars checkEq t1 ++ ", " ++ printTerm vars checkEq t2 ++ ")"
      printAC op (t:ts) = op ++ "(" ++ printTerm vars checkEq t ++ ", " ++ printAC op ts ++ ")"

printTerm2 :: (Show l) => Term l -> String
printTerm2 t = case viewTerm t of
    Lit l                                           -> showAtom2 $ show l
    FApp (AC Mult)     ts                           -> printAC "mult" ts
    FApp (AC Union)    ts                           -> printAC "union" ts
    FApp (AC Xor)      ts                           -> printAC "xor" ts
    FApp (NoEq (f, _)) ts | (BC.unpack f == "pair") -> printPair ts
    FApp (NoEq (f, _)) ts                           -> (showFunction $ BC.unpack f) ++ printList ts
    FApp (C EMap)      ts                           -> "em" ++ printList ts
    FApp List          ts                           -> printList ts
    where
      printList ts = "(" ++ (intercalate ", " $ map printTerm2 ts) ++ ")"
      printPair [t1,t2] = "(" ++ printTerm2 t1 ++ ", " ++ printTerm2 t2 ++ ")"
      printAC op [t1,t2] = op ++ "(" ++ printTerm2 t1 ++ ", " ++ printTerm2 t2 ++ ")"
      printAC op (t:ts) = op ++ "(" ++ printTerm2 t ++ ", " ++ printAC op ts ++ ")"

translatePatternTerm :: (Document d, Show l) => S.Set String -> M.Map String String -> Term l -> (d, M.Map String String)
translatePatternTerm vars helperVars t = case viewTerm t of
    Lit l | (S.member (show l) vars || head (show l) == '\'') -> ((text "=" <> (text . showAtom $ show l)), helperVars)
    Lit l                                                     -> ((text . showAtom $ show l), helperVars)
    _                                                         -> (varDoc, newHelperVars)
                                                                 where
                                                                   (newVar, newHelperVars) = makeVariable t helperVars
                                                                   varDoc = text newVar

makeDestructorDefinition :: (Show l) => Term l -> String
makeDestructorDefinition t = 
  "forall " ++ intercalate ", " (map (++":bitstring") atoms) ++ ";#" ++ printTerm2 t
  where
    atoms = map showAtom2 . S.toList . S.fromList $ getAtoms t

makeVariable :: (Show l) => Term l -> M.Map String String -> (String, M.Map String String)
makeVariable t varMap = case M.lookup (printTerm S.empty False t) varMap of
    Just v  -> (v, varMap)
    Nothing -> let newVar = "helperVar" ++ (show $ M.size varMap)
                   newMap = M.insert (printTerm S.empty False t) newVar varMap
                 in
               (newVar, newMap)
      

makeDestructorName :: (Show l) => M.Map (String, String) String -> Term l -> String -> (String, M.Map (String, String) String)
makeDestructorName dMap t a = case M.lookup ((makeDestructorDefinition t),a) dMap of
    Just d  -> (d, dMap)
    Nothing -> let newDestructor = "g_" ++ (showAtom2 a) ++ "_" ++ (show $ M.size dMap)
                   newMap = M.insert ((makeDestructorDefinition t),a) newDestructor dMap
                 in
               (newDestructor, newMap)

makeDestructorExpressions :: (Document d, Show l, Ord l) => S.Set String -> M.Map String String -> M.Map (String, String) String -> Term l -> (d, S.Set String, M.Map (String, String) String)
makeDestructorExpressions vars helperVars destructors t = 
    ((vcat doclist), S.fromList atoms, newDestructors)
    where
      (doclist, newDestructors) = foldl (\(docs,destrs) a -> let (doc, destrs') = makeDestructorExpression vars helperVars destrs t a in (docs ++ [doc], destrs')) ([], destructors) atoms
      atoms = nub $ getAtoms t

getAtoms :: (Show l) => Term l -> [String]
getAtoms t = case viewTerm t of
    Lit l     -> [show l]
    FApp _ ts -> foldl (\acc t -> acc ++ getAtoms t) [] ts

makeDestructorExpression :: (Document d, Show l) => S.Set String -> M.Map String String -> M.Map (String, String) String -> Term l -> String -> (d, M.Map (String, String) String)
makeDestructorExpression vars helperVars destructors t a = if (S.member a vars) || (head a == '\'')
                                      then (oldVarDoc, newDestructors)
                                      else (newVarDoc, newDestructors)
                                      where
                                        (var, _) = makeVariable t helperVars
                                        (destr, newDestructors) = makeDestructorName destructors t a
                                        oldVarDoc = text "let (=" <> (text $ showAtom a) <>
                                                text ") =" <-> text destr <> 
                                                text "(" <> text var <> text ") in"
                                        newVarDoc = text "let" <-> (text $ showAtom a) <->
                                                 text "=" <-> text destr <> 
                                                 text "(" <> text var <> text ") in"
