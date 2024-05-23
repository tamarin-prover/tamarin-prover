-- |
-- Copyright   : (c) 2022 Julian Biehl
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Julian Biehl <s8jubieh@stud.uni-saarland.de>
-- Portability : GHC only
--
-- Translation from multiset rewrite rules to ProVerif

module RuleTranslation
  ( loadRules
  , ppFunSym
  , sanitizeSymbol
  , replaceTrueFalse
  ) where

import Theory
import Theory.Text.Pretty

import Sapic.Exceptions
import Sapic.Facts

import Control.Exception

import Data.ByteString.Char8 qualified as BC
import Data.Char
import Data.Map qualified as M
import Data.Maybe (mapMaybe)
import Data.List as List
import Data.Set qualified as S

-- This is the function which is called from the export module. It returns a list
-- of process declarations for translated rules, a process which executes them all
-- in parallel, and the headers we need for the translation
loadRules
  :: OpenTheory
  -> ( [Doc]
     , Doc
     , ( [(String, String, String, [String])]
       , [(String, String, String, String)]
       , [(String, String, String, [String])]
       , [(String, String)]
       , [(String, String)]
       )
     )
loadRules thy = case theoryRules thy of
  []    -> ([text ""], text "", ([],[],[],[],[]))
  rules -> (ruleDocs, ruleComb, headers)
    where
      (ruleDocs, destructors) =
        foldl' (\acc@(_, destrs) r -> acc `combine2` translateOpenProtoRule r thy destrs) ([], M.empty) rules
      headers = (baseHeaders, desHeaders, frHeaders, tblHeaders, evHeaders)
      baseHeaders = [("free", "publicChannel", ":channel", [])]
      desHeaders = map makeDestructorHeader $ M.toList destructors
      (frHeaders, tblHeaders, evHeaders) = foldMap (`makeHeadersFromRule` thy) rules
      ruleNames = map (\(OpenProtoRule ruE _) -> showRuleName ruE._rInfo._preName) rules
      ruleComb = text ("( " ++ intercalate " | " (map ((++")") . ("!("++)) ruleNames) ++ " )")

------------------------------------------------------------------------------
-- Header generation
------------------------------------------------------------------------------

makeDestructorHeader :: ((String, String), String) -> (String, String, String, String)
makeDestructorHeader ((dDef, atom), dName) =
  let (s1,s2) = break (=='#') dDef
  in ("reduc", s1, dName ++ "(" ++ tail s2 ++ ") = " ++ showAtom False atom, "[private]")

makeHeadersFromRule
  :: OpenProtoRule
  -> OpenTheory
  -> ( [(String, String, String, [String])]
     , [(String, String)], [(String, String)]
     )
makeHeadersFromRule (OpenProtoRule ruE _) = makeHeadersFromProtoRule ruE

notDiffRuleActs :: Rule ProtoRuleEInfo -> [Fact LNTerm]
notDiffRuleActs ru = filter isNotDiffAnnotation ru._rActs
  where
    isNotDiffAnnotation fa =
      fa /= Fact { factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0
                 , factAnnotations = S.empty
                 , factTerms = []
                 }

makeHeadersFromProtoRule
  :: Rule ProtoRuleEInfo
  -> OpenTheory
  -> ( [(String, String, String, [String])]
     , [(String, String)]
     , [(String, String)]
     )
makeHeadersFromProtoRule ru thy = (freeHeaders, tables, events)
  where
    freeHeaders = makeFreeHeaders ru._rPrems (notDiffRuleActs ru) ru._rConcs thy
    tables = makeTableHeaders ru._rPrems ru._rConcs
    events = makeEventHeaders (notDiffRuleActs ru)

makeFreeHeaders :: [LNFact] -> [LNFact] -> [LNFact] -> OpenTheory -> [(String, String, String, [String])]
makeFreeHeaders rprems racts rconcls thy = headers
  where
    allTerms = foldMap factTerms (rprems ++ racts ++ rconcls)
    termBitstrings = foldMap searchTermForBitstrings allTerms
    lemmas = (._lFormula) <$> theoryLemmas thy
    lemmaBitstrings = foldMap searchLemmaForBitstrings lemmas
    bitstrings = termBitstrings `S.union` lemmaBitstrings
    headers = map ("free",, ":bitstring", []) $ S.toList bitstrings

searchLemmaForBitstrings :: ProtoFormula Unit2 (String, LSort) Name LVar -> S.Set String
searchLemmaForBitstrings =
  foldFormula searchAtomForBitstring (const S.empty) id (\_ p q -> p `S.union` q) (\_ _ p -> p)
  where
    searchAtomForBitstring a = case a of
      Action _ f -> foldMap searchTermForBitstrings f
      _          -> S.empty

searchTermForBitstrings :: Show l => Term l -> S.Set String
searchTermForBitstrings =
  foldMap (\l -> if (head $ show l, last $ show l) == ('\'', '\'')
                   then S.singleton (showAtom True $ show l)
                   else S.empty)


makeTableHeaders :: [LNFact] -> [LNFact] -> [(String, String)]
makeTableHeaders rprems rconcls = headers
  where
    getFactInfo (Fact tag _ ts) = (showFactName tag, length ts)
    allFactInfos = S.toList $ S.fromList (map getFactInfo rprems ++ map getFactInfo rconcls)
    tableInfos = filter (\(t, _) -> t `notElem` ["Fr", "In", "Out"]) allFactInfos
    headers = map (\(t,n) -> (t, "(" ++ intercalate ", " (replicate n "bitstring") ++ ")")) tableInfos

makeEventHeaders :: [LNFact] -> [(String, String)]
makeEventHeaders racts = headers
  where
    getFactInfo (Fact tag _ ts) = (showEventName tag, length ts)
    allFactInfos = S.toList $ S.fromList (map getFactInfo racts)
    headers = map (\(t,n) -> (t, "(" ++ intercalate ", " (replicate n "bitstring") ++ ")")) allFactInfos

------------------------------------------------------------------------------
-- Rule translation
------------------------------------------------------------------------------

translateOpenProtoRule
  :: HighlightDocument d
  => OpenProtoRule
  -> OpenTheory
  -> M.Map (String, String) String
  -> (d, M.Map (String, String) String)
translateOpenProtoRule (OpenProtoRule ruE _) thy = translateProtoRule (checkTypes ruE thy)

-- Functions with user-defined types cannot be used in rewrite rules, they
-- are currently written such that everything is treated as a bitstring
checkTypes :: Rule ProtoRuleEInfo -> OpenTheory -> Rule ProtoRuleEInfo
checkTypes ru thy = if null incorrectFunctionUsages then ru else throw $ UnsupportedTypes incorrectFunctionUsages
  where
    allFacts = ru._rPrems ++ notDiffRuleActs ru ++ ru._rConcs
    allTerms = foldMap factTerms allFacts
    incorrectFunctionUsages = S.toList . S.fromList $ foldMap (incorrectTermTypes thy) allTerms

incorrectTermTypes :: Show l => OpenTheory -> Term l -> [String]
incorrectTermTypes thy t = case viewTerm t of
  Lit _                 -> []
  FApp (NoEq (f, _)) ts -> checkFun (BC.unpack f) ++ foldMap (incorrectTermTypes thy) ts
  FApp _             ts -> foldMap (incorrectTermTypes thy) ts
  where
    functionInfo = theoryFunctionTypingInfos thy
    checkFun name =
      mapMaybe (\(_ , inTypes, outTypes) -> typeChecker name inTypes outTypes) $
      filter (\((f,_), _, _) -> BC.unpack f == name) functionInfo

    typeChecker name _ (Just _)             = Just name
    typeChecker _ [] _                      = Nothing
    typeChecker name (Nothing : ts) outType = typeChecker name ts outType
    typeChecker name (Just _ : _) _         = Just name

translateProtoRule
  :: HighlightDocument d
  => Rule ProtoRuleEInfo
  -> M.Map (String, String) String
  -> (d, M.Map (String, String) String)
translateProtoRule ru de =
  (ruleDoc, destructors)
  where
    (factsDoc,destructors) = translateRule ru._rPrems (notDiffRuleActs ru) ru._rConcs de
    ruleDoc = text "let" <-> text (showRuleName ru._rInfo._preName) <-> text "=" $-$ nest 8 factsDoc

showRuleName :: ProtoRuleName -> String
showRuleName FreshRule = "rFresh"
showRuleName (StandRule s) = 'r' : s

translateRule
  :: HighlightDocument d
  => [LNFact]
  -> [LNFact]
  -> [LNFact]
  -> M.Map (String, String) String
  -> (d, M.Map (String, String) String)
translateRule rprems racts rconcls destrs =
  -- docsX contains the expression resulting from the given translation (as an instance of Doc)
  -- varsX is a set of all variables that have appeared in the rule translation until that point
  -- varsX' is a map where the keys are the patterns, which have appeared in the rule translation until that point,
  -- and the values are their helper variables
  -- destrX is a map where the keys are terms a and t, where a given destructor extracts a from t
  -- and the values are the given destructors (which have appeared in the rule translation until that point)
  let (docs1, vars1, vars1', destr1) = translatePatterns rprems GET patternGetsFilter S.empty M.empty destrs
      (docs2, vars2) = translateNonPatterns rprems GET nonPatternGetsFilter vars1
      (docs3, vars3, _, destr3) = translatePatterns rprems IN patternInsFilter vars2 vars1' destr1
      (docs4, vars4) = translateNonPatterns rprems IN nonPatternInsFilter vars3
      (docs5, vars5) = translateNonPatterns rprems NEW isFrFact vars4
      (docs6, vars6) = translateNonPatterns racts EVENT (const True) vars5
      (docs7, vars7) = translateNonPatterns (rconcls \\ rprems) INSERT isStorage vars6
      (docs8, _) = translateNonPatterns rconcls OUT isOutFact vars7

  in (combineRuleDocs (docs1++docs2++docs3) (docs4++docs5++docs6++docs7++docs8), destr3)

combineRuleDocs :: (HighlightDocument d) => [d] -> [d] -> d
combineRuleDocs rd1 rd2 = vcat rd1 $-$ separateRuleDocs rd2
  where
    separateRuleDocs []     = text "0."
    separateRuleDocs [r]    = r <> text "."
    separateRuleDocs (r:rs) = r <> semi $-$ separateRuleDocs rs


isStorage :: LNFact -> Bool
isStorage f = not (isFrFact f || isInFact f || isOutFact f)

patternGetsFilter :: LNFact -> Bool
patternGetsFilter p = isStorage p && hasPattern p

nonPatternGetsFilter :: LNFact -> Bool
nonPatternGetsFilter p = isStorage p && not (hasPattern p)


-- | @translatePatterns facts factType filterFunction vars helperVars destructors@ applies the
--   @filterFunction@ to the @facts@ to extract those that should be translated with this call, and
--   returns a list with translations for all those facts. @factType@ indicates what type of fact
--   should be translated. @vars@ are all variables that have appeared in the current rule translation
--   up to this point. @helperVars@ maps all patterns that have already appeared in this rule
--   translation to their helper variables. @destructors@ contains the map with all destructors.
--   Also returns the updated set of variables for the current rule translation (including the ones
--   seen here for the first time), as well as the updated set of helper vars for this rule
--   translation and the updated map of destructors.
translatePatterns
  :: HighlightDocument d
  => [LNFact]
  -> FactType
  -> (LNFact -> Bool)
  -> S.Set String
  -> M.Map String String
  -> M.Map (String, String) String
  -> ([d], S.Set String, M.Map String String, M.Map (String, String) String)
translatePatterns facts factType filterFunction vars helperVars destructors =
  -- Translate all selected pattern facts, while keeping track of the variables that have already
  -- appeared and also continuously updating the maps with the helper vars and the destructors.
  foldl' (\acc@(_, vs', hvs', destrs') f -> acc `combine4` translate f vs' hvs' destrs')
    ([], vars, helperVars, destructors) patternFacts
  where
    patternFacts = filter filterFunction facts

    -- Translates one single fact, both with the core part that is either 'get' or 'in', as well
    -- as all destructor expressions to extract the content of the patterns. @vs@ is the set
    -- of variables that have already appeared in the rule translation up to this point, @hvs@
    -- is the map of helper variables (which are used to store the content of the patterns before
    -- applying the destructors), and @destrs@ is the map containing all the currently defined
    -- destructors. Also returns the updated set of variables from the current rule translation,
    -- the updated map of helper vars and the updated map of destructors, so they can be used
    -- for the translation of the next fact.
    translate prem@(Fact _ _ ts) vs hvs destrs = (factPlusDestructorsDoc, newVars, newHelperVars, newDestructors)
      where
        -- First create only the part of the translation that is 'get'
        -- or 'in', introducing new helper vars for all patterns.
        (factDoc, newHelperVars) = translatePatternFact prem factType vs hvs

        -- For each pattern term, create the list of destructor expressions
        -- that extract its contents. @literals@ contains all non-pattern
        -- terms from the current fact, which have to be remembered together
        -- with all variables from the current rule. This way, they will not
        -- be accidentally redefined when extracting them with a destructor,
        -- but instead can be prepended with '=' to check for equality. All
        -- variables which are seen in a destructor expression for the first
        -- time have to also be remembered in case they appear again in a
        -- later expression, which is why this set is also given to
        -- @makeDestructorExpressions@ and updated during the fold. The map
        -- of destructors is also updated continiuously.
        (destrDocList, newVars, newDestructors) =
          foldl' (\acc@(_, vset, des) t -> acc `combine3` makeDestructorExpressions vset newHelperVars des t)
            ([], vs `S.union` literals, destrs) patternTerms

        -- Then put all the docs together.
        factPlusDestructorsDoc = factDoc $-$ vcat destrDocList

        patternTerms = filter isPattern ts
        literals = S.fromList $ foldMap (map show . lits) $ filter (not . isPattern) ts

    combine4 (as, b, c, d) (a, b1, c1, d1) = (as ++ [a], b <> b1, c <> c1, d <> d1)
    combine3 (as, b, c)    (a, b1, c1)     = (as ++ [a], b <> b1, c <> c1)

translateNonPatterns :: HighlightDocument d => [LNFact] -> FactType -> (LNFact -> Bool) -> S.Set String -> ([d], S.Set String)
translateNonPatterns facts factType filterFunction vars =
  foldl' (\acc@(_, currVars) f -> acc `combine2` translate f currVars) ([], vars) nonPatternFacts
  where
    nonPatternFacts = filter filterFunction facts
    translate prem@(Fact _ _ ts) vs = (factDoc, atoms)
      where
        factDoc = if factType `elem` [OUT, INSERT, EVENT] && checkForNewIDs
                    then idConstructor $-$ translateFact prem factType vs
                    else translateFact prem factType vs
        atoms = S.fromList $ foldMap (map show . lits) ts
        checkForNewIDs = not (atoms `S.isSubsetOf` vs) && any (('$' ==) . head) (atoms `S.difference` vs)
        idConstructor = idExp . S.toList $ atoms `S.difference` vs
        idExp = vcat . map (\a -> text "in(publicChannel, " <> text (showAtom True a) <> text ": bitstring);") . filter (('$' ==) . head)


translateFact :: Document d => LNFact -> FactType -> S.Set String -> d
translateFact (Fact tag _ ts) factType vars = case factType of
    GET    -> text "get" <-> text (showFactName tag) <> translateTerms vars True <> text " in"
    IN     -> text "in(publicChannel," <-> translateTerm vars True (head ts)
              <> text (if head (printTerm True vars True (head ts)) == '=' then ")" else ": bitstring)")
    NEW    -> text "new" <-> translateTerm S.empty False (head ts) <> text ": bitstring"
    INSERT -> text "insert" <-> text (showFactName tag) <> translateTerms S.empty False
    OUT    -> text "out(publicChannel," <-> translateTerm S.empty False (head ts) <> text ")"
    EVENT  -> text "event" <-> text (showEventName tag) <> translateTerms S.empty False
    where
      translateTerms varSet checkEq =
        text "(" <> (fsep . punctuate comma $ map (translateTerm varSet checkEq) ts) <> text ")"

translatePatternFact
  :: Document d
  => LNFact
  -> FactType
  -> S.Set String
  -> M.Map String String
  -> (d, M.Map String String)
translatePatternFact (Fact tag _ ts) factType vars helperVars =
  (factDoc, newHelperVars)
  where
    (doclist, newHelperVars) =
      foldl' (\acc@(_, helpers) t -> acc `combine2` translatePatternTerm vars helpers t) ([], helperVars) ts
    factDoc = case factType of
      GET -> text "get" <-> text (showFactName tag) <> text "(" <> (fsep . punctuate comma $ doclist) <> text ") in"
      IN  -> text "in(publicChannel," <-> head doclist <> text ": bitstring);"
      _   -> error "translatePatternFact: fact with type other than GET or IN" -- should not happen, such facts don't require special treatment

sanitizeSymbol :: Char -> String -> String
sanitizeSymbol pre s =
  if (s `elem` reservedWords) || Data.Char.isDigit (head s)
    then pre : s
    else s

reservedWords :: [String]
reservedWords =
  [ "among", "axiom", "channel", "choice", "clauses", "const", "def", "diff"
  , "do", "elimtrue", "else", "equation", "equivalence", "event", "expand", "fail", "for"
  , "forall", "foreach", "free", "fun", "get", "if", "implementation", "in", "inj-event"
  , "insert", "lemma", "let", "letfun", "letproba", "new", "noninterf", "noselect", "not"
  , "nounif", "or", "otherwise", "out", "param", "phase", "pred", "proba", "process"
  , "proof", "public_vars", "putbegin", "query", "reduc", "restriction", "secret", "select"
  , "set", "suchthat", "sync", "table", "then", "type", "weaksecret", "yield"
  ]

showAtom :: Bool -> String -> String
showAtom sanitized a = case head a of
  '~'  -> sanitize . replaceDots $ tail a
  '$'  -> sanitize . replaceDots $ tail a
  '\'' -> sanitizeName $ 's' : (replaceDots . init $ tail a)
  _    -> sanitize $ replaceDots a
  where
    replaceDots = map (\c -> if c == '.' then '_' else c)
    sanitize = if sanitized then sanitizeSymbol 'a' else ("var_" ++)
    sanitizeName = if sanitized then id else ("var_" ++)

ppFunSym :: BC.ByteString -> String
ppFunSym f = replaceTrueFalse . sanitizeSymbol 'f' $ BC.unpack f

replaceTrueFalse :: String -> String
replaceTrueFalse "true" = "okay"
replaceTrueFalse "false" = "notokay"
replaceTrueFalse s = s

showFactName :: FactTag -> String
showFactName tag = if factTagName tag `elem` ["Fr", "In", "Out"]
                     then factTagName tag
                     else 't' : factTagName tag

showEventName :: FactTag -> String
showEventName tag = 'e' : factTagName tag

translateTerm :: (Document d, Show l) => S.Set String -> Bool -> Term l -> d
translateTerm vars checkEq t = text $ printTerm True vars checkEq t

printTerm :: (Show l) => Bool -> S.Set String -> Bool -> Term l -> String
printTerm sanitizeAtoms vars checkEq t = case viewTerm t of
  Lit l | checkEq && (S.member (show l) vars || head (show l) == '\'') -> '=' : showAtom sanitizeAtoms (show l)
  Lit l                                         -> showAtom sanitizeAtoms $ show l
  FApp (AC Mult)     ts                         -> printFuncApp "mult" ts
  FApp (AC Union)    ts                         -> printFuncApp "union" ts
  FApp (AC Xor)      ts                         -> printFuncApp "xor" ts
  FApp (AC NatPlus)  ts                         -> printFuncApp "plus" ts
  FApp (NoEq (f, _)) ts | BC.unpack f == "pair" -> printFuncApp "" ts
  FApp (NoEq (f, _)) ts                         -> ppFunSym f ++ printTermsList ts
  FApp (C EMap)      ts                         -> "em" ++ printTermsList ts
  FApp List          ts                         -> printTermsList ts
  where
    printTermsList ts = "(" ++ intercalate ", " (map (printTerm sanitizeAtoms vars checkEq) ts) ++ ")"
    printFuncApp acOp [t1,t2] = acOp ++ "(" ++ printTerm sanitizeAtoms vars checkEq t1 ++ ", " ++ printTerm sanitizeAtoms vars checkEq t2 ++ ")"
    printFuncApp acOp (tr:trs) = acOp ++ "(" ++ printTerm sanitizeAtoms vars checkEq tr ++ ", " ++ printFuncApp acOp trs ++ ")"
    printFuncApp _ [] = []


translatePatternTerm
  :: (Document d, Show l)
  => S.Set String
  -> M.Map String String
  -> Term l
  -> (d, M.Map String String)
translatePatternTerm vars helperVars t = case viewTerm t of
  Lit l | S.member (show l) vars || head (show l) == '\'' ->
    (text "=" <> (text . showAtom True $ show l), helperVars)
  Lit l ->
    (text . showAtom True $ show l, helperVars)
  _ ->
    (varDoc, newHelperVars)
    where
      (newVar, newHelperVars) = makeVariable t helperVars
      varDoc = text newVar

makeDestructorDefinition :: (Show l) => Term l -> String
makeDestructorDefinition t =
  "forall " ++ intercalate ", " (map (++":bitstring") atoms) ++ ";#" ++ printTerm False S.empty False t
  where
    atoms = map (showAtom False) . S.toList . S.fromList $ map show $ lits t

makeVariable :: (Show l) => Term l -> M.Map String String -> (String, M.Map String String)
makeVariable t varMap = case M.lookup (printTerm True S.empty False t) varMap of
    Just v  -> (v, M.empty)
    Nothing -> let newVar = "helperVar" ++ show (M.size varMap)
                   newMap = M.singleton (printTerm True S.empty False t) newVar
               in (newVar, newMap)

-- | @makeDestructorName dMap t a@ looks up if a destructor that extracts @a@ from @t@ already exists
--   in map @dMap@, and depending on the result returns an empty map (nothing to update with) or a
--   single map entry to update the map with. Note that for the mapping we don't just print the term to
--   a string, but use @makeDestructorDefinition@ to also prepend it with declarations of all its
--   variables. We need those later when we want to define the destructor, and create them right here
--   because here we can still extract the variables from the actual term, while later we can only
--   access the term as a string. (Terms are stringified for mapping because in their raw form they
--   are not orderable, i.e. can not be used in a map.)
makeDestructorName
  :: Show l
  => M.Map (String, String) String
  -> Term l
  -> String
  -> (String, M.Map (String, String) String)
makeDestructorName dMap t a = case M.lookup (makeDestructorDefinition t,a) dMap of
    Just d  -> (d, M.empty)
    Nothing -> let newDestructor = "g_" ++ showAtom False a ++ "_" ++ show (M.size dMap)
                   newMap = M.singleton (makeDestructorDefinition t,a) newDestructor
               in (newDestructor, newMap)

makeDestructorExpressions
  :: (Document d, Show l, Ord l)
  => S.Set String
  -> M.Map String String
  -> M.Map (String, String) String
  -> Term l
  -> (d, S.Set String, M.Map (String, String) String)
makeDestructorExpressions vars helperVars destructors t =
  (vcat doclist, S.fromList atoms, newDestructors)
  where
    (doclist, newDestructors) =
      foldl' (\acc@(_,destrs) a -> acc `combine2` makeDestructorExpression vars helperVars destrs t a)
        ([], destructors) atoms
    atoms = nub $ map show $ lits t

makeDestructorExpression
  :: (Document d, Show l)
  => S.Set String
  -> M.Map String String
  -> M.Map (String, String) String
  -> Term l
  -> String
  -> (d, M.Map (String, String) String)
makeDestructorExpression vars helperVars destructors t a =
  (varDoc, newDestructors)
  where
    (var, _) = makeVariable t helperVars
    (destr, newDestructors) = makeDestructorName destructors t a
    varDoc =
      (if S.member a vars || head a == '\''
         then
           text "let (=" <> text (showAtom True a) <>
           text ") ="
         else
           text "let" <-> text (showAtom True a) <->
           text "="
      ) <-> text destr <> text "(" <> text var <> text ") in"

combine2 :: Semigroup b => ([a],b) -> (a,b) -> ([a], b)
combine2 (as, b) (a, b1) = (as++[a], b <> b1)
