-- |
-- Copyright   : (c) 2022 Julian Biehl
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Julian Biehl <s8jubieh@stud.uni-saarland.de>
-- Portability : GHC only
--
-- Translation from multiset rewrite rules to ProVerif
module Export.ProVerif.Rule
  ( loadRules,
    translateEmbeddedRuleAction,
    ppFunSym,
    replaceTrueFalse,
    makeEventHeaders,
    multisetTheory
  )
where

import Control.Exception
import Data.ByteString.Char8 qualified as BC
import Data.List as List
import Data.Map qualified as M
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import Data.Set qualified as S
import Extension.Data.Label qualified as L
import Export.Name
import Export.ProVerif.Header
import Export.ProVerif.Instrumentation (InstrumentationPlan (..))
import Export.Types (translationFail, translationInvariantFail)
import Sapic.Exceptions
import Sapic.Facts
import Theory
import Theory.Module
import Theory.Text.Parser
import Theory.Text.Pretty
import TheoryObject (theoryMacros)

-- | Instrumentation carried into a single rule's translation: the theory
-- plan plus the rule's allocated rule-id variable, if any.
data RuleInstrumentation = RuleInstrumentation
  { riPlan :: InstrumentationPlan,
    riRuleIdName :: Maybe String
  }

-- | No instrumentation, for embedded rule actions.
emptyRuleInstrumentation :: RuleInstrumentation
emptyRuleInstrumentation =
  RuleInstrumentation (InstrumentationPlan "" S.empty S.empty) Nothing

loadRules :: InstrumentationPlan -> OpenTheory -> ModuleType -> ([Doc], Doc, S.Set ProVerifHeader)
loadRules plan thy m = case theoryRules thy of
  [] -> ([text ""], text "", S.empty)
  rules -> (ruleDocs, ruleComb, headers)
    where
      completionEvent = plan.instrumentationCompletionEvent
      ruleIdEvents = plan.instrumentationRuleIdEvents
      completionTriggerEvents = plan.instrumentationCompletionTriggers
      (ruleDocs, destructors) =
        foldl'
          (\acc@(_, destrs) r ->
             acc `accumulateResult`
               translateOpenProtoRule plan ruleIdNames r thy destrs)
          ([], M.empty)
          rulesMod
      headers =
        S.fromList (baseHeaders : desHeaders)
          `S.union` ruleHeaders
          `S.union` completionHeader
      baseHeaders = Sym "free" "publicChannel" ":channel" []
      desHeaders = map makeDestructorHeader $ M.toList destructors
      ruleHeaders = foldMap (\r -> makeHeadersFromRule ruleIdEvents r thy) rulesMod
      completionHeader
        | S.null completionTriggerEvents = S.empty
        | otherwise =
            S.singleton
              (HEvent ('e' : completionEvent) "(bitstring)")
      ruleNames = map (\(OpenProtoRule ruE _) -> showRuleName ruE._rInfo._preName) rulesMod
      ruleIdNames = snd $ foldl' allocateRuleId (initialAllocator, M.empty) ruleNames
      allocateRuleId (allocator, names) targetRuleName =
        let (TargetVariable allocated, allocator') =
              allocateVariable ("rid_" ++ targetRuleName) allocator
         in (allocator', M.insert targetRuleName allocated names)
      initialAllocator =
        reserveNames VariableNamespace sourceVariableNames emptyNameAllocator
      sourceVariableNames =
        S.fromList
          [ sanitizeSymbol 'a' name
          | OpenProtoRule rule _ <- rulesMod,
            fact <- rule._rPrems ++ notDiffRuleActs rule ++ rule._rConcs,
            LVar name _ _ <- frees fact
          ]
      ruleComb = text ("( " ++ intercalate " | " (map ((++ ")") . ("!(" ++)) ruleNames) ++ " )")
      rulesMod = map (\(OpenProtoRule ruE rusAC) -> OpenProtoRule (applyMacroInRule (theoryMacros thy) ruE) rusAC) $ case m of
        ModuleProVerif -> rules
        _ -> translationInvariantFail "Rule translation was invoked for an incompatible output module."

translateEmbeddedRuleAction ::
  (HighlightDocument d) =>
  S.Set String ->
  [LNFact] ->
  [LNFact] ->
  [LNFact] ->
  (d, S.Set ProVerifHeader, Bool)
translateEmbeddedRuleAction matchedVars rprems racts rconcls =
  (ruleDoc, headers, hasTailDocs)
  where
    (headDocs, tailDocs, destructors) =
      translateRuleDocs emptyRuleInstrumentation matchedVars rprems racts rconcls M.empty
    hasTailDocs = not (null tailDocs)
    ruleDoc =
      if hasTailDocs
        then combineActionDocs headDocs tailDocs
        else vcat headDocs
    freeHeaders = makeFreeHeadersFromFacts rprems racts rconcls
    tableHeaders = makeTableHeaders rprems rconcls
    eventHeaders = makeEventHeaders S.empty racts
    destructorHeaders = S.fromList $ map makeDestructorHeader (M.toList destructors)
    headers =
      S.unions
        [ S.singleton (Sym "free" "publicChannel" ":channel" []),
          freeHeaders,
          tableHeaders,
          eventHeaders,
          destructorHeaders
        ]

-- Multiset semantics
-- Steps:
-- 1. For each non-persistent and non-output fact, create a fresh varible.
--    - Add to each fact in conclusion
--    - Add fresh facts to premise
-- 2. For each fact in the premise that is non-persistent, non-fresh, and not the input fact, add stamp values.
--  - For each of these facts add a DistinctFact event with the same arguments ensuring that they are only used once.
-- 3. Add static restriction to theory.

-- | Apply multisetSemantics to all rules in an OpenTheory
mapRulesWithMultisetSemantics :: OpenTheory -> OpenTheory
mapRulesWithMultisetSemantics =
  L.modify thyItems (map updateRule)
  where
    updateRule (RuleItem (OpenProtoRule ruE ruAC)) =
      RuleItem (OpenProtoRule (multisetSemantics ruE) ruAC)
    updateRule item = item

multisetTheory :: OpenTheory -> OpenTheory
multisetTheory thy =
  let thy' = mapRulesWithMultisetSemantics thy
      hasDistinctFact =
        any ruleHasDistinctFact
          [ ruE
          | RuleItem (OpenProtoRule ruE _) <- L.get thyItems thy'
          ]
   in if hasDistinctFact
        then case addRestriction (parseAndConvertRestriction resDistinctFact) thy' of
               Just thy'' -> thy''
               Nothing    -> translationInvariantFail "Could not add the generated multiset restriction to the theory."
        else thy'

-- Helper to check if a rule has a DistinctFact action
ruleHasDistinctFact :: Rule i -> Bool
ruleHasDistinctFact ru =
  any (\f -> factTagName (factTag f) == "DistinctFact") (ru._rActs)

resDistinctFact :: String
resDistinctFact =
  unlines
    [ "restriction DistinctFact:",
      "\"All x #i #j. DistinctFact(x)@i & DistinctFact(x)@j ==> #i = #j\""
    ]

parseAndConvertRestriction :: String -> Restriction
parseAndConvertRestriction s =
  case parseRestriction s of
    Right (Restriction name synFormula _) ->
      case toLNFormula synFormula of
        Just lnFormula -> Restriction name lnFormula Nothing
        Nothing -> translationInvariantFail "Could not convert the generated multiset restriction."
    _ -> translationInvariantFail $ "Could not parse the generated multiset restriction: " ++ s

multisetSemantics :: HasRuleName (Rule i) => Rule i -> Rule i
multisetSemantics r = r
  { _rPrems = freshFacts ++ statPrems
  , _rActs = distinctActions ++ r._rActs
  , _rConcs = statConcs
  }
  where
    statifyConcs :: String -> [LNFact] -> ([LNFact], [(FactTag, LNTerm)])
    statifyConcs prefix facts =
      let (_, factsWithVars) = mapAccumL (statify prefix) M.empty facts
          (facts', vars) = unzip factsWithVars
      in (facts', catMaybes vars)

    statifyPrems :: String -> [LNFact] -> ([LNFact], [(FactTag, LNTerm, [LNTerm])])
    statifyPrems prefix facts =
      let (_, factsWithVars) = mapAccumL (statify prefix) M.empty facts
          facts' = map fst factsWithVars
          distincts = [ (tag, fresh, factTerms fact)
                      | (fact, Just (tag, fresh)) <- factsWithVars ]
      in (facts', distincts)

    statify :: String -> M.Map String Int -> LNFact -> (M.Map String Int, (LNFact, Maybe (FactTag, LNTerm)))
    statify prefix counts f
      | isFrFact f || isInFact f || isOutFact f || isPersistentFact f = (counts, (f, Nothing))
      | Fact tag ann ts <- f =
          let name = factTagName tag
              idx  = M.findWithDefault 0 name counts
              counts' = M.insert name (idx + 1) counts
              fresh = mkFreshTerm prefix name (toInteger idx)
          in (counts', (Fact tag ann (fresh : ts), Just (tag, fresh)))

    (statConcs, freshVars) = statifyConcs "R" r._rConcs
    (statPrems, distinctVars) = statifyPrems "L" r._rPrems

    freshFacts = map (mkFreshFact . snd) freshVars

    distinctActions = [ Fact (ProtoFact Linear "DistinctFact" 0) S.empty [termsToPair args]
                      | (_, _, args) <- distinctVars ]

    mkFreshTerm prefix n idx = LIT $ Var $ LVar ("st" ++ prefix ++ "_" ++ n) LSortFresh idx
    mkFreshFact fv = Fact FreshFact S.empty [fv]

    termsToPair :: [LNTerm] -> LNTerm
    termsToPair []     = translationFail "Multiset export does not support a zero-arity linear fact."
    termsToPair [x]    = x
    termsToPair (x:xs) = fAppPair (x, termsToPair xs)


------------------------------------------------------------------------------
-- Header generation
------------------------------------------------------------------------------

makeDestructorHeader :: ((String, String), String) -> ProVerifHeader
makeDestructorHeader ((dDef, atom), dName) =
  case break (== '#') dDef of
    (declarations, _ : body) ->
      Eq "reduc" declarations (dName ++ "(" ++ body ++ ") = " ++ showAtom False atom) "[private]"
    _ -> translationInvariantFail "A generated destructor definition has no body."

makeHeadersFromRule :: S.Set String -> OpenProtoRule -> OpenTheory -> S.Set ProVerifHeader
makeHeadersFromRule ruleIdEvents (OpenProtoRule ruE _) = makeHeadersFromProtoRule ruleIdEvents ruE

notDiffRuleActs :: Rule ProtoRuleEInfo -> [Fact LNTerm]
notDiffRuleActs ru = filter isNotDiffAnnotation ru._rActs
  where
    isNotDiffAnnotation fa =
      fa
        /= Fact
          { factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0,
            factAnnotations = S.empty,
            factTerms = []
          }

makeHeadersFromProtoRule :: S.Set String -> Rule ProtoRuleEInfo -> OpenTheory -> S.Set ProVerifHeader
makeHeadersFromProtoRule ruleIdEvents ru thy = S.unions [freeHeaders, tables, events]
  where
    freeHeaders = makeFreeHeaders ru._rPrems (notDiffRuleActs ru) ru._rConcs thy
    tables = makeTableHeaders ru._rPrems ru._rConcs
    events = makeEventHeaders ruleIdEvents (notDiffRuleActs ru)

makeFreeHeaders :: [LNFact] -> [LNFact] -> [LNFact] -> OpenTheory -> S.Set ProVerifHeader
makeFreeHeaders rprems racts rconcls thy =
  makeFreeHeadersFromFacts rprems racts rconcls
    `S.union` S.map (\x -> Sym "free" x ":bitstring" []) lemmaBitstrings
  where
    lemmaBitstrings = foldMap (searchLemmaForBitstrings . (._lFormula)) (theoryLemmas thy)

makeFreeHeadersFromFacts :: [LNFact] -> [LNFact] -> [LNFact] -> S.Set ProVerifHeader
makeFreeHeadersFromFacts rprems racts rconcls =
  S.map (\x -> Sym "free" x ":bitstring" []) (freeBitstringsFromFacts rprems racts rconcls)

freeBitstringsFromFacts :: [LNFact] -> [LNFact] -> [LNFact] -> S.Set String
freeBitstringsFromFacts rprems racts rconcls = foldMap searchTermForBitstrings allTerms
  where
    allTerms = foldMap factTerms (rprems ++ racts ++ rconcls)

searchLemmaForBitstrings :: ProtoFormula Unit2 (String, LSort) Name LVar -> S.Set String
searchLemmaForBitstrings =
  foldFormula searchAtomForBitstring (const S.empty) id (\_ p q -> p `S.union` q) (\_ _ p -> p)
  where
    searchAtomForBitstring a = case a of
      Action _ f -> foldMap searchTermForBitstrings f
      _ -> S.empty

searchTermForBitstrings :: (Show l) => Term l -> S.Set String
searchTermForBitstrings =
  foldMap
    ( \l ->
        if isQuoted (show l)
          then S.singleton (showAtom True (show l))
          else S.empty
    )
  where
    isQuoted ('\'' : rest) = not (null rest) && last rest == '\''
    isQuoted _ = False

makeTableHeaders :: [LNFact] -> [LNFact] -> S.Set ProVerifHeader
makeTableHeaders rprems rconcls =
  S.map toTable
    . S.filter stateFact
    . S.map getFactInfo
    $ S.fromList (rprems ++ rconcls)
  where
    getFactInfo (Fact tag _ ts) = (showFactName tag, length ts)
    stateFact (t, _) = t `notElem` ["Fr", "In", "Out"]
    toTable (t, n) = Table t ("(" ++ intercalate ", " (replicate n "bitstring") ++ ")")

makeEventHeaders :: Ord a => S.Set String -> [Fact a] -> S.Set ProVerifHeader
makeEventHeaders ruleIdEvents racts =
  S.map toHEvent
    . S.map getFactInfo
    $ S.fromList racts
  where
    getFactInfo (Fact tag _ ts) = (factTagName tag, length ts)
    toHEvent (name, n) =
      let extra = if name `S.member` ruleIdEvents then 1 else 0
          eventName = showEventNameFromName name
          arity = n + extra
      in HEvent eventName ("(" ++ intercalate ", " (replicate arity "bitstring") ++ ")")

showEventNameFromName :: String -> String
showEventNameFromName tag = 'e' : tag

------------------------------------------------------------------------------
-- Rule translation
------------------------------------------------------------------------------

translateOpenProtoRule ::
  (HighlightDocument d) =>
  InstrumentationPlan ->
  M.Map String String ->
  OpenProtoRule ->
  OpenTheory ->
  M.Map (String, String) String ->
  (d, M.Map (String, String) String)
translateOpenProtoRule plan ruleIdNames (OpenProtoRule ruE _) thy =
  translateProtoRule plan ruleIdNames (checkTypes ruE thy)

-- Functions with user-defined types cannot be used in rewrite rules, they
-- are currently written such that everything is treated as a bitstring
checkTypes :: Rule ProtoRuleEInfo -> OpenTheory -> Rule ProtoRuleEInfo
checkTypes ru thy = if null incorrectFunctionUsages then ru else throw $ UnsupportedTypes incorrectFunctionUsages
  where
    allFacts = ru._rPrems ++ notDiffRuleActs ru ++ ru._rConcs
    allTerms = foldMap factTerms allFacts
    incorrectFunctionUsages = S.toList . S.fromList $ foldMap (incorrectTermTypes thy) allTerms

incorrectTermTypes :: (Show l) => OpenTheory -> Term l -> [String]
incorrectTermTypes thy t = case viewTerm t of
  Lit _ -> []
  FApp (NoEq (f, _)) ts -> checkFun (BC.unpack f) ++ foldMap (incorrectTermTypes thy) ts
  FApp (AC (ACfct (f, _))) ts -> checkFun (BC.unpack f) ++ foldMap (incorrectTermTypes thy) ts
  FApp _ ts -> foldMap (incorrectTermTypes thy) ts
  where
    functionInfo = theoryFunctionTypingInfos thy
    checkFun name =
      mapMaybe (\(_, inTypes, outTypes) -> typeChecker name inTypes outTypes) $
        filter filterfct functionInfo
        where
          filterfct (NoEqUser (f,_),_,_) = BC.unpack f == name
          filterfct (ACfctUser (f,_),_,_) = BC.unpack f == name

    typeChecker name _ (Just _) = Just name
    typeChecker _ [] _ = Nothing
    typeChecker name (Nothing : ts) outType = typeChecker name ts outType
    typeChecker name (Just _ : _) _ = Just name

translateProtoRule ::
  (HighlightDocument d) =>
  InstrumentationPlan ->
  M.Map String String ->
  Rule ProtoRuleEInfo ->
  M.Map (String, String) String ->
  (d, M.Map (String,String) String)
translateProtoRule plan ruleIdNames ru de =
  (ruleDoc, destructors)
  where
    rname = showRuleName ru._rInfo._preName
    ruleIdName =
      fromMaybe
        (translationInvariantFail ("missing allocated rule-ID name for " ++ rname))
        (M.lookup rname ruleIdNames)
    (factsDoc, destructors) =
      translateRule
        (RuleInstrumentation plan (Just ruleIdName))
        ru._rPrems
        (notDiffRuleActs ru)
        ru._rConcs
        de
    ruleDoc = text "let" <-> text rname <-> text "=" $-$ nest 8 factsDoc

showRuleName :: ProtoRuleName -> String
showRuleName FreshRule = "rFresh"
showRuleName (StandRule s) = 'r' : s

translateRule ::
  (HighlightDocument d) =>
  RuleInstrumentation ->
  [LNFact] ->
  [LNFact] ->
  [LNFact] ->
  M.Map (String, String) String ->
  (d, M.Map (String, String) String)
translateRule instrumentation rprems racts rconcls destrs =
  let (headDocs, tailDocs, newDestrs) =
        translateRuleDocs instrumentation S.empty rprems racts rconcls destrs
   in (combineRuleDocs headDocs tailDocs, newDestrs)

translateRuleDocs ::
  (HighlightDocument d) =>
  RuleInstrumentation ->
  S.Set String ->
  [LNFact] ->
  [LNFact] ->
  [LNFact] ->
  M.Map (String, String) String ->
  ([d], [d], M.Map (String, String) String)
translateRuleDocs instrumentation initialVars rprems racts rconcls destrs =
  -- docsX contains the expression resulting from the given translation (as an instance of Doc)
  -- varsX is a set of all variables that have appeared in the rule translation until that point
  -- varsX' is a map where the keys are the patterns, which have appeared in the rule translation until that point,
  -- and the values are their helper variables
  -- destrX is a map where the keys are terms a and t, where a given destructor extracts a from t
  -- and the values are the given destructors (which have appeared in the rule translation until that point)
  let completionEvent = instrumentation.riPlan.instrumentationCompletionEvent
      ruleIdEvents = instrumentation.riPlan.instrumentationRuleIdEvents
      completionTriggerEvents = instrumentation.riPlan.instrumentationCompletionTriggers
      ruleIdName = fromMaybe "" instrumentation.riRuleIdName
      ruleNeedsCompletion =
        any
          (\fact -> factTagName (factTag fact) `S.member` completionTriggerEvents)
          racts
      ruleUsesRuleId =
        ruleNeedsCompletion
          || any
            (\fact -> factTagName (factTag fact) `S.member` ruleIdEvents)
            racts
      ruleIdDoc = text "new" <-> text ruleIdName <> text ": bitstring"
      completionDoc =
        text "event"
          <-> text ('e' : completionEvent)
          <> parens (text ruleIdName)
      (docs1, vars1, vars1', destr1) = translatePatterns rprems GET patternGetsFilter initialVars M.empty destrs
      (docs2, vars2) = translateNonPatterns rprems GET nonPatternGetsFilter vars1
      (docs3, vars3, _, destr3) = translatePatterns rprems IN patternInsFilter vars2 vars1' destr1
      (docs4, vars4) = translateNonPatterns rprems IN nonPatternInsFilter vars3
      (docs5, vars5) = translateNonPatterns rprems NEW isFrFact vars4
      -- Actions from embedded restrictions (_restrict(...)) as well as Eq, Neq need to come before all other actions.
      -- The restriction holds only for variables after the restriction action.
      (docs6, vars6) =
        if ruleUsesRuleId
          then translateNonPatternsWithRuleId ruleIdEvents ruleIdName (sortActionsByPriority racts) EVENT (const True) vars5
          else translateNonPatterns (sortActionsByPriority racts) EVENT (const True) vars5
      (docs7, vars7) = translateNonPatterns (rconcls \\ rprems) INSERT isStorage vars6
      (docs8, _) = translateNonPatterns rconcls OUT isOutFact vars7
      rulePrefixDocs = [ruleIdDoc | ruleUsesRuleId]
      completionDocs = [completionDoc | ruleNeedsCompletion]
      headDocs = docs1 ++ docs2 ++ docs3
      tailDocs =
        rulePrefixDocs
          ++ docs4
          ++ docs5
          ++ docs6
          ++ completionDocs
          ++ docs7
          ++ docs8
   in (headDocs, tailDocs, destr3)

-- | Put embedded restrictions first, equality checks second, and all remaining
-- actions last. 'partition' preserves the source order within each group.
sortActionsByPriority :: [LNFact] -> [LNFact]
sortActionsByPriority facts = restrictionFacts ++ eqNeqFacts ++ otherFacts
  where
    (restrictionFacts, nonRestrictionFacts) = partition (hasRstrPrefix restrPrefix) facts
    (eqNeqFacts, otherFacts) = partition isEqOrNeqFact nonRestrictionFacts

    hasRstrPrefix :: String -> LNFact -> Bool
    hasRstrPrefix prefix fact = prefix `isPrefixOf` factTagName (factTag fact)

    isEqOrNeqFact :: LNFact -> Bool
    isEqOrNeqFact fact = factTagName (factTag fact) `elem` equalityActionNames

    -- "Eq" is produced by SAPIC. Keep the corresponding negative name and
    -- the long-form spellings for hand-written embedded MSR actions.
    equalityActionNames = ["Eq", "Neq", "Equal", "Unequal"]

combineActionDocs :: (HighlightDocument d) => [d] -> [d] -> d
combineActionDocs rd1 rd2 = vcat rd1 $-$ separateActionDocs rd2
  where
    separateActionDocs [r] = r
    separateActionDocs (r : rs) = r <> semi $-$ separateActionDocs rs
    separateActionDocs [] = text ""

combineRuleDocs :: (HighlightDocument d) => [d] -> [d] -> d
combineRuleDocs rd1 rd2 = vcat rd1 $-$ separateRuleDocs rd2
  where
    separateRuleDocs [] = text "0."
    separateRuleDocs [r] = r <> text "."
    separateRuleDocs (r : rs) = r <> semi $-$ separateRuleDocs rs

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
translatePatterns ::
  (HighlightDocument d) =>
  [LNFact] ->
  FactType ->
  (LNFact -> Bool) ->
  S.Set String ->
  M.Map String String ->
  M.Map (String, String) String ->
  ([d], S.Set String, M.Map String String, M.Map (String, String) String)
translatePatterns facts factType filterFunction vars helperVars destructors =
  -- Translate all selected pattern facts, while keeping track of the variables that have already
  -- appeared and also continuously updating the maps with the helper vars and the destructors.
  foldl'
    (\acc@(_, vs', hvs', destrs') f -> acc `accumulateWith4` translate f vs' hvs' destrs')
    ([], vars, helperVars, destructors)
    patternFacts
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
          foldl'
            (\acc@(_, vset, des) t -> acc `accumulateWith3` makeDestructorExpressions vset newHelperVars des t)
            ([], vs `S.union` literals, destrs)
            patternTerms

        -- Then put all the docs together.
        factPlusDestructorsDoc = factDoc $-$ vcat destrDocList

        patternTerms = filter isPattern ts
        literals = S.fromList $ foldMap (map show . lits) $ filter (not . isPattern) ts

    -- | Accumulate result with 4 semigroup values
    accumulateWith4 (as, b, c, d) (a, b1, c1, d1) = (as ++ [a], b <> b1, c <> c1, d <> d1)
    -- | Accumulate result with 3 semigroup values
    accumulateWith3 (as, b, c) (a, b1, c1) = (as ++ [a], b <> b1, c <> c1)

-- | Like translateNonPatterns but includes a rule ID as the first argument to EVENT facts
translateNonPatternsWithRuleId :: (HighlightDocument d) => S.Set String -> String -> [LNFact] -> FactType -> (LNFact -> Bool) -> S.Set String -> ([d], S.Set String)
translateNonPatternsWithRuleId ruleIdEvents ruleIdName facts factType filterFunction vars =
  foldl' (\acc@(_, currVars) f -> acc `accumulateResult` translate f currVars) ([], vars) nonPatternFacts
  where
    nonPatternFacts = filter filterFunction facts
    translate prem@(Fact tag _ ts) vs = (factDoc, atoms)
      where
        factName = factTagName tag
        useRuleId = factType == EVENT && factName `S.member` ruleIdEvents
        factDoc =
          if factType `elem` [OUT, INSERT, EVENT] && checkForNewIDs
            then idConstructor $-$ renderFact
            else renderFact
        renderFact =
          if useRuleId
            then translateFactWithRuleId prem factType vs ruleIdName
            else translateFact prem factType vs
        atoms = S.fromList $ foldMap (map show . lits) ts
        checkForNewIDs = not (atoms `S.isSubsetOf` vs) && any (startsWith '$') (atoms `S.difference` vs)
        idConstructor = idExp . S.toList $ atoms `S.difference` vs
        idExp = vcat . map (\a -> text "in(publicChannel, " <> text (showAtom True a) <> text ": bitstring);") . filter (startsWith '$')

translateNonPatterns :: (HighlightDocument d) => [LNFact] -> FactType -> (LNFact -> Bool) -> S.Set String -> ([d], S.Set String)
translateNonPatterns = translateNonPatternsWithRuleId S.empty ""

-- | Like translateFact but prepends the rule ID to EVENT fact arguments. Only
-- EVENT facts carry a rule ID; other fact types render as in 'translateFact'.
translateFactWithRuleId :: (Document d) => LNFact -> FactType -> S.Set String -> String -> d
translateFactWithRuleId fact@(Fact tag _ ts) factType vars ruleIdName = case factType of
  EVENT -> text "event" <-> text (showEventName tag) <> termsWithRuleId
  _ -> translateFact fact factType vars
  where
    termsWithRuleId =
      text "(" <> text ruleIdName <> (if null ts then text "" else comma <-> (fsep . punctuate comma $ map (translateTerm S.empty False) ts)) <> text ")"

translateFact :: (Document d) => LNFact -> FactType -> S.Set String -> d
translateFact (Fact tag _ ts) factType vars = case factType of
  GET -> text "get" <-> text (showFactName tag) <> translateTerms vars True <> text " in"
  IN ->
    text "in(publicChannel," <-> translateTerm vars True firstTerm
      <> text (if startsWith '=' (printTerm True vars True firstTerm) then ")" else ": bitstring)")
  NEW -> text "new" <-> translateTerm S.empty False firstTerm <> text ": bitstring"
  INSERT -> text "insert" <-> text (showFactName tag) <> translateTerms S.empty False
  OUT -> text "out(publicChannel," <-> translateTerm S.empty False firstTerm <> text ")"
  EVENT -> text "event" <-> text (showEventName tag) <> translateTerms S.empty False
  where
    translateTerms varSet checkEq =
      text "(" <> (fsep . punctuate comma $ map (translateTerm varSet checkEq) ts) <> text ")"
    firstTerm = case ts of
      term : _ -> term
      [] -> translationFail "Input, output, and fresh facts require one term."

translatePatternFact ::
  (Document d) =>
  LNFact ->
  FactType ->
  S.Set String ->
  M.Map String String ->
  (d, M.Map String String)
translatePatternFact (Fact tag _ ts) factType vars helperVars =
  (factDoc, newHelperVars)
  where
    (doclist, newHelperVars) =
      foldl' (\acc@(_, helpers) t -> acc `accumulateResult` translatePatternTerm vars helpers t) ([], helperVars) ts
    factDoc = case factType of
      GET -> text "get" <-> text (showFactName tag) <> text "(" <> (fsep . punctuate comma $ doclist) <> text ") in"
      IN -> case doclist of
        document : _ -> text "in(publicChannel," <-> document <> text ": bitstring);"
        [] -> translationFail "An input pattern requires one term."
      _ -> translationInvariantFail "Pattern translation received a fact other than get or input."

startsWith :: Char -> String -> Bool
startsWith expected (actual : _) = expected == actual
startsWith _ [] = False

showAtom :: Bool -> String -> String
showAtom sanitized atom = case atom of
  '~' : rest -> sanitize (replaceDots rest)
  '$' : rest -> sanitize (replaceDots rest)
  '\'' : rest -> sanitizeName ('v' : replaceDots (dropLast rest))
  _ : _ -> sanitize (replaceDots atom)
  [] -> translationFail "Cannot translate an empty atom name."
  where
    replaceDots = map (\c -> if c == '.' then '_' else c)
    sanitize = if sanitized then sanitizeSymbol 'a' else ("var_" ++)
    sanitizeName = if sanitized then id else ("var_" ++)
    dropLast [] = []
    dropLast xs = init xs

ppFunSym :: BC.ByteString -> String
ppFunSym f = replaceTrueFalse . sanitizeSymbol 'f' $ BC.unpack f

replaceTrueFalse :: String -> String
replaceTrueFalse "true" = "okay"
replaceTrueFalse "false" = "notokay"
replaceTrueFalse s = s

showFactName :: FactTag -> String
showFactName tag =
  if factTagName tag `elem` ["Fr", "In", "Out"]
    then factTagName tag
    else 't' : factTagName tag

showEventName :: FactTag -> String
showEventName = showEventNameFromName . factTagName

translateTerm :: (Document d, Show l) => S.Set String -> Bool -> Term l -> d
translateTerm vars checkEq t = text $ printTerm True vars checkEq t

printTerm :: (Show l) => Bool -> S.Set String -> Bool -> Term l -> String
printTerm sanitizeAtoms vars checkEq t = case viewTerm t of
  Lit _ | checkEq && (S.member rendered vars || startsWith '\'' rendered) -> '=' : showAtom sanitizeAtoms rendered
  Lit l -> showAtom sanitizeAtoms $ show l
  FApp (AC Mult) ts -> printFuncApp "mult" ts
  FApp (AC Union) ts -> printFuncApp "union" ts
  FApp (AC Xor) ts -> printFuncApp "xor" ts
  FApp (AC NatPlus) ts -> printFuncApp "plus" ts
  FApp (NoEq (f, _)) ts | BC.unpack f == "pair" -> printFuncApp "" ts
  FApp (NoEq (f, _)) ts -> ppFunSym f ++ printTermsList ts
  FApp (AC (ACfct (f, _))) ts -> ppFunSym f ++ printTermsList ts
  FApp (C EMap) ts -> "em" ++ printTermsList ts
  FApp List ts -> printTermsList ts
  where
    rendered = case viewTerm t of
      Lit literal -> show literal
      _ -> ""
    printTermsList ts = "(" ++ intercalate ", " (map (printTerm sanitizeAtoms vars checkEq) ts) ++ ")"
    printFuncApp acOp [t1, t2] = acOp ++ "(" ++ printTerm sanitizeAtoms vars checkEq t1 ++ ", " ++ printTerm sanitizeAtoms vars checkEq t2 ++ ")"
    printFuncApp acOp (tr : trs) = acOp ++ "(" ++ printTerm sanitizeAtoms vars checkEq tr ++ ", " ++ printFuncApp acOp trs ++ ")"
    printFuncApp _ [] = []

translatePatternTerm ::
  (Document d, Show l) =>
  S.Set String ->
  M.Map String String ->
  Term l ->
  (d, M.Map String String)
translatePatternTerm vars helperVars t = case viewTerm t of
  Lit l
    | S.member (show l) vars || startsWith '\'' (show l) ->
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
  "forall " ++ intercalate ", " (map (++ ":bitstring") atoms) ++ ";#" ++ printTerm False S.empty False t
  where
    atoms = map (showAtom False) . S.toList . S.fromList $ map show $ lits t

makeVariable :: (Show l) => Term l -> M.Map String String -> (String, M.Map String String)
makeVariable t varMap = case M.lookup (printTerm True S.empty False t) varMap of
  Just v -> (v, M.empty)
  Nothing ->
    let newVar = "helperVar" ++ show (M.size varMap)
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
makeDestructorName ::
  (Show l) =>
  M.Map (String, String) String ->
  Term l ->
  String ->
  (String, M.Map (String, String) String)
makeDestructorName dMap t a = case M.lookup (makeDestructorDefinition t, a) dMap of
  Just d -> (d, M.empty)
  Nothing ->
    let newDestructor = "g_" ++ showAtom False a ++ "_" ++ show (M.size dMap)
        newMap = M.singleton (makeDestructorDefinition t, a) newDestructor
     in (newDestructor, newMap)

makeDestructorExpressions ::
  (Document d, Show l, Ord l) =>
  S.Set String ->
  M.Map String String ->
  M.Map (String, String) String ->
  Term l ->
  (d, S.Set String, M.Map (String, String) String)
makeDestructorExpressions vars helperVars destructors t =
  (vcat doclist, S.fromList atoms, newDestructors)
  where
    (doclist, newDestructors) =
      foldl'
        (\acc@(_, destrs) a -> acc `accumulateResult` makeDestructorExpression vars helperVars destrs t a)
        ([], destructors)
        atoms
    atoms = nub $ map show $ lits t

makeDestructorExpression ::
  (Document d, Show l) =>
  S.Set String ->
  M.Map String String ->
  M.Map (String, String) String ->
  Term l ->
  String ->
  (d, M.Map (String, String) String)
makeDestructorExpression vars helperVars destructors t a =
  (varDoc, newDestructors)
  where
    (var, _) = makeVariable t helperVars
    (destr, newDestructors) = makeDestructorName destructors t a
    varDoc =
      ( if S.member a vars || startsWith '\'' a
          then
            text "let (="
              <> text (showAtom True a)
              <> text ") ="
          else
            text "let"
              <-> text (showAtom True a)
              <-> text "="
      )
        <-> text destr
        <> text "("
        <> text var
        <> text ") in"

-- | Accumulate a result into a list while combining semigroup values.
-- Used for folding over facts during rule translation.
accumulateResult :: (Semigroup b) => ([a], b) -> (a, b) -> ([a], b)
accumulateResult (as, b) (a, b1) = (as ++ [a], b <> b1)
