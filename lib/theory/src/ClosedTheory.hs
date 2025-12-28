{-# LANGUAGE FlexibleContexts #-}

module ClosedTheory (
    module ClosedTheory
    , prettyClosedProtoRule
) where

import Control.Basics
import qualified Data.Set as S
-- import qualified Data.Label.Total

import Lemma
import Rule
import Safe
import Theory.Model
import Theory.Proof
import TheoryObject
import Text.PrettyPrint.Highlight
import Term.Macro
import Items.RuleItem



-- import           Data.Typeable
import           Data.Monoid                         (Sum(..))

-- import qualified Data.Label.Total

import           Theory.Tools.InjectiveFactInstances

import           Theory.Text.Pretty
import OpenTheory
import Pretty

------------------------------------------------------------------------------
-- Closed theory querying / construction / modification
------------------------------------------------------------------------------

-- | Closed theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedTheory =
    Theory SignatureWithMaude ClosedRuleCache ClosedProtoRule IncrementalProof ()

-- | Closed Diff theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedDiffTheory =
    DiffTheory SignatureWithMaude ClosedRuleCache DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof

-- | Either Theories can be Either a normal or a diff theory
type EitherClosedTheory = Either ClosedTheory ClosedDiffTheory

-- querying
-----------

-- | All lemmas.
getLemmas :: ClosedTheory -> [Lemma IncrementalProof]
getLemmas = theoryLemmas

-- | All diff lemmas.
getDiffLemmas :: ClosedDiffTheory -> [DiffLemma IncrementalDiffProof]
getDiffLemmas = diffTheoryDiffLemmas

-- | All side lemmas.
getEitherLemmas :: ClosedDiffTheory -> [(Side, Lemma IncrementalProof)]
getEitherLemmas = diffTheoryLemmas

-- | The variants of the intruder rules.
getIntrVariants :: ClosedTheory -> [IntrRuleAC]
getIntrVariants = intruderRules . (.cache.rules)

-- | The variants of the intruder rules.
getIntrVariantsDiff :: Side -> ClosedDiffTheory -> [IntrRuleAC]
getIntrVariantsDiff s
  | s == LHS  = intruderRules . (.cacheLeft.rules)
  | s == RHS  = intruderRules . (.cacheRight.rules)
  | otherwise = error $ "The Side MUST always be LHS or RHS."

-- | All protocol rules modulo E.
getProtoRuleEs :: ClosedTheory -> [ProtoRuleE]
-- we remove duplicates if they exist due to variant unfolding
getProtoRuleEs = S.toList . S.fromList . map ((.ruleE) . openProtoRule) . theoryRules

-- | All protocol rules modulo E.
getProtoRuleEsDiff :: Side -> ClosedDiffTheory -> [ProtoRuleE]
-- we remove duplicates if they exist due to variant unfolding
getProtoRuleEsDiff s = S.toList . S.fromList . map ((.ruleE) . openProtoRule) . diffTheorySideRules s

-- | Get the proof context for a lemma of the closed theory.
getProofContext :: Lemma a -> ClosedTheory -> ProofContext
getProofContext l thy = ProofContext
    thy.signature
    thy.cache.rules
    thy.cache.injectiveFactInsts
    kind
    (cases thy.cache)
    inductionHint
    specifiedHeuristic
    specifiedTactic
    (toSystemTraceQuantifier l.traceQuantifier)
    l.name
    ([ h | HideLemma h <- l.attributes])
    thy.options.verboseOption
    False
    (all isSubtermRule  $ filter isDestrRule $ intruderRules thy.cache.rules)
    (any isConstantRule $ filter isDestrRule $ intruderRules thy.cache.rules)
    thy.isSapic
  where
    kind    = lemmaSourceKind l
    cases   = case kind of RawSource     -> (.rawSources)
                           RefinedSource -> (.refinedSources)
    inductionHint
      | any (`elem` [SourceLemma, InvariantLemma]) l.attributes = UseInduction
      | otherwise                                               = AvoidInduction

    -- Heuristic specified for the lemma > globally specified heuristic > default heuristic
    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case thy.heuristic of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = (headMay [Heuristic gr
                    | LemmaHeuristic gr <- l.attributes])

    -- Tactic specified for the lemma
    specifiedTactic = case lattr of
        [] -> Nothing
        _  -> Just lattr
      where
        lattr = thy.tactic

-- | Get the proof context for a lemma of the closed theory.
getProofContextDiff :: Side -> Lemma a -> ClosedDiffTheory -> ProofContext
getProofContextDiff s l thy = case s of
  LHS -> ProofContext
            thy.signature
            thy.cacheLeft.rules
            thy.cacheLeft.injectiveFactInsts
            kind
            (cases thy.cacheLeft)
            inductionHint
            specifiedHeuristic
            specifiedTactic
            (toSystemTraceQuantifier l.traceQuantifier)
            l.name
            ([ h | HideLemma h <- l.attributes])
            thy.options.verboseOption
            False
            (all isSubtermRule  $ filter isDestrRule $ intruderRules thy.cacheLeft.rules)
            (any isConstantRule $ filter isDestrRule $ intruderRules thy.cacheLeft.rules)
            thy.isSapic
  RHS -> ProofContext
            thy.signature
            thy.cacheRight.rules
            thy.cacheRight.injectiveFactInsts
            kind
            (cases thy.cacheRight)
            inductionHint
            specifiedHeuristic
            specifiedTactic
            (toSystemTraceQuantifier l.traceQuantifier)
            l.name
            ([ h | HideLemma h <- l.attributes])
            thy.options.verboseOption
            False
            (all isSubtermRule  $ filter isDestrRule $ intruderRules thy.cacheRight.rules)
            (any isConstantRule $ filter isDestrRule $ intruderRules thy.cacheRight.rules)
            thy.isSapic
  where
    kind    = lemmaSourceKind l
    cases   = case kind of RawSource     -> (.rawSources)
                           RefinedSource -> (.refinedSources)
    inductionHint
      | any (`elem` [SourceLemma, InvariantLemma]) l.attributes = UseInduction
      | otherwise                                               = AvoidInduction
    -- Heuristic specified for the lemma > globally specified heuristic > default heuristic
    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case thy.heuristic of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = (headMay [Heuristic gr
                    | LemmaHeuristic gr <- l.attributes])

    specifiedTactic = case lattr of
        [] -> Nothing
        _  -> Just lattr
      where
        lattr = thy.tactic

-- | Get the proof context for a diff lemma of the closed theory.
getDiffProofContext :: DiffLemma a -> ClosedDiffTheory -> DiffProofContext
getDiffProofContext l thy = DiffProofContext (proofContext LHS) (proofContext RHS)
    (map (.rule) $ diffTheoryDiffRules thy) thy.diffCacheLeft.rules.construct
    thy.diffCacheLeft.rules.destruct
    ((LHS, restrictionsLeft):[(RHS, restrictionsRight)]) gatherReusableLemmas
  where
    items = thy.items
    restrictionsLeft  = do EitherRestrictionItem (LHS, rstr) <- items
                           return $ formulaToGuarded_ rstr.formula
    restrictionsRight = do EitherRestrictionItem (RHS, rstr) <- items
                           return $ formulaToGuarded_ rstr.formula
    gatherReusableLemmas = do
        EitherLemmaItem (s, lem) <- items
        guard $    lemmaSourceKind lem <= RefinedSource
                && ReuseDiffLemma `elem` lem.attributes
                && AllTraces == lem.traceQuantifier
        return $ (s, formulaToGuarded_ lem.formula)
    proofContext s   = case s of
        LHS -> ProofContext
            thy.signature
            thy.diffCacheLeft.rules
            thy.diffCacheLeft.injectiveFactInsts
            RefinedSource
            thy.diffCacheLeft.refinedSources
            AvoidInduction
            specifiedHeuristic
            specifiedTactic
            ExistsNoTrace
            l.name
            ([ h | HideLemma h <- l.attributes])
            thy.options.verboseOption
            True
            (all isSubtermRule  $ filter isDestrRule $ intruderRules thy.cacheLeft.rules)
            (any isConstantRule $ filter isDestrRule $ intruderRules thy.cacheLeft.rules)
            thy.isSapic
        RHS -> ProofContext
            thy.signature
            thy.diffCacheRight.rules
            thy.diffCacheRight.injectiveFactInsts
            RefinedSource
            thy.diffCacheRight.refinedSources
            AvoidInduction
            specifiedHeuristic
            specifiedTactic
            ExistsNoTrace
            l.name
            ([ h | HideLemma h <- l.attributes])
            thy.options.verboseOption
            True
            (all isSubtermRule  $ filter isDestrRule $ intruderRules thy.cacheRight.rules)
            (any isConstantRule $ filter isDestrRule $ intruderRules thy.cacheRight.rules)
            thy.isSapic

    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case thy.heuristic of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = (headMay [Heuristic gr
                    | LemmaHeuristic gr <- l.attributes])

    specifiedTactic = case lattr of
        [] -> Nothing
        _  -> Just lattr
      where
        lattr = thy.tactic

-- | The facts with injective instances in this theory
getInjectiveFactInsts :: ClosedTheory -> S.Set (FactTag, [[MonotonicBehaviour]])
getInjectiveFactInsts = (.cache.injectiveFactInsts)

-- | The facts with injective instances in this theory
getDiffInjectiveFactInsts :: Side -> Bool -> ClosedDiffTheory -> S.Set (FactTag, [[MonotonicBehaviour]])
getDiffInjectiveFactInsts s isdiff = case (s, isdiff) of
           (LHS, False) -> (.cacheLeft.injectiveFactInsts)
           (RHS, False) -> (.cacheRight.injectiveFactInsts)
           (LHS, True)  -> (.diffCacheLeft.injectiveFactInsts)
           (RHS, True)  -> (.diffCacheRight.injectiveFactInsts)

-- | The classified set of rules modulo AC in this theory.
getClassifiedRules :: ClosedTheory -> ClassifiedRules
getClassifiedRules = (.cache.rules)

-- | The classified set of rules modulo AC in this theory.
getDiffClassifiedRules :: Side -> Bool -> ClosedDiffTheory -> ClassifiedRules
getDiffClassifiedRules s isdiff = case (s, isdiff) of
           (LHS, False) -> (.cacheLeft.rules)
           (RHS, False) -> (.cacheRight.rules)
           (LHS, True)  -> (.diffCacheLeft.rules)
           (RHS, True)  -> (.diffCacheRight.rules)

-- | The precomputed case distinctions.
getSource :: SourceKind -> ClosedTheory -> [Source]
getSource RawSource     = (.cache.rawSources)
getSource RefinedSource = (.cache.refinedSources)

-- | The precomputed case distinctions.
getDiffSource :: Side -> Bool -> SourceKind -> ClosedDiffTheory -> [Source]
getDiffSource LHS False RawSource     = (.cacheLeft.rawSources)
getDiffSource RHS False RawSource     = (.cacheRight.rawSources)
getDiffSource LHS False RefinedSource = (.cacheLeft.refinedSources)
getDiffSource RHS False RefinedSource = (.cacheRight.refinedSources)
getDiffSource LHS True  RawSource     = (.diffCacheLeft.rawSources)
getDiffSource RHS True  RawSource     = (.diffCacheRight.rawSources)
getDiffSource LHS True  RefinedSource = (.diffCacheLeft.refinedSources)
getDiffSource RHS True  RefinedSource = (.diffCacheRight.refinedSources)

-- construction
---------------

-- | Close a protocol rule; i.e., compute AC variant and source assertion
-- soundness sequent, if required.
closeEitherProtoRule :: MaudeHandle -> (Side, OpenProtoRule) -> (Side, [ClosedProtoRule])
closeEitherProtoRule hnd (s, ruE) = (s, closeProtoRule hnd [] ruE)

-- | Apply macro to a diff protocol rule.
applyMacroInDiffProtoRule :: [LNMacro]-> DiffProtoRule -> DiffProtoRule
applyMacroInDiffProtoRule mcs (DiffProtoRule ruE sides) = DiffProtoRule (applyMacroInRule mcs ruE) sides

-- | Apply macro to an open protocol rule.
applyMacroInProtoRule :: [LNMacro]-> OpenProtoRule -> OpenProtoRule
applyMacroInProtoRule mcs (OpenProtoRule ruE variants) = OpenProtoRule (applyMacroInRule mcs ruE) variants


-- -- | Convert a lemma to the corresponding guarded formula.
-- lemmaToGuarded :: Lemma p -> Maybe LNGuarded
-- lemmaToGuarded lem =


-- | Pretty print an closed rule.
prettyClosedProtoRule :: HighlightDocument d => ClosedProtoRule -> d
prettyClosedProtoRule cru =
  if isTrivialProtoVariantAC ruAC ruE then
  -- We have a rule that only has one trivial variant, and without added annotations
  -- Hence showing the initial rule modulo E
    (prettyProtoRuleE ruE) $--$
    (nest 2 $ prettyLoopBreakers ruAC.info $-$
     multiComment_ ["has exactly the trivial AC variant"])
  else
    if ruleName ruAC == ruleName ruE then
      if not (equalUpToTerms ruAC ruE) then
      -- Here we have a rule with added annotations,
      -- hence showing the annotated rule as if it was a rule mod E
      -- note that we can do that, as we unfolded variants
        (prettyProtoRuleACasE ruAC) $--$
        (nest 2 $ prettyLoopBreakers ruAC.info $-$
         multiComment_ ["has exactly the trivial AC variant"])
      else
      -- Here we have a rule with one or multiple variants, but without other annotations
      -- Hence showing the rule mod E with commented variants
        (prettyProtoRuleE ruE) $--$
        (nest 2 $ prettyLoopBreakers ruAC.info $-$
         (multiComment $ prettyProtoRuleAC ruAC))
    else
    -- Here we have a variant of a rule that has multiple variants.
    -- Hence showing only the variant as a rule modulo AC. This should not
    -- normally be used, as it breaks the ability to re-import.
      (prettyProtoRuleAC ruAC) $--$
      (nest 3 $ prettyLoopBreakers ruAC.info $-$
          (multiComment_ ["variant of"]) $-$
          (multiComment $ prettyProtoRuleE ruE)
      )
 where
    ruAC      = cru.ruleAC
    ruE       = cru.ruleE

-- -- | Pretty print an closed rule.
-- prettyClosedEitherRule :: HighlightDocument d => (Side, ClosedProtoRule) -> d
-- prettyClosedEitherRule (s, cru) =
--     text ((show s) ++ ": ") <>
--     (prettyProtoRuleE ruE) $--$
--     (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$ ppRuleAC)
--   where
--     ruAC = L.get cprRuleAC cru
--     ruE  = L.get cprRuleE cru
--     ppRuleAC
--       | isTrivialProtoVariantAC ruAC ruE = multiComment_ ["has exactly the trivial AC variant"]
--       | otherwise                        = multiComment $ prettyProtoRuleAC ruAC

-- | Pretty print a closed theory.
prettyClosedTheory :: HighlightDocument d => ClosedTheory -> d
prettyClosedTheory thy = if containsManualRuleVariants mergedRules
    then
      prettyTheory prettySignatureWithMaude
                  ppInjectiveFactInsts
                  -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                  prettyOpenProtoRuleAsClosedRule
                  prettyIncrementalProof
                  emptyString
                  thy'
    else
      prettyTheory prettySignatureWithMaude
                  ppInjectiveFactInsts
                  -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                  prettyClosedProtoRule
                  prettyIncrementalProof
                  emptyString
                  thy
  where
    items = thy.items
    mergedRules = mergeOpenProtoRules $ map (mapTheoryItem openProtoRule id) items
    thy' :: Theory SignatureWithMaude ClosedRuleCache OpenProtoRule IncrementalProof ()
    thy' = Theory {name=thy.name
            ,inFile=thy.inFile
            ,heuristic=thy.heuristic
            ,tactic=thy.tactic
            ,signature=thy.signature
            ,cache=thy.cache
            ,items = mergedRules
            ,options =thy.options
            ,isSapic = thy.isSapic}
    ppInjectiveFactInsts crc =
        case S.toList crc.injectiveFactInsts of
            []   -> emptyDoc
            tags -> multiComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) (map fst tags) ]

-- | Pretty print a closed diff theory.
prettyClosedDiffTheory :: HighlightDocument d => ClosedDiffTheory -> d
prettyClosedDiffTheory thy = if containsManualRuleVariantsDiff mergedRules
    then
      prettyDiffTheory prettySignatureWithMaude
                 ppInjectiveFactInsts
                 -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                 (\_ -> emptyDoc) --prettyClosedEitherRule
                 prettyIncrementalDiffProof
                 prettyIncrementalProof
                 thy'
    else
        prettyDiffTheory prettySignatureWithMaude
                   ppInjectiveFactInsts
                   -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                   (\_ -> emptyDoc) --prettyClosedEitherRule
                   prettyIncrementalDiffProof
                   prettyIncrementalProof
                   thy
  where
    items = thy.items
    mergedRules = mergeLeftRightRulesDiff $ mergeOpenProtoRulesDiff $
       map (mapDiffTheoryItem id (\(x, y) -> (x, (openProtoRule y))) id id) items
    thy' :: DiffTheory SignatureWithMaude ClosedRuleCache DiffProtoRule OpenProtoRule IncrementalDiffProof IncrementalProof
    thy' = DiffTheory {name=thy.name
            ,inFile=thy.inFile
            ,heuristic=thy.heuristic
            ,tactic=thy.tactic
            ,signature=thy.signature
            ,cacheLeft=thy.cacheLeft
            ,cacheRight=thy.cacheRight
            ,diffCacheLeft=thy.diffCacheLeft
            ,diffCacheRight=thy.diffCacheRight
            ,items = mergedRules
            ,options =thy.options
            ,isSapic = thy.isSapic}
    ppInjectiveFactInsts crc =
        case S.toList crc.injectiveFactInsts of
            []   -> emptyDoc
            tags -> multiComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) (map fst tags) ]

prettyClosedSummary :: Document d => ClosedTheory -> d
prettyClosedSummary thy =
    vcat lemmaSummaries
  where
    lemmaSummaries = do
        LemmaItem lem  <- thy.items
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary lem.proof
            quantifier = (toSystemTraceQuantifier lem.traceQuantifier)
            analysisType = parens $ prettyTraceQuantifier lem.traceQuantifier
        return $ text lem.name <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))

prettyClosedDiffSummary :: Document d => ClosedDiffTheory -> d
prettyClosedDiffSummary thy =
    (vcat lemmaSummaries) $$ (vcat diffLemmaSummaries)
  where
    lemmaSummaries = do
        EitherLemmaItem (s, lem)  <- thy.items
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary lem.proof
            quantifier = (toSystemTraceQuantifier lem.traceQuantifier)
            analysisType = parens $ prettyTraceQuantifier lem.traceQuantifier
        return $ text (show s) <-> text ": " <-> text lem.name <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    diffLemmaSummaries = do
        DiffLemmaItem (lem)  <- thy.items
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldDiffProof diffProofStepSummary lem.proof
        return $ text "DiffLemma: " <-> text lem.name <-> colon <->
                 text (showDiffProofStatus status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))
    diffProofStepSummary = diffProofStepStatus &&& const (Sum (1::Integer))

checkProofStatuses :: ClosedTheory -> [ProofStatus]
checkProofStatuses thy =  map (foldProof proofStepStatus . (.proof)) $ theoryLemmas thy

checkDiffProofStatuses :: ClosedDiffTheory -> [ProofStatus]
checkDiffProofStatuses thy = map (foldProof proofStepStatus . (.proof) . snd) $ diffTheoryLemmas thy

-- | Render the results of the precomputations, for --precompute-only
prettyPrecomputation ::  Document d => ClosedTheory -> d
prettyPrecomputation thy = foldr1 ($-$)
    [
      ruleLink
    , reqCasesLink "Raw sources:" RawSource
    , reqCasesLink "Refined sources:" RefinedSource
    ]
  where
    rules          = getClassifiedRules thy
    rulesInfo      = text $ show $ length rules.protocol
    casesInfo kind = nCases <> comma <-> text chainInfo
      where
        cases   = getSource kind thy
        nChains = sum $ map (sum . unsolvedChainConstraints) cases
        nCases  = text $ show (length cases) ++ " " ++ "cases"
        chainInfo | nChains == 0 = "deconstructions complete"
                  | otherwise    = show nChains ++ " partial deconstructions left"

    overview n p   = n <-> p
    ruleLinkMsg         = text $ "Multiset rewriting rules" ++
                          (if null(theoryRestrictions thy) then "" else " and restrictions") ++ ":"
    ruleLink            = overview ruleLinkMsg rulesInfo
    reqCasesLink name k = overview (text name) (casesInfo k)


-- | Render the results of the precomputations, for --precompute-only (diff mode)
prettyDiffPrecomputation :: Document d => ClosedDiffTheory -> d
prettyDiffPrecomputation thy = foldr1 ($-$)
    [
      ruleLink LHS False
    , ruleLink RHS False
    , ruleLink LHS True
    , ruleLink RHS True
    , reqCasesLink LHS "LHS: Raw sources:"            RawSource False
    , reqCasesLink RHS "RHS: Raw sources:"            RawSource False
    , reqCasesLink LHS "LHS: Raw sources [Diff]:"     RawSource True
    , reqCasesLink RHS "RHS: Raw sources [Diff]:"     RawSource True
    , reqCasesLink LHS "LHS: Refined sources:"        RefinedSource   False
    , reqCasesLink RHS "RHS: Refined sources:"        RefinedSource   False
    , reqCasesLink LHS "LHS: Refined sources [Diff]:" RefinedSource   True
    , reqCasesLink RHS "RHS: Refined sources [Diff]:" RefinedSource   True
    ]
  where
    rules s isdiff     = getDiffClassifiedRules s isdiff thy
    rulesInfo s isdiff = text $ show $ length (rules s isdiff).protocol
    casesInfo s kind isdiff = nCases <> comma <-> text chainInfo
      where
        cases   = getDiffSource s isdiff kind thy
        nChains = sum $ map (sum . unsolvedChainConstraints) cases
        nCases  = text $ show (length cases) ++ " " ++ "cases"
        chainInfo | nChains == 0 = "deconstructions complete"
                  | otherwise    = show nChains ++ " partial deconstructions left"

    overview n p   = n <-> p
    ruleLink s isdiff    = overview (ruleLinkMsg s isdiff) (rulesInfo s isdiff)
    ruleLinkMsg s isdiff = text $ show s ++ ": Multiset rewriting rules" ++
                           (if null(diffTheorySideRestrictions s thy) then "" else " and restrictions") ++ (if isdiff then " [Diff]" else "") ++ ":"

    reqCasesLink s name k isdiff = overview (text name) (casesInfo s k isdiff)
