{-# LANGUAGE GADTs #-}

-- |
-- Explicit semantic outcomes and prepared values for ProVerif properties.
module Export.ProVerif.Property
  ( PreparedAxiomProperty (..),
    PreparedFormula (..),
    PreparedQueryFormula (..),
    PreparedQueryProperty (..),
    PreparedRestrictionProperty (..),
    PropertyOutcome (..),
    PropertyRole (..),
    QueryPolarity (..),
    QueryRecombination (..),
    RuleIdStrategy (..),
    annotateAxiomProperty,
    annotateQueryProperty,
    annotateRestrictionProperty,
    mapPropertyOutcome,
    planOutcome,
    preparedFormulaRuleIdEvents,
    prepareProperty,
  )
where

import Control.Applicative ((<|>))
import Control.Monad.Fresh (MonadFresh)
import Control.Monad.Trans.PreciseFresh qualified as Precise
import Data.Either (fromRight)
import Data.List as List
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as S
import Data.Set qualified as Set
import Export.ProVerif.Formula
import Export.ProVerif.Instrumentation
import Export.Types (translationInvariantFail)
import Sapic.Typing
import Theory
import Theory.Tools.Wellformedness (formulaFacts)

data QueryPolarity
  = DirectResult
  | InvertResult
  deriving (Eq, Ord, Show)

data QueryRecombination
  = ConjoinQueryResults
  | DisjoinQueryResults
  deriving (Eq, Ord, Show)

-- | How rule-id variables are allocated for a prepared formula's split
-- timepoints: one name per origin, or the shared name when only one group
-- remains in a subformula.
data RuleIdStrategy = OriginRuleIds | SharedRuleIdWhenSingle
  deriving (Eq, Ord, Show)

data PreparedQueryFormula = PreparedQueryFormula
  { preparedQueryBody :: PreparedFormula,
    preparedQueryPolarity :: QueryPolarity,
    preparedQueryRuleIdStrategy :: RuleIdStrategy
  }

data PreparedQueryProperty = PreparedQueryProperty
  { preparedQueryFormulas :: NE.NonEmpty PreparedQueryFormula,
    preparedQueryRecombination :: Maybe QueryRecombination,
    preparedQueryCompletionTriggers :: Set.Set String
  }

data PreparedFormula = PreparedFormula
  { preparedFormula :: LNFormula,
    preparedTimeOrigins :: Map.Map String String,
    preparedHadTimepointSplit :: Bool,
    preparedKeepTimeVariables :: Bool,
    preparedRuleIdNames :: Map.Map String String
  }

data PreparedAxiomProperty = PreparedAxiomProperty
  { preparedAxiomFormulas :: NE.NonEmpty PreparedFormula,
    preparedAxiomCompletionTriggers :: Set.Set String,
    preparedAxiomApproximation :: Maybe String
  }

data PreparedRestrictionProperty = PreparedRestrictionProperty
  { preparedRestrictionFormulas :: NE.NonEmpty PreparedFormula,
    preparedRestrictionWasRewritten :: Bool,
    preparedRestrictionApproximation :: Maybe String
  }

data PropertyOutcome a
  = PropertyEmitted a
  | PropertyOmitted String
  | PropertyExcluded

data PropertyRole prepared where
  QueryProperty :: Lemma ProofSkeleton -> PropertyRole PreparedQueryProperty
  AxiomProperty :: Lemma ProofSkeleton -> PropertyRole PreparedAxiomProperty
  RestrictionProperty :: Restriction -> PropertyRole PreparedRestrictionProperty

-- | The prepared outcome recorded for a property name; entries absent from
-- the plan are explicitly excluded properties.
planOutcome :: String -> [(String, PropertyOutcome a)] -> PropertyOutcome a
planOutcome name plans = fromMaybe PropertyExcluded (lookup name plans)

prepareProperty :: String -> TypingEnvironment -> PropertyRole prepared -> PropertyOutcome prepared
prepareProperty completionEvent typeEnvironment = \case
  QueryProperty lemma -> prepareQueryProperty completionEvent typeEnvironment lemma
  AxiomProperty lemma -> prepareAxiomProperty completionEvent typeEnvironment lemma
  RestrictionProperty restriction -> prepareRestrictionProperty typeEnvironment restriction

-- | Translate a lemma formula for ProVerif output.
-- This function translates ONLY lemmas in the "classical way" with timepoints.
-- The resulting translations are suitable only as ProVerif queries (not lemmas/axioms/restrictions).
--
-- Key steps:
-- 1. Simplify and apply rewriting transformations
-- 2. Split shared timepoints if needed
-- 3. Split top-level connectives (AND for all-traces, OR for exists-trace)
-- 4. Apply final transformations and print each subformula
prepareQueryProperty :: String -> TypingEnvironment -> Lemma ProofSkeleton -> PropertyOutcome PreparedQueryProperty
prepareQueryProperty completionEvent typeEnvironment lemma
  | Just reason <- queryKnowledgeFragmentFailure lemma._lTraceQuantifier lemma._lFormula =
      PropertyOmitted reason
  | Just reason <- listToMaybe [reason | (_, Just reason) <- preparedCandidates] =
      PropertyOmitted reason
  | otherwise =
      PropertyEmitted
        PreparedQueryProperty
          { preparedQueryFormulas = preparedNonEmpty "query" (map fst preparedCandidates),
            preparedQueryRecombination = recombination,
            preparedQueryCompletionTriggers = completionTriggers
          }
  where
    simplifiedFormula = simplifyFormula lemma._lFormula
    standardRewrittenFormula = rewriteFormulaForQuery lemma._lTraceQuantifier simplifiedFormula
    standardNeedsRuleId = formulaHasSharedTimepoints standardRewrittenFormula
    standardFormulaForProcessing
      | standardNeedsRuleId = makeTimeVarsDistinct standardRewrittenFormula
      | otherwise = standardRewrittenFormula
    standardFormulas =
      splitTopLevel lemma._lTraceQuantifier standardFormulaForProcessing
    standardTranslationRejected =
      not (null standardFormulas)
        && all standardSubformulaRejected standardFormulas
    standardSubformulaRejected formula =
      let (transformed, _) = transformQueryFormula lemma DirectResult formula
          (formulaToRender, _) = queryFormulaToTranslate lemma transformed
       in isJust (queryFormulaFailure typeEnvironment formulaToRender)
    positiveWitnessDualization
      | lemma._lTraceQuantifier == ExistsTrace,
        standardTranslationRejected = rewritePositiveWitnessExistsTrace simplifiedFormula
      | otherwise = Nothing
    allTraceNormalization
      | lemma._lTraceQuantifier == AllTraces,
        standardTranslationRejected = normalizeAllTraceFormula simplifiedFormula
      | otherwise = Nothing
    formulaBeforeRewrites =
      fromMaybe
        (fromMaybe simplifiedFormula allTraceNormalization)
        positiveWitnessDualization
    initialPolarity
      | isJust positiveWitnessDualization = InvertResult
      | otherwise = DirectResult
    rewrittenBeforeCompletion
      | isJust allTraceNormalization =
          mapTopLevelConjunctsFormula
            (rewriteFormulaForQuery lemma._lTraceQuantifier)
            formulaBeforeRewrites
      | otherwise = rewriteFormulaForQuery lemma._lTraceQuantifier formulaBeforeRewrites
    (guardedFormula, completionTriggers) =
      guardSameActionConclusions completionEvent rewrittenBeforeCompletion
    needsRuleId = formulaHasSharedTimepoints guardedFormula
    (formulaForProcessing, splitTimeOrigins)
      | needsRuleId = makeTimeVarsDistinctWithOrigins guardedFormula
      | otherwise = (guardedFormula, M.empty)
    splitFormulas = splitTopLevel lemma._lTraceQuantifier formulaForProcessing
    preparedCandidates = map prepareCandidate splitFormulas
    prepareCandidate formula =
      ( PreparedQueryFormula
          { preparedQueryBody =
              PreparedFormula
                { preparedFormula = formulaToRender,
                  preparedTimeOrigins = splitTimeOrigins,
                  preparedHadTimepointSplit = needsRuleId,
                  preparedKeepTimeVariables = True,
                  preparedRuleIdNames = M.empty
                },
            preparedQueryPolarity = finalPolarity,
            preparedQueryRuleIdStrategy =
              if initialPolarity == InvertResult
                then OriginRuleIds
                else SharedRuleIdWhenSingle
          },
        queryFormulaFailure typeEnvironment formulaToRender
      )
      where
        (transformed, transformedPolarity) =
          transformQueryFormula lemma initialPolarity formula
        (formulaToRender, isExistentialNegation) =
          queryFormulaToTranslate lemma transformed
        finalPolarity
          | isExistentialNegation = InvertResult
          | otherwise = transformedPolarity
    recombination
      | length preparedCandidates < 2 = Nothing
      | lemma._lTraceQuantifier == AllTraces = Just ConjoinQueryResults
      | otherwise = Just DisjoinQueryResults

queryFormulaFailure :: TypingEnvironment -> LNFormula -> Maybe String
queryFormulaFailure _typeEnvironment formula
  | alternations > 1 =
      Just ("formula has " ++ show alternations ++ " quantifier alternations; ProVerif supports at most one")
  | hasNegatedActionInFormula formula =
      Just "formula contains a negated event that ProVerif cannot express"
  | not (supportsQueryFormula formula) =
      Just "formula is outside the supported ProVerif query fragment"
  | otherwise = Nothing
  where
    alternations = countQuantifierAlternations formula

transformQueryFormula :: Lemma ProofSkeleton -> QueryPolarity -> LNFormula -> (LNFormula, QueryPolarity)
transformQueryFormula lemma inheritedPolarity formula
  | inheritedPolarity == DirectResult,
    lemma._lTraceQuantifier == ExistsTrace,
    Just dualized <- rewriteEventFreeExistsTrace formula =
      (dualized, InvertResult)
transformQueryFormula lemma inheritedPolarity formula =
  (finalFormula, queryPolarity)
  where
    hasLeadingNotEx = case formula of
      Not (Qua Ex _ _) -> True
      _ -> False
    hasAllImpliesFalse = case formula of
      Qua All _ body -> checkAllImpliesNot body
      _ -> False
    checkAllImpliesNot (Qua All _ body) = checkAllImpliesNot body
    checkAllImpliesNot (Not _) = True
    checkAllImpliesNot (Conn Imp _ (TF False)) = True
    checkAllImpliesNot _ = False
    notExists = isNegatedExistsWithConjunction formula
    existsConjunction = isExistsWithNegatedExistentials formula
    hadLeadingNegation =
      hasLeadingNotEx
        || hasAllImpliesFalse
        || notExists
        || (existsConjunction && lemma._lTraceQuantifier == ExistsTrace)
    movedToConclusion =
      moveNegatedActionsToConclusion $ moveConstraintsToConclusion formula
    shape = classifyFormulaShape lemma._lTraceQuantifier movedToConclusion
    finalFormula =
      simplifyFormula $ expandNegatedTimepointComparisons $ applyRewriteForShape shape movedToConclusion
    queryPolarity
      | inheritedPolarity == InvertResult || hadLeadingNegation || isNegated finalFormula = InvertResult
      | otherwise = DirectResult
    isNegated (Not _) = True
    isNegated _ = False

queryFormulaToTranslate :: Lemma ProofSkeleton -> LNFormula -> (LNFormula, Bool)
queryFormulaToTranslate lemma formula =
  case formula of
    Not inner@(Qua Ex _ _) -> (inner, True)
    Not inner
      | isAllImpliesExists inner,
        lemma._lTraceQuantifier == ExistsTrace -> (inner, True)
    _
      | lemma._lTraceQuantifier == AllTraces,
        Just existential <- universalNegationAsExists formula -> (existential, True)
    _ -> (formula, False)


prepareRestrictionProperty :: TypingEnvironment -> Restriction -> PropertyOutcome PreparedRestrictionProperty
prepareRestrictionProperty _typeEnvironment restriction
  | Just reason <- assumptionKnowledgeFragmentFailure restriction._rstrFormula =
      PropertyOmitted reason
  | Left reason <- selectedCandidates = PropertyOmitted reason
  | Just reason <- renderFailure = PropertyOmitted reason
  | otherwise =
      PropertyEmitted
        PreparedRestrictionProperty
          { preparedRestrictionFormulas = preparedNonEmpty "restriction" (map prepareCandidate candidates),
            preparedRestrictionWasRewritten = wasRewritten,
            preparedRestrictionApproximation = approximation
          }
  where
    beforePull =
      simplifyFormula
        . flattenNestedImplications
        . expandNegatedTimepointComparisons
        . moveNegatedActionsToConclusion
        . moveConstraintsToConclusion
        . eliminateTemporalEqualities
        . simplifyFormula
        $ restriction._rstrFormula
    (normalized, approximation) = pullNegationsWithDiagnostic "restriction" beforePull
    needsRuleId = formulaHasSharedTimepoints normalized
    (formulaWithDistinctTimepoints, splitTimeOrigins)
      | needsRuleId = makeTimeVarsDistinctWithOrigins normalized
      | otherwise = (normalized, M.empty)
    selectedCandidates
      | Just alternatives <- tryRewriteForbiddenAlternatives formulaWithDistinctTimepoints =
          Right (alternatives, True)
      | Just rewritten <- tryRewriteNegatedRestriction formulaWithDistinctTimepoints =
          Right ([rewritten], True)
      | hasNestedImplicationInConjunction formulaWithDistinctTimepoints =
          Left "formula has a nested implication inside a conjunction"
      | hasVariableCaptureInNestedImplication formulaWithDistinctTimepoints =
          Left "flattening a nested quantified implication would capture a variable"
      | otherwise = Right ([formulaWithDistinctTimepoints], False)
    (rawCandidates, wasRewritten) = fromRight ([], False) selectedCandidates
    candidates = map (flattenNestedImplications . allImplExLessWoTmps) rawCandidates
    renderFailure =
      listToMaybe
        [ "formula is outside the supported ProVerif restriction fragment"
        | formula <- candidates,
          not (supportsAssumptionFormula formula)
        ]
    prepareCandidate formula =
      PreparedFormula
        { preparedFormula = formula,
          preparedTimeOrigins = splitTimeOrigins,
          preparedHadTimepointSplit = needsRuleId,
          preparedKeepTimeVariables = True,
          preparedRuleIdNames = M.empty
        }

    tryRewriteForbiddenAlternatives (Not positive) = do
      let (prefix, body) = collectExistentialPrefix (pnf positive)
      branches <- positiveDnf 16 body
      let distinctBranches = List.nub branches
      if null prefix
          || length distinctBranches < 2
          || not (all isSupportedPositivePremise distinctBranches)
          || not (all formulaContainsAction distinctBranches)
        then Nothing
        else
          Just
            [ rewrapBoundPrefix All prefix (Conn Imp branch (TF False))
            | branch <- distinctBranches
            ]
    tryRewriteForbiddenAlternatives _ = Nothing

    collectExistentialPrefix (Qua Ex binder body) =
      let (rest, inner) = collectExistentialPrefix body
       in (binder : rest, inner)
    collectExistentialPrefix body = ([], body)

    positiveDnf limit formula = case formula of
      Conn Or left right -> do
        leftBranches <- positiveDnf limit left
        rightBranches <- positiveDnf (limit - length leftBranches) right
        let branches = leftBranches ++ rightBranches
        if length branches <= limit then Just branches else Nothing
      Conn And left right -> do
        leftBranches <- positiveDnf limit left
        rightBranches <- positiveDnf limit right
        let branchCount = length leftBranches * length rightBranches
        if branchCount <= limit
          then
            Just
              [ buildConjunction (flattenConjuncts leftBranch ++ flattenConjuncts rightBranch)
              | leftBranch <- leftBranches,
                rightBranch <- rightBranches
              ]
          else Nothing
      _
        | limit >= 1,
          isQuantifierFree formula -> Just [formula]
        | otherwise -> Nothing

    tryRewriteNegatedRestriction (Not formula) = tryRewriteNegatedBody formula
    tryRewriteNegatedRestriction _ = Nothing
    tryRewriteNegatedBody (Qua Ex binder body) =
      Qua All binder <$> tryRewriteNegatedBody body
    tryRewriteNegatedBody (Conn And premise (Not (Ato (EqE left right)))) =
      Just (Conn Imp premise (Ato (EqE left right)))
    tryRewriteNegatedBody (Conn And premise (Ato (Less left right))) =
      Just (Conn Imp premise (Conn Or (Ato (Less right left)) (Ato (EqE left right))))
    tryRewriteNegatedBody _ = Nothing

prepareAxiomProperty :: String -> TypingEnvironment -> Lemma ProofSkeleton -> PropertyOutcome PreparedAxiomProperty
prepareAxiomProperty completionEvent _typeEnvironment lemma
  | Just reason <- assumptionKnowledgeFragmentFailure lemma._lFormula =
      PropertyOmitted reason
  | Just reason <- axiomFailure = PropertyOmitted reason
  | otherwise =
      PropertyEmitted
        PreparedAxiomProperty
          { preparedAxiomFormulas = preparedNonEmpty "axiom" (map prepareRenderedFormula renderedAxiomFormulas),
            preparedAxiomCompletionTriggers = completionTriggers,
            preparedAxiomApproximation = approximation
          }
  where
    simplified = simplifyFormula lemma._lFormula
    sharedNormalization = normalizeAllTraceFormula simplified
    normalized = fromMaybe simplified sharedNormalization
    (rewrittenBeforeCompletion, approximation)
      | isJust sharedNormalization = rewriteTopLevelConjuncts normalized
      | otherwise = rewriteFormulaForAxiomWithDiagnostic normalized
    (guarded, completionTriggers) =
      guardSameActionConclusions completionEvent rewrittenBeforeCompletion
    axiomFormulas
      | isJust sharedNormalization =
          splitTopLevel AllTraces guarded
      | otherwise = [guarded]
    renderedAxiomFormulas =
      map (flattenNestedImplications . allImplExLessWoTmps) axiomFormulas
    axiomFailure =
      listToMaybe
        ( [ "formula has a nested implication inside a conjunction"
          | any hasNestedImplicationInConjunction axiomFormulas
          ]
            ++ [ "flattening a nested quantified implication would capture a variable"
               | any hasVariableCaptureInNestedImplication axiomFormulas
               ]
            ++ [ "formula contains a negated event that ProVerif cannot express"
               | any hasNegatedEventInFormula axiomFormulas
               ]
            ++ [ "formula is outside the supported ProVerif axiom fragment"
               | formula <- renderedAxiomFormulas,
                 not (supportsAssumptionFormula formula)
               ]
        )
    rewriteTopLevelConjuncts (Conn And left right) =
      let (left', leftApproximation) = rewriteTopLevelConjuncts left
          (right', rightApproximation) = rewriteTopLevelConjuncts right
       in ( Conn And left' right',
            leftApproximation <|> rightApproximation
          )
    rewriteTopLevelConjuncts formula = rewriteFormulaForAxiomWithDiagnostic formula

prepareRenderedFormula :: LNFormula -> PreparedFormula
prepareRenderedFormula formula =
  PreparedFormula
    { preparedFormula = renderedFormula,
      preparedTimeOrigins = timeOrigins,
      preparedHadTimepointSplit = needsRuleId,
      preparedKeepTimeVariables = requiresAxiomTimepoints renderedFormula,
      preparedRuleIdNames = M.empty
    }
  where
    needsRuleId = formulaHasSharedTimepoints formula
    (renderedFormula, timeOrigins)
      | needsRuleId = makeTimeVarsDistinctWithOrigins formula
      | otherwise = (formula, M.empty)

mapPropertyOutcome :: (a -> b) -> PropertyOutcome a -> PropertyOutcome b
mapPropertyOutcome transform (PropertyEmitted prepared) =
  PropertyEmitted (transform prepared)
mapPropertyOutcome _ (PropertyOmitted reason) = PropertyOmitted reason
mapPropertyOutcome _ PropertyExcluded = PropertyExcluded

annotatePreparedFormula :: RuleIdStrategy -> S.Set String -> PreparedFormula -> PreparedFormula
annotatePreparedFormula strategy ruleIdEvents prepared =
  prepared
    { preparedRuleIdNames = ruleIdNames,
      preparedKeepTimeVariables = prepared.preparedKeepTimeVariables || M.size ruleIdNames > 1
    }
  where
    formula = prepared.preparedFormula
    ruleIdNames
      | prepared.preparedHadTimepointSplit && strategy == OriginRuleIds =
          ridOccurrenceNamesWithOrigins
            ruleIdEvents
            prepared.preparedTimeOrigins
            formula
      | prepared.preparedHadTimepointSplit =
          ridOccurrenceNamesWithOriginsPreservingSingle
            ruleIdEvents
            prepared.preparedTimeOrigins
            formula
      | otherwise = ridOccurrenceNames ruleIdEvents formula

annotateQueryProperty :: S.Set String -> PreparedQueryProperty -> PreparedQueryProperty
annotateQueryProperty ruleIdEvents prepared =
  prepared
    { preparedQueryFormulas = fmap annotateQuery prepared.preparedQueryFormulas
    }
  where
    annotateQuery queryFormula =
      queryFormula
        { preparedQueryBody =
            annotatePreparedFormula
              queryFormula.preparedQueryRuleIdStrategy
              ruleIdEvents
              queryFormula.preparedQueryBody
        }

annotateAxiomProperty :: S.Set String -> PreparedAxiomProperty -> PreparedAxiomProperty
annotateAxiomProperty ruleIdEvents prepared =
  prepared
    { preparedAxiomFormulas =
        fmap (annotatePreparedFormula SharedRuleIdWhenSingle ruleIdEvents) prepared.preparedAxiomFormulas
    }

annotateRestrictionProperty :: S.Set String -> PreparedRestrictionProperty -> PreparedRestrictionProperty
annotateRestrictionProperty ruleIdEvents prepared =
  prepared
    { preparedRestrictionFormulas =
        fmap (annotatePreparedFormula SharedRuleIdWhenSingle ruleIdEvents) prepared.preparedRestrictionFormulas
    }

preparedFormulaRuleIdEvents :: PreparedFormula -> S.Set String
preparedFormulaRuleIdEvents prepared =
  formulaRuleIdEventsWithOrigins prepared.preparedTimeOrigins prepared.preparedFormula

-- | Whether an existential conclusion is allowed in the checked fragment.
data ConclusionFragment = AllowExistentialConclusion | ForbidExistentialConclusion
  deriving (Eq, Ord, Show)

supportsUniversalFormula :: MonadFresh m => ConclusionFragment -> LNFormula -> m Bool
supportsUniversalFormula _ body
  | isQuantifierFree body = pure True
supportsUniversalFormula _ (Conn Imp premise conclusion)
  | isQuantifierFree premise = do
      existentialDisjunction <- isExistentialDisjunction conclusion
      if existentialDisjunction
        then pure True
        else isNestedImplicationOk conclusion
supportsUniversalFormula AllowExistentialConclusion quantified@(Qua Ex _ _) = do
  (_, _, body) <- openFormulaPrefix quantified
  supportsUniversalFormula AllowExistentialConclusion body
supportsUniversalFormula _ _ = pure False

supportsQueryFormula :: LNFormula -> Bool
supportsQueryFormula formula =
  Precise.evalFresh (go formula) (avoidPrecise formula)
  where
    go frm
      | formulaContainsKUFact frm = pure False
    go (Not fm@(Qua {})) = go fm
    go fm@(Qua Ex _ _) = do
      (_, _, body) <- openFormulaPrefix fm
      pure (isQuantifierFree body)
    go fm@(Qua All _ _) = do
      (_, _, body) <- openFormulaPrefix fm
      supportsUniversalFormula AllowExistentialConclusion body
    go _ = pure False

supportsAssumptionFormula :: LNFormula -> Bool
supportsAssumptionFormula formula
  | formulaContainsKUFact formula = False
  | hasUnsupportedPremiseTimeConstraint formula && not (hasDistinctFact formula) = False
  | hasTopLevelNegatedAction formula = False
  | hasNestedImplicationInConclusion formula = False
  | otherwise = Precise.evalFresh (go formula) (avoidPrecise formula)
  where
    go fm@(Not (Qua Ex _ _))
      | isSimpleNegatedAction fm = pure False
    go (Not fm@(Qua Ex _ _)) = do
      (_, _, body) <- openFormulaPrefix fm
      pure (isQuantifierFree body)
    go fm@(Qua All _ _) = do
      (_, _, body) <- openFormulaPrefix fm
      supportsUniversalFormula ForbidExistentialConclusion body
    go _ = pure False

hasNestedImplicationInConclusion :: LNFormula -> Bool
hasNestedImplicationInConclusion = check False
  where
    check inConclusion (Qua _ _ body) = check inConclusion body
    check False (Conn Imp _ conclusion) = check True conclusion
    check True (Conn Imp _ _) = True
    check inConclusion (Conn _ left right) = check inConclusion left || check inConclusion right
    check inConclusion (Not body) = check inConclusion body
    check _ _ = False

hasDistinctFact :: LNFormula -> Bool
hasDistinctFact =
  any (\(Fact tag _ _) -> factTagName tag == "DistinctFact") . formulaFacts

requiresAxiomTimepoints :: LNFormula -> Bool
requiresAxiomTimepoints formula = hasDistinctFact formula || conclusionHasTimeConstraint formula
  where
    actionTimepoints = formulaActionTimepoints formula
    conclusionHasTimeConstraint (Qua _ _ body) = conclusionHasTimeConstraint body
    conclusionHasTimeConstraint (Conn Imp _ conclusion) = hasTimeConstraint conclusion
    conclusionHasTimeConstraint body = hasTimeConstraint body
    hasTimeConstraint =
      foldFormula
        (\case
            EqE left right -> left `elem` actionTimepoints || right `elem` actionTimepoints
            Less _ _ -> True
            _ -> False
        )
        (const False)
        id
        (\_ left right -> left || right)
        (\_ _ body -> body)

hasUnsupportedPremiseTimeConstraint :: LNFormula -> Bool
hasUnsupportedPremiseTimeConstraint formula = go False formula
  where
    actionTimepoints = formulaActionTimepoints formula
    hasConstraint = foldFormula atomConstraint (const False) id (\_ l r -> l || r) (\_ _ body -> body)
    atomConstraint (Less _ _) = True
    atomConstraint (EqE left _) = left `elem` actionTimepoints
    atomConstraint _ = False
    go inConclusion (Qua _ _ body) = go inConclusion body
    go False (Conn Imp premise conclusion) = hasConstraint premise || go True conclusion
    go inConclusion (Conn _ left right) = go inConclusion left || go inConclusion right
    go inConclusion (Not body) = go inConclusion body
    go True _ = False
    go False (Ato atom) = atomConstraint atom
    go False _ = False

formulaActionTimepoints :: LNFormula -> [VTerm Name (BVar LVar)]
formulaActionTimepoints =
  foldFormula
    (\case Action timepoint _ -> [timepoint]; _ -> [])
    (const [])
    id
    (\_ left right -> left ++ right)
    (\_ _ body -> body)


hasNegatedActionInFormula :: LNFormula -> Bool
hasNegatedActionInFormula (Not (Ato (Action _ _))) = True
hasNegatedActionInFormula (Not (Qua All _ body)) = containsAction body
  where
    containsAction (Ato (Action _ _)) = True
    containsAction (Qua All _ b) = containsAction b
    containsAction (Qua Ex _ b) = containsAction b
    containsAction (Conn _ p q) = containsAction p || containsAction q
    containsAction _ = False
-- Recurse through quantifiers and connectives to find nested negated actions
hasNegatedActionInFormula (Qua _ _ body) = hasNegatedActionInFormula body
hasNegatedActionInFormula (Conn _ p q) = hasNegatedActionInFormula p || hasNegatedActionInFormula q
hasNegatedActionInFormula _ = False

-- | Check if a formula has a negated action that cannot be translated to ProVerif.
-- The pattern Not (Qua Ex ...) at the TOP level is fine - it becomes a reachability query
-- with a "leading negation" comment. What we need to reject is negated actions
-- INSIDE a query body, like: A ==> not(Ex x. B(x)@i) where the negation is in the conclusion
-- of an implication, or bare Not (Ato (Action _ _)).
--
-- NOTE: For queries, Not (Qua Ex _ body) is VALID and handled by renderFormula which
-- strips the Not and emits the inner existential as a reachability query.
hasTopLevelNegatedAction :: LNFormula -> Bool
hasTopLevelNegatedAction (Not (Ato (Action _ _))) = True
-- Not (Qua Ex ...) at the very top level is fine - it's handled as a leading negation query
-- We only need to check inside quantifiers or connectives
hasTopLevelNegatedAction (Qua All _ body) = hasTopLevelNegatedAction body
hasTopLevelNegatedAction (Qua Ex _ body) = hasTopLevelNegatedAction body
hasTopLevelNegatedAction (Conn And p q) = hasTopLevelNegatedAction p || hasTopLevelNegatedAction q
hasTopLevelNegatedAction (Conn Or p q) = hasTopLevelNegatedAction p || hasTopLevelNegatedAction q
-- Check for negated events inside implications (conclusion)
hasTopLevelNegatedAction (Conn Imp _ concl) = hasNegatedEventInConclusion concl
  where
    -- Check if conclusion contains a negated event that ProVerif can't handle
    hasNegatedEventInConclusion (Not (Ato (Action _ _))) = True
    hasNegatedEventInConclusion (Not (Qua Ex _ _)) = True  -- not(Ex ...) in conclusion is problematic
    hasNegatedEventInConclusion (Conn And p q) = hasNegatedEventInConclusion p || hasNegatedEventInConclusion q
    hasNegatedEventInConclusion (Conn Or p q) = hasNegatedEventInConclusion p || hasNegatedEventInConclusion q
    hasNegatedEventInConclusion _ = False
hasTopLevelNegatedAction _ = False

-- Property splitting always retains at least the unsplit source formula.
-- Reaching the empty case therefore indicates an internal preparation bug,
-- not unsupported user input.
preparedNonEmpty :: String -> [a] -> NE.NonEmpty a
preparedNonEmpty propertyKind =
  fromMaybe
    (translationInvariantFail ("property preparation invariant failed: emitted " ++ propertyKind ++ " has no formulas"))
    . NE.nonEmpty
