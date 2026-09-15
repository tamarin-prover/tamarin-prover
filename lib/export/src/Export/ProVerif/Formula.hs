-- |
-- Pure ProVerif formula normalization, fragment checks, and transformations.
module Export.ProVerif.Formula
  ( allImplExLessWoTmps,
    applyRewriteForShape,
    assumptionKnowledgeFragmentFailure,
    classifyFormulaShape,
    collectActionsWithTimepoints,
    collectBinderHintNames,
    collectBinderHints,
    collectQuantifierPrefix,
    collectTemporalEqKeyPairs,
    countQuantifierAlternations,
    eliminateTemporalEqualities,
    eventsSharingTimepoints,
    expandNegatedTimepointComparisons,
    flattenConjuncts,
    flattenNestedImplications,
    formulaContainsAction,
    formulaContainsKUFact,
    formulaHasSharedTimepoints,
    hasNegatedEventInFormula,
    hasNestedImplicationInConjunction,
    hasVariableCaptureInNestedImplication,
    isAllImpliesExists,
    isExistentialDisjunction,
    isExistsWithNegatedExistentials,
    isKnowledgeFact,
    isNegatedExistsWithConjunction,
    isNestedImplicationOk,
    isQuantifierFree,
    isSimpleNegatedAction,
    isSupportedPositivePremise,
    makeBinderHintsGloballyUnique,
    mapTopLevelConjunctsFormula,
    moveConstraintsToConclusion,
    moveNegatedActionsToConclusion,
    normalizeAllTraceFormula,
    pullNegationsWithDiagnostic,
    queryKnowledgeFragmentFailure,
    rewriteEventFreeExistsTrace,
    rewriteFormulaForAxiomWithDiagnostic,
    rewriteFormulaForQuery,
    rewritePositiveWitnessExistsTrace,
    splitTopLevel,
    universalNegationAsExists,
  )
where

import Control.Monad.Fresh
import Control.Monad.Trans.PreciseFresh qualified as Precise
import Data.List as List
import Data.Map qualified as M
import Data.Maybe
import Data.Set qualified as S
import Export.Name (freshNameAvoiding)
import Theory
import Utils.Misc (fixpoint)
import Theory.Tools.Wellformedness (formulaFacts)

-- | Flatten nested conjunctions into the list of their conjuncts.
flattenConjuncts :: LNFormula -> [LNFormula]
flattenConjuncts (Conn And p q) = flattenConjuncts p ++ flattenConjuncts q
flattenConjuncts formula = [formula]

-- | Flatten nested disjunctions into the list of their disjuncts.
flattenDisjuncts :: LNFormula -> [LNFormula]
flattenDisjuncts (Conn Or p q) = flattenDisjuncts p ++ flattenDisjuncts q
flattenDisjuncts formula = [formula]

-- | Collect the leading binders of one quantifier kind, outermost first,
-- together with the remaining body.
collectQuantifierPrefix :: Quantifier -> LNFormula -> ([(String, LSort)], LNFormula)
collectQuantifierPrefix q (Qua q' v body)
  | q == q' =
      let (rest, inner) = collectQuantifierPrefix q body
       in (v : rest, inner)
collectQuantifierPrefix _ body = ([], body)

-- | Collect the binder hints of all quantifiers in a formula, outermost first.
collectBinderHints :: LNFormula -> [(String, LSort)]
collectBinderHints (Qua _ binderHint body) = binderHint : collectBinderHints body
collectBinderHints (Not body) = collectBinderHints body
collectBinderHints (Conn _ left right) = collectBinderHints left ++ collectBinderHints right
collectBinderHints _ = []

-- | The set of binder-hint names of all quantifiers in a formula.
collectBinderHintNames :: LNFormula -> S.Set String
collectBinderHintNames = S.fromList . map fst . collectBinderHints

-- | Check whether a formula is an existentially quantified attacker-knowledge action.
isExistentialKAction :: LNFormula -> Bool
isExistentialKAction formula =
  case collectQuantifierPrefix Ex formula of
    (_ : _, Ato (Action _ fact)) -> isKLogFact fact
    _ -> False

formulaContainsAction :: LNFormula -> Bool
formulaContainsAction = not . null . formulaFacts

isSupportedPositivePremise :: LNFormula -> Bool
isSupportedPositivePremise = isSupportedPositiveFormula PositivePremise

-- | Positive formulas accepted in a correspondence conclusion.  Existential
-- quantifiers are allowed, but positive universals and negated actions are
-- not part of ProVerif's correspondence fragment.
isSupportedPositiveConclusion :: LNFormula -> Bool
isSupportedPositiveConclusion = isSupportedPositiveFormula PositiveConclusion

data PositiveFormulaPosition
  = PositivePremise
  | PositiveConclusion

isSupportedPositiveFormula :: PositiveFormulaPosition -> LNFormula -> Bool
isSupportedPositiveFormula PositiveConclusion (Qua Ex _ body) =
  isSupportedPositiveFormula PositiveConclusion body
isSupportedPositiveFormula _ (Ato (Action _ _)) = True
isSupportedPositiveFormula _ (Ato (EqE _ _)) = True
isSupportedPositiveFormula _ (Ato (Less _ _)) = True
isSupportedPositiveFormula _ (Not (Ato (EqE _ _))) = True
isSupportedPositiveFormula _ (Not (Ato (Less _ _))) = True
isSupportedPositiveFormula position (Conn And left right) =
  isSupportedPositiveFormula position left && isSupportedPositiveFormula position right
isSupportedPositiveFormula position (Conn Or left right) =
  isSupportedPositiveFormula position left && isSupportedPositiveFormula position right
isSupportedPositiveFormula _ (TF True) = True
isSupportedPositiveFormula PositiveConclusion (TF False) = True
isSupportedPositiveFormula _ _ = False

-- | Knowledge atoms need separate fragment checks before any query rewriting.
-- KU is an internal message-deduction annotation and is outside the formal
-- translation.  K is supported for all-trace properties only when every K
-- occurrence is positive in NNF(not phi), exactly as required by T-UKF.
-- Restrictions and reuse/source axioms are assumptions, so their direct
-- preservation instead requires positive K occurrences in NNF(phi).
formulaContainsKUFact :: LNFormula -> Bool
formulaContainsKUFact =
  any (\(Fact tag _ _) -> tag == KUFact) . formulaFacts

formulaContainsKFact :: LNFormula -> Bool
formulaContainsKFact =
  any isKLogFact . formulaFacts

isKnowledgeFact :: Fact t -> Bool
isKnowledgeFact fact@(Fact tag _ _) = tag == KUFact || isKLogFact fact

hasNegativeKInNNF :: LNFormula -> Bool
hasNegativeKInNNF = go . nnf . simplifyFormula
  where
    go (Not (Ato (Action _ fact))) = isKLogFact fact
    go (Not body) = go body
    go (Conn _ left right) = go left || go right
    go (Qua _ _ body) = go body
    go _ = False

hasNegativeKInNegatedNNF :: LNFormula -> Bool
hasNegativeKInNegatedNNF = hasNegativeKInNNF . Not

queryKnowledgeFragmentFailure :: TraceQuantifier -> LNFormula -> Maybe String
queryKnowledgeFragmentFailure traceQuantifier formula
  | formulaContainsKUFact formula =
      Just "formula contains KU fact, which is outside the supported formal semantics"
  | traceQuantifier == ExistsTrace && formulaContainsKFact formula =
      Just "exists-trace formula contains K fact; completeness is only proved for K-free formulas"
  | hasNegativeKInNegatedNNF formula =
      Just "formula is outside T-UKF: NNF(not(phi)) contains a negative K atom"
  | otherwise = Nothing

assumptionKnowledgeFragmentFailure :: LNFormula -> Maybe String
assumptionKnowledgeFragmentFailure formula
  | formulaContainsKUFact formula =
      Just "formula contains KU fact, which is outside the supported formal semantics"
  | hasNegativeKInNNF formula =
      Just "NNF(phi) contains a negative K atom, which cannot be translated soundly as an assumption"
  | otherwise = Nothing

-- | Rebuild a quantifier prefix around a body that already contains the
-- corresponding de Bruijn-bound variables. This deliberately uses 'Qua'
-- directly: 'forAll' and 'exists' quantify free variables instead.
-- Quantifiers are applied from outer to inner, so the first hint becomes the
-- outermost quantifier.
-- | Apply the structural rewrites shared by query rendering and
-- property-driven instrumentation analysis. Keeping this as one pipeline is
-- important: completion demand must be computed from the correspondence that
-- is actually rendered, after negative premise actions have moved to the
-- conclusion.
rewriteFormulaForQuery :: TraceQuantifier -> LNFormula -> LNFormula
rewriteFormulaForQuery traceQuantifier fm =
  let fmInj
        | traceQuantifier == AllTraces = rewriteInjectiveAgreement fm
        | otherwise = fm
      fm0 = eliminateTemporalEqualities fmInj
      fm1 = eliminateDoubleNegations fm0
      fm1a = moveNegatedActionsToConclusion fm1
      fm1b = convertNegExWithTimeConstraint fm1a
      shape = classifyFormulaShape traceQuantifier fm1b
   in flattenNestedQuantifiers (applyRewriteForShape shape fm1b)
  where
    flattenNestedQuantifiers (Qua All x body) =
      case flattenNestedQuantifiers body of
        Conn Imp prem concl
          | needsFlatteningInConclusion concl -> Qua All x (Conn Imp prem (pnf concl))
          | otherwise -> Qua All x (Conn Imp prem concl)
        body' -> Qua All x body'
    flattenNestedQuantifiers (Conn Imp prem concl)
      | needsFlatteningInConclusion concl = Conn Imp prem (pnf concl)
      | otherwise = Conn Imp prem concl
    flattenNestedQuantifiers formula@(Qua Ex _ _) = pnf formula
    flattenNestedQuantifiers (Not formula@(Qua Ex _ _)) = Not (pnf formula)
    flattenNestedQuantifiers (Conn And left right) =
      Conn And
        (flattenNestedQuantifiers left)
        (flattenNestedQuantifiers right)
    flattenNestedQuantifiers formula = formula

    needsFlatteningInConclusion (Qua Ex _ body) =
      needsFlatteningInConclusion body
    needsFlatteningInConclusion (Conn And left right) =
      hasNestedEx left || hasNestedEx right
    needsFlatteningInConclusion (Conn Or _ _) = False
    needsFlatteningInConclusion _ = False

    hasNestedEx (Qua Ex _ _) = True
    hasNestedEx (Conn And left right) =
      hasNestedEx left || hasNestedEx right
    hasNestedEx _ = False

-- | Pull negations to the top level, reporting a partial normalization as an
-- approximation note for the given property kind.
pullNegationsWithDiagnostic :: String -> LNFormula -> (LNFormula, Maybe String)
pullNegationsWithDiagnostic propertyKind formula =
  case pullNegationsToTop formula of
    Left partiallyNormalized ->
      ( partiallyNormalized,
        Just
          ( "negations could only be partially normalized; the emitted "
              ++ propertyKind
              ++ " is an approximation"
          )
      )
    Right fullyNormalized -> (fullyNormalized, Nothing)

rewriteFormulaForAxiomWithDiagnostic :: LNFormula -> (LNFormula, Maybe String)
rewriteFormulaForAxiomWithDiagnostic formula =
  ( simplifyFormula
      . flattenNestedImplications
      . expandNegatedTimepointComparisons
      $ pulled,
    approximation
  )
  where
    beforePull =
      moveConstraintsToConclusion
        . moveNegatedActionsToConclusion
        . eliminateTemporalEqualities
        $ formula
    (pulled, approximation) = pullNegationsWithDiagnostic "axiom" beforePull

mapTopLevelConjunctsFormula :: (LNFormula -> LNFormula) -> LNFormula -> LNFormula
mapTopLevelConjunctsFormula f (Conn And left right) =
  Conn And
    (mapTopLevelConjunctsFormula f left)
    (mapTopLevelConjunctsFormula f right)
mapTopLevelConjunctsFormula f fm = f fm

-- | Make quantifier hints unique throughout a formula without changing any
-- de Bruijn references. Some equivalence-preserving rewrites duplicate closed
-- quantified scopes or move independently scoped formulas next to each other.
-- The later shared-timepoint analysis uses binder hints to recover occurrence
-- groups, so equal hints from independent scopes must not be conflated.
makeBinderHintsGloballyUnique :: LNFormula -> LNFormula
makeBinderHintsGloballyUnique formula = snd (go S.empty formula)
  where
    reserved = collectBinderHintNames formula

    go used (Qua q (name, srt) body) =
      let name'
            | name `S.notMember` used = name
            | otherwise = freshNameAvoiding "_" (reserved `S.union` used) name
          (used', body') = go (S.insert name' used) body
       in (used', Qua q (name', srt) body')
    go used (Not body) =
      let (used', body') = go used body
       in (used', Not body')
    go used (Conn conn left right) =
      let (used', left') = go used left
          (used'', right') = go used' right
       in (used'', Conn conn left' right')
    go used body = (used, body)

-- | Check if a formula represents a valid existential disjunction pattern.
-- Valid patterns include:
-- - An existential formula with quantifier-free body
-- - A disjunction of existential formulas
-- - A temporal/equality constraint: #i < #j, x = y
-- - A bare action atom (from moved negated actions)
-- - A nested implication: All x. P => Q (where Q is valid conclusion)
isExistentialDisjunction :: MonadFresh m => LNFormula -> m Bool
isExistentialDisjunction fm@(Qua Ex _ _) = do
  (_, _, fm') <- openFormulaPrefix fm
  -- Accept either quantifier-free bodies or nested existential/disjunctive structure.
  if isQuantifierFree fm'
    then pure True
    else isExistentialDisjunction fm'
-- Handle universals (nested implications): All x. P => Q
isExistentialDisjunction fm@(Qua All _ _) = do
  (_, _, fm') <- openFormulaPrefix fm
  isExistentialDisjunction fm'
-- Handle implications: P => Q (nested implication body)
isExistentialDisjunction (Conn Imp p q) | isQuantifierFree p = do
  -- The premise must be quantifier-free, conclusion can be:
  -- quantifier-free, existential, or another nested implication
  if isQuantifierFree q
    then pure True
    else isExistentialDisjunction q
-- Handle disjunctions: (Ex...) | (Ex...) | ...
isExistentialDisjunction (Conn Or fm1 fm2) = do
  b1 <- isExistentialDisjunction fm1
  b2 <- isExistentialDisjunction fm2
  pure $ b1 && b2
-- Handle conjunctions: (Ex...) & (Ex...) & ... or (All...) & (Ex...)
-- This allows patterns like: ((Ex #j. A@j) & (Ex #k. B@k)) | ((Ex #r. C@r) & (Ex #t. D@t))
-- Also allows: (All #j. B@j => C) & (Ex #k. D@k)
isExistentialDisjunction (Conn And fm1 fm2) = do
  b1 <- isExistentialDisjunction fm1
  b2 <- isExistentialDisjunction fm2
  pure $ b1 && b2
isExistentialDisjunction fm | isConstraintAtom fm = pure True
isExistentialDisjunction fm | isBareActionAtom fm = pure True
isExistentialDisjunction (TF _) = pure True
isExistentialDisjunction _ = pure False

-- | Check if a formula is a temporal or equality constraint
isConstraintAtom :: LNFormula -> Bool
isConstraintAtom (Ato (Less _ _)) = True
isConstraintAtom (Ato (EqE _ _)) = True
isConstraintAtom (Not (Ato (EqE _ _))) = True
isConstraintAtom (Conn Or f1 f2) = isConstraintAtom f1 && isConstraintAtom f2
isConstraintAtom _ = False

-- | Check if a formula is a bare action atom
isBareActionAtom :: LNFormula -> Bool
isBareActionAtom (Ato (Action _ _)) = True
isBareActionAtom _ = False

-- | Check if a formula is a nested implication that can be flattened.
-- Pattern: All x. Q => R  where Q is quantifier-free and R is quantifier-free or existential disjunction
-- This is equivalent to adding Q to the premise.
isNestedImplicationOk :: MonadFresh m => LNFormula -> m Bool
isNestedImplicationOk fm@(Qua All _ _) = do
  (_, _, fm') <- openFormulaPrefix fm
  isNestedImplicationOk fm'
isNestedImplicationOk (Conn Imp q r) | isQuantifierFree q = do
  -- The nested premise q must be quantifier-free
  -- The nested conclusion r can be:
  -- 1. Quantifier-free (like #i < #j)
  -- 2. An existential disjunction
  -- 3. Another nested implication
  if isQuantifierFree r
    then pure True
    else do
      isExDisj <- isExistentialDisjunction r
      if isExDisj
        then pure True
        else isNestedImplicationOk r
isNestedImplicationOk _ = pure False

isQuantifierFree :: LNFormula -> Bool
isQuantifierFree (Qua {}) = False
isQuantifierFree (Ato _) = True
isQuantifierFree (TF _) = True
isQuantifierFree (Not p) = isQuantifierFree p
isQuantifierFree (Conn _ p q) = isQuantifierFree p && isQuantifierFree q

-- | Count the number of quantifier alternations in a formula.
-- An alternation occurs when we switch from All to Ex or vice versa.
-- For example:
--   All x. P(x)                     -> 0 alternations (All only)
--   All x. Ex y. P(x,y)             -> 1 alternation  (All -> Ex)
--   All x. Ex y. not(Ex z. Q)       -> 2 alternations (All -> Ex -> All, since not(Ex) = All)
--   All x. (P(x) => Ex y. Q(y))     -> 1 alternation  (All -> Ex)
-- The supported fragment has at most 1 alternation: All* (premise => Ex* conclusion)
countQuantifierAlternations :: LNFormula -> Int
countQuantifierAlternations = go Nothing
  where
    -- go tracks the current quantifier context (Nothing = none yet, Just All/Ex = last seen)
    go :: Maybe Quantifier -> LNFormula -> Int
    go _ (Ato _) = 0
    go _ (TF _) = 0
    go ctx (Not (Qua Ex v body)) = go ctx (Qua All v body)  -- not(Ex) = All
    go ctx (Not (Qua All v body)) = go ctx (Qua Ex v body)  -- not(All) = Ex
    go ctx (Not body) = go ctx body
    go ctx (Qua q _ body) =
      let alternation = case ctx of
            Nothing -> 0  -- First quantifier, no alternation
            Just q' -> if q == q' then 0 else 1  -- Same quantifier = 0, different = 1
          bodyAlternations = go (Just q) body
      in alternation + bodyAlternations
    go ctx (Conn _ p q) = max (go ctx p) (go ctx q)


-- | Classification of formula shapes for rewriting.
-- Formulas are classified by their top-level structure to determine
-- which rewrite strategy to apply. Each shape maps to exactly one
-- transformation strategy.
--
-- Listed in priority order (first match wins during classification).
data FormulaShape
    = ShapeAllActionsImpliesNotExists
      -- ^ ∀x. (A@i ⇒ ¬∃y. B@j)
      -- Action: Convert to PNF

    | ShapeNotExistsConj
      -- ^ ¬(∃x. P ∧ Q ∧ ¬R) with exactly one negation
      -- Action: Pull negations, convert ¬A∨B to A⇒B

    | ShapeExistsConjNotExists
      -- ^ ∃x. (P ∧ ¬∃y. Q)  [only for existential trace quantifier]
      -- Action: Rearrange conjuncts, convert A∧¬B to A⇒B

    | ShapeAllImpliesDisjWithNegations
      -- ^ ∀x. (P ⇒ ¬Q₁ ∨ ¬Q₂ ∨ R)
      -- Action: Move negated disjuncts to premise

    | ShapeAllImpliesConjWithNegations
      -- ^ ∀x. (P ⇒ ¬Q₁ ∧ ¬Q₂)
      -- Action: Distribute implication over conjunction to create
      -- (∀x. P ⇒ ¬Q₁) ∧ (∀x. P ⇒ ¬Q₂) which gets split by splitTopLvlConns

    | ShapeOther
      -- ^ No special structure detected
      -- Action: No structural rewrite needed (identity transform)
    deriving (Eq, Show)

-- | Classify a formula's shape for rewriting.
-- This examines the formula structure after double negation elimination
-- and determines which rewrite strategy should be applied.
classifyFormulaShape :: TraceQuantifier -> LNFormula -> FormulaShape
classifyFormulaShape traceQuant fm
    | isAllActionsImpliesNotExists fm = ShapeAllActionsImpliesNotExists
    | isNegatedExistsWithConjunction fm = ShapeNotExistsConj
    | isExistsWithNegatedExistentials fm && traceQuant == ExistsTrace = ShapeExistsConjNotExists
    | isAllImpliesConjWithNegations fm = ShapeAllImpliesConjWithNegations
    | isAllImpliesDisjWithNegations fm = ShapeAllImpliesDisjWithNegations
    | otherwise = ShapeOther

-- | Apply the rewrite strategy for a given formula shape.
-- Each shape has exactly one associated transformation.
applyRewriteForShape :: FormulaShape -> LNFormula -> LNFormula
applyRewriteForShape shape fm = case shape of
    ShapeAllActionsImpliesNotExists  -> convertPnfToNegatedExists $ pnf fm
    ShapeNotExistsConj               -> transformNotExistsConjToImplication fm
    ShapeExistsConjNotExists         -> transformExistsConjToNegatedImplication fm
    ShapeAllImpliesConjWithNegations -> distributeImplicationOverConjunction fm
    ShapeAllImpliesDisjWithNegations -> moveNegatedDisjunctsToPremise fm
    ShapeOther                       -> fm
  where
    -- Convert the result of pnf to negated existential form
    -- pnf(All x. A ==> not(Ex y. B)) = All x y. not(A) | not(B)
    -- We want: not(Ex x y. A & B) which renders as a conjunction with leading negation
    -- This is the standard form for reachability queries with negation
    convertPnfToNegatedExists :: LNFormula -> LNFormula
    convertPnfToNegatedExists formula =
        -- Collect all quantifiers and the body
        let (quants, body) = collectQuantifiers formula
            -- Extract the negated atoms from the disjunction
            atoms = collectNegatedAtoms body
            -- Build the conjunction and wrap with existentials, then negate
            conjunction = buildConjunction atoms
            existential = rewrapBoundPrefix Ex quants conjunction
        in Not existential

    collectQuantifiers :: LNFormula -> ([(String, LSort)], LNFormula)
    collectQuantifiers (Qua All (name, srt) body) =
        let (rest, innerBody) = collectQuantifiers body
        in ((name, srt) : rest, innerBody)
    collectQuantifiers (Qua Ex (name, srt) body) =
        let (rest, innerBody) = collectQuantifiers body
        in ((name, srt) : rest, innerBody)
    collectQuantifiers f = ([], f)

    collectNegatedAtoms :: LNFormula -> [LNFormula]
    collectNegatedAtoms (Conn Or p q) = collectNegatedAtoms p ++ collectNegatedAtoms q
    collectNegatedAtoms (Not p) = [p]
    collectNegatedAtoms _ = []

-- | Split a conditional safety property by whether a witness exists.  The
-- source formula is a negated existential attack whose safety conditions
-- contain:
--
--   * a universal condition for every matching witness; and
--   * an implication that supplies a fallback condition when no witness
--     exists.
--
-- Writing Base for the positive attack premise, OuterBad for its direct
-- violations, M for the witness predicate, BadM for violations attached to a
-- witness, and H for the no-witness fallback, the attack is excluded exactly
-- when both of these correspondences hold:
--
--   Base & M ==> OuterBad | BadM
--   Base     ==> OuterBad | M | not(H)
--
-- The positive M branch in the second correspondence is essential. This
-- recognizer depends only on formula structure, polarity, scoping, and the
-- supported positive correspondence fragment.  It never inspects fact names.
rewriteConditionalExistenceCase :: LNFormula -> Maybe LNFormula
rewriteConditionalExistenceCase fm0@(Not outerEx@(Qua Ex _ _)) =
  Precise.evalFresh attempt (avoidPrecise fm0)
  where
    attempt = do
      (outerVars, _, body) <- openFormulaPrefix outerEx
      let conjuncts = flattenConjuncts body
          indexed = zip [0 :: Int ..] conjuncts
          outerNegatives =
            [ (idx, positive)
            | (idx, Not positive@(Qua Ex _ _)) <- indexed
            ]
          matchingGuards =
            [ (idx, guarded)
            | (idx, guarded@(Qua All _ _)) <- indexed
            ]
          noMatchGuards =
            [ (idx, (matching, fallback))
            | (idx, Conn Imp (Not matching@(Qua Ex _ _)) fallback) <- indexed
            ]
      case (matchingGuards, noMatchGuards) of
        ( [(matchingIdx, matchingGuard)],
          [(noMatchIdx, (matchingExists, fallback))]
          ) -> do
            parsedMatching <- parseMatchingGuard matchingGuard
            let fallbackViolations = positiveNegatedExistentials fallback
                recognized =
                  S.fromList
                    ([matchingIdx, noMatchIdx] ++ map fst outerNegatives)
                baseParts =
                  [ formula
                  | (idx, formula) <- indexed,
                    idx `S.notMember` recognized
                  ]
                outerViolations = map snd outerNegatives
            case (parsedMatching, fallbackViolations) of
              (Just (matchingVars, matchingPremise, matchingViolations), Just fallbackBad)
                | not (null baseParts),
                  all isSupportedPositivePremise baseParts,
                  formulaContainsAction (buildConjunction baseParts),
                  isSupportedPositivePremise matchingPremise,
                  formulaContainsAction matchingPremise,
                  all isSupportedPositiveConclusion
                    (outerViolations ++ matchingViolations ++ fallbackBad),
                  sameMatchingExistence matchingGuard matchingExists -> do
                    let base = buildConjunction baseParts
                        first =
                          Conn Imp
                            (Conn And base matchingPremise)
                            (buildDisjunction (outerViolations ++ matchingViolations))
                        second =
                          Conn Imp
                            base
                            (buildDisjunction (outerViolations ++ [matchingExists] ++ fallbackBad))
                        firstClosed =
                          foldr (hinted forAll) first (outerVars ++ matchingVars)
                        secondClosed = foldr (hinted forAll) second outerVars
                    pure $
                      Just $
                        makeBinderHintsGloballyUnique
                          (Conn And firstClosed secondClosed)
              _ -> pure Nothing
        _ -> pure Nothing

    parseMatchingGuard guarded = do
      (matchingVars, _, guardedBody) <- openFormulaPrefix guarded
      pure $ case guardedBody of
        Conn Imp matchingPremise safeMatching ->
          case positiveNegatedExistentials safeMatching of
            Just violations ->
              Just (matchingVars, matchingPremise, violations)
            Nothing -> Nothing
        _ -> Nothing

    -- The universal guard and the no-match premise must quantify the same
    -- matching-session predicate. Compare their de Bruijn bodies directly,
    -- ignoring only the All/Ex quantifier kinds and binder hints.
    sameMatchingExistence guarded matching =
      case (stripQuantifierPrefix All guarded, stripQuantifierPrefix Ex matching) of
        ((guardSorts, Conn Imp guardedPremise _), (matchSorts, matchingBody)) ->
          guardSorts == matchSorts && guardedPremise == matchingBody
        _ -> False

    stripQuantifierPrefix quantifier = go []
      where
        go sorts (Qua q (_, srt) body)
          | q == quantifier = go (srt : sorts) body
        go sorts body = (reverse sorts, body)

    positiveNegatedExistentials formula =
      traverse positiveOf (flattenConjuncts formula)
      where
        positiveOf (Not positive@(Qua Ex _ _))
          | isSupportedPositiveConclusion positive = Just positive
        positiveOf _ = Nothing

rewriteConditionalExistenceCase _ = Nothing

-- | Rewrite the standard injective-agreement idiom into an equivalent
-- conjunction of two fragment-supported lemmas.
--
-- The idiom (Lowe's injective agreement, as encoded throughout the example
-- corpus; fact symbols vary per model):
--
--   All xs #i. P(as)@i ==>
--     (Ex #j. W(bs)@j & #j < #i
--        & not(Ex ys #i2. P(cs)@i2 & not(#i2 = #i)))
--     | R1 | .. | Rn
--
-- is rewritten to the conjunction of
--
--   (a) All xs #i. P(as)@i ==> (Ex #j. W(bs)@j & #j < #i) | R1 | .. | Rn
--   (b) All xs ys #i #i2. P(as)@i & P(cs)@i2 ==> #i = #i2 | R1 | .. | Rn
--
-- (a) is the non-injective correspondence; (b) states that no two distinct
-- P-instances share the session parameters unless one of the escape
-- disjuncts (typically key reveals) applies; the timepoint equality is
-- rendered as a rule-id equality. Note the escape disjuncts must be carried
-- into (b): the original lemma excuses duplicated commits through them.
-- The conjunction is equivalent: the original implies (a) by weakening,
-- and (b) because for a second P with the same parameters at a different
-- timepoint the witness branch is contradicted, leaving the escapes;
-- conversely, given P and no escape, (a) provides the witness and (b)
-- discharges the negated existential. The top-level-connective splitting
-- then emits two ProVerif queries whose results are recombined with a
-- conjunction.
--
-- The variant that states uniqueness as a universal implication
-- 'All ys #i2. P(cs)@i2 ==> #i2 = #i' is handled identically.
--
-- The rewrite only fires on this exact shape: a single positive
-- (non-attacker) action premise over the correspondence's only outer
-- timepoint binder, and exactly one uniqueness conjunct (over the premise's
-- fact symbol) in exactly one conclusion disjunct. Top-level conjunctions
-- are handled recursively, one correspondence at a time.
rewriteInjectiveAgreement :: LNFormula -> LNFormula
rewriteInjectiveAgreement (Conn And left right) =
  Conn And
    (rewriteInjectiveAgreement left)
    (rewriteInjectiveAgreement right)
rewriteInjectiveAgreement fm0@(Qua All _ _) =
  let rewritten =
        fromMaybe fm0 $ Precise.evalFresh attempt (avoidPrecise fm0)
   in
    if rewritten /= fm0 && formulaHasSharedTimepoints fm0
      then makeBinderHintsGloballyUnique rewritten
      else rewritten
  where
    attempt = do
      (allVars, _, body) <- openFormulaPrefix fm0
      case body of
        Conn Imp (Ato prem@(Action pTime pf@(Fact ptag _ _))) concl
          | [iP] <- [v | v <- allVars, lvarSort v == LSortNode],
            pTime == varTerm (Free iP),
            ptag /= KUFact && not (isKLogFact pf) -> do
              let disjs = flattenDisjuncts concl
              results <- mapM (matchInjDisjunct iP ptag) disjs
              case [(k, r) | (k, Just r) <- zip [0 :: Int ..] results] of
                [(k, (d', dup, nVars, i2))] -> do
                  let concl' = rebuildOr [if idx == k then d' else d | (idx, d) <- zip0 disjs]
                      lemA = foldr (hinted forAll) (Conn Imp (Ato prem) concl') allVars
                      -- The escape disjuncts (all disjuncts except the
                      -- witness) also excuse duplicated P-instances.
                      escapes = [d | (idx, d) <- zip0 disjs, idx /= k]
                      uniq =
                        Conn Imp
                          (Conn And (Ato prem) (Ato dup))
                          (rebuildOr (Ato (EqE (varTerm (Free iP)) (varTerm (Free i2))) : escapes))
                      lemB = foldr (hinted forAll) uniq (allVars ++ nVars)
                  pure (Just (Conn And lemA lemB))
                _ -> pure Nothing
        _ -> pure Nothing

    -- Match one conclusion disjunct: an existential witness conjunction with
    -- exactly one uniqueness conjunct over the premise's fact symbol.
    -- Returns the disjunct without that conjunct, the generalised second
    -- premise atom, and its quantified variables.
    matchInjDisjunct iP ptag d@(Qua Ex _ _) = do
      (dVars, _, dBody) <- openFormulaPrefix d
      let conjs = flattenConjuncts dBody
      results <- mapM (matchUniqConjunct iP ptag) conjs
      case [(k, r) | (k, Just r) <- zip [0 :: Int ..] results] of
        [(k, (dup, nVars, i2))]
          | rest@(_ : _) <- [c | (idx, c) <- zip0 conjs, idx /= k],
            -- the second premise atom must not mention the witness variables
            all (`notElem` dVars) (frees (Ato dup :: LNFormula)) ->
              pure (Just (foldr (hinted exists) (rebuildAnd rest) dVars, dup, nVars, i2))
        _ -> pure Nothing
    matchInjDisjunct _ _ _ = pure Nothing

    -- The uniqueness conjunct: not(Ex ys #i2. P(cs)@i2 & not(#i2 = #i)),
    -- or the universal variant All ys #i2. P(cs)@i2 ==> #i2 = #i.
    matchUniqConjunct iP ptag (Not nEx@(Qua Ex _ _)) = do
      (nVars, _, nBody) <- openFormulaPrefix nEx
      pure $ case List.partition isNegEq (flattenConjuncts nBody) of
        ([Not (Ato (EqE e1 e2))], [Ato dup@(Action dTime (Fact dtag _ _))])
          | dtag == ptag,
            Just i2 <- timeVarOf nVars dTime,
            sameTimepoints iP i2 e1 e2 ->
              Just (dup, nVars, i2)
        _ -> Nothing
      where
        isNegEq (Not (Ato (EqE _ _))) = True
        isNegEq _ = False
    matchUniqConjunct iP ptag nAll@(Qua All _ _) = do
      (nVars, _, nBody) <- openFormulaPrefix nAll
      pure $ case nBody of
        Conn Imp (Ato dup@(Action dTime (Fact dtag _ _))) (Ato (EqE e1 e2))
          | dtag == ptag,
            Just i2 <- timeVarOf nVars dTime,
            sameTimepoints iP i2 e1 e2 ->
              Just (dup, nVars, i2)
        _ -> Nothing
    matchUniqConjunct _ _ _ = pure Nothing

    timeVarOf nVars t =
      case [v | v <- nVars, lvarSort v == LSortNode, t == varTerm (Free v)] of
        [v] -> Just v
        _ -> Nothing
    sameTimepoints iP i2 e1 e2 =
      S.fromList [e1, e2] == S.fromList [varTerm (Free iP), varTerm (Free i2)]

    rebuildOr = foldr1 (Conn Or)
    rebuildAnd = foldr1 (Conn And)
    zip0 = zip [0 :: Int ..]
rewriteInjectiveAgreement fm0 = fm0

-- | Eliminate temporal equality constraints by unifying the equated timepoint
-- variables (one-point rule). In Tamarin, @Ex #j. B()\@j & #i = #j@ is
-- equivalent to @B()\@i@; rewriting the explicit-equality form into the
-- shared-variable form lets the shared-timepoint splitting (rule-id
-- instrumentation) apply, instead of leaving behind an equality between two
-- distinct ProVerif timepoints, which is never satisfiable there (every
-- ProVerif event has a unique timepoint).
-- Dually for universals: @All #j. (A()\@j & #i = #j) ==> C@ becomes
-- @A()\@i ==> C@. Both rewrites are equivalences, so they are sound at any
-- polarity.
eliminateTemporalEqualities :: LNFormula -> LNFormula
eliminateTemporalEqualities fm0 =
  let fm' = go fm0
   in if fm' == fm0 then fm0 else simplifyFormula fm'
  where
    go (Qua q v@(_, LSortNode) body) =
      let body' = go body
       in case pinningEq q body' of
            Just repl -> substituteBinder repl body'
            Nothing -> Qua q v body'
    go (Qua q v body) = Qua q v (go body)
    go (Conn c p q) = Conn c (go p) (go q)
    go (Not p) = Not (go p)
    go fm = fm

    -- Find an equality that pins the binder being eliminated (Bound 0 at the
    -- binder level) to a variable bound outside of it, in a position where the
    -- equality is definite: a positive conjunct under an existential,
    -- respectively a positive premise conjunct of the implication under a
    -- universal. Returns the replacement variable, indexed relative to the
    -- position of the binder with the binder itself removed.
    pinningEq :: Quantifier -> LNFormula -> Maybe (BVar LVar)
    pinningEq Ex body = findPin 0 body
    pinningEq All body = descendAll 0 body
      where
        descendAll d (Qua All _ b) = descendAll (d + 1) b
        descendAll d (Conn Imp prem _) = findPin d prem
        descendAll _ _ = Nothing

    -- Search positive conjunct positions (through conjunctions and nested
    -- existentials) at depth d below the binder being eliminated.
    findPin :: Integer -> LNFormula -> Maybe (BVar LVar)
    findPin d (Conn And p q) = findPin d p `orElse` findPin d q
    findPin d (Qua Ex _ p) = findPin (d + 1) p
    findPin d (Ato (EqE s t)) = pin d s t `orElse` pin d t s
    findPin _ _ = Nothing

    pin d s t = case (viewTerm s, viewTerm t) of
      (Lit (Var (Bound i)), Lit (Var other))
        | i == d -> case other of
            Bound k | k > d -> Just (Bound (k - d - 1))
            Free v | lvarSort v == LSortNode -> Just (Free v)
            _ -> Nothing
      _ -> Nothing

    orElse m@(Just _) _ = m
    orElse Nothing n = n

    -- Substitute the eliminated binder by repl (indexed relative to the
    -- binder's position, with the binder itself already removed) and shift the
    -- indices of all enclosing binders down accordingly. The pinning equality
    -- itself becomes trivial (t = t) and is removed by the final
    -- simplifyFormula.
    substituteBinder :: BVar LVar -> LNFormula -> LNFormula
    substituteBinder repl = mapAtoms (fmap . mapLits . fmap . adjust)
      where
        adjust d (Bound i)
          | i == d = case repl of
              Bound r -> Bound (r + d)
              Free v -> Free v
          | i > d = Bound (i - 1)
        adjust _ v = v


moveConstraintsToConclusion :: LNFormula -> LNFormula
moveConstraintsToConclusion fm = case fm of
  -- Handle quantifiers recursively
  Qua q x p -> Qua q x (moveConstraintsToConclusion p)

  -- Main transformation: (A && constraint) ==> B becomes A ==> (¬constraint || B)
  Conn Imp premise conclusion ->
    let (constraints, premise') = extractConstraints premise
    in if null constraints
       then Conn Imp (moveConstraintsToConclusion premise') (moveConstraintsToConclusion conclusion)
       else Conn Imp (moveConstraintsToConclusion premise') (addConstraintsToConclusion constraints (moveConstraintsToConclusion conclusion))

  -- Recursively process other connectives
  Conn c p q -> Conn c (moveConstraintsToConclusion p) (moveConstraintsToConclusion q)
  Not p -> Not (moveConstraintsToConclusion p)

  -- Base cases
  _ -> fm
  where
    -- Check if an atom is a constraint (Less or EqE on time variables)
    isConstraint :: LNFormula -> Bool
    isConstraint (Ato (Less _ _)) = True
    isConstraint (Ato (EqE _ _)) = True
    isConstraint (Not (Ato (EqE _ _))) = True
    isConstraint _ = False

    -- Extract constraints from the current premise scope. Do not descend
    -- through quantifiers: moving a constraint that mentions a bound variable
    -- into the conclusion would either capture a different binder or leave an
    -- out-of-scope de Bruijn index.
    -- Returns: (list of constraints, formula without constraints)
    extractConstraints :: LNFormula -> ([LNFormula], LNFormula)
    extractConstraints (Conn And p q)
      | isConstraint q =
          let (cs, p') = extractConstraints p
          in (q : cs, p')
      | isConstraint p =
          let (cs, q') = extractConstraints q
          in (p : cs, q')
      | otherwise =
          let (cs1, p') = extractConstraints p
              (cs2, q') = extractConstraints q
          in (cs1 ++ cs2, if null cs1 && null cs2 then Conn And p q else if null cs1 then Conn And p q' else if null cs2 then Conn And p' q else Conn And p' q')
    extractConstraints f
      | isConstraint f = ([f], TF True)
      | otherwise = ([], f)

    -- Add negated constraints to conclusion with OR
    -- For (i < j): negate to (i >= j) which is (i > j) || (i = j)
    -- For ¬(i = j): negate to (i = j)
    addConstraintsToConclusion :: [LNFormula] -> LNFormula -> LNFormula
    addConstraintsToConclusion [] conclusion = conclusion
    addConstraintsToConclusion (c:cs) conclusion =
      let negatedC = negateConstraint c
          conclusion' = Conn Or negatedC conclusion
      in addConstraintsToConclusion cs conclusion'

    -- Negate a constraint for moving to conclusion
    negateConstraint :: LNFormula -> LNFormula
    negateConstraint (Ato (Less i j)) =
      -- ¬(i < j) is (i >= j) which is (i > j) || (i = j)
      -- In ProVerif this becomes: (i > j) || (i = j)
      -- We use Not Less to represent >=
      Conn Or (Ato (Less j i)) (Ato (EqE i j))
    negateConstraint (Not (Ato (EqE i j))) =
      -- ¬¬(i = j) is (i = j)
      Ato (EqE i j)
    negateConstraint (Ato (EqE i j)) =
      -- ¬(i = j) is (i ≠ j)
      Not (Ato (EqE i j))
    negateConstraint c = Not c

-- | Convert negated existentials with trailing time constraints to implications.
-- This transforms patterns like:
--   not(Ex #i #j vars. A@i & B@j & not(#i=#j))
-- into:
--   All #i #j vars. (A@i & B@j) ==> #i=#j
--
-- Similarly for Less constraints:
--   not(Ex #i #j #k vars. A & #i < #j & #j < #k)
-- into:
--   All #i #j #k vars. A ==> not(#i < #j) | not(#j < #k)
--   which simplifies to: All #i #j #k vars. A ==> (#j <= #i) | (#k <= #j)
--
-- This avoids the "leading negation" pattern and puts time constraints in the
-- conclusion where ProVerif can handle them properly.
convertNegExWithTimeConstraint :: LNFormula -> LNFormula
convertNegExWithTimeConstraint fm = case fm of
  -- Main pattern: not(Ex vars. body) where body has trailing time constraints
  Not fm'@(Qua Ex _ _) ->
    -- First, collect all the nested existential quantifiers and get the inner body
    let (vars, innerBody) = collectExistentialVars fm'
        -- Build a context from the collected vars (innermost first after reversing)
        -- vars are collected outermost first, so reverse for de Bruijn lookup
        ctx = reverse vars
     in case extractTrailingTimeConstraints ctx innerBody of
      Just (conjuncts, constraints) | not (null constraints) ->
        -- Build: All vars. conjuncts ==> disjunctionOfConstraints
        let premise = buildConjunction conjuncts
            -- For not(#i=#j), conclusion is #i=#j (remove negation)
            -- For #i < #j, conclusion is not(#i < #j) which we'll expand later
            conclusion = buildConclusionFromConstraints constraints
            -- Wrap with all the universal quantifiers (converted from existential)
         in rewrapBoundPrefix All vars (Conn Imp premise conclusion)
      _ -> Not (convertNegExWithTimeConstraint fm')

  -- Recurse through other structures
  Qua q x p -> Qua q x (convertNegExWithTimeConstraint p)
  Conn c p q -> Conn c (convertNegExWithTimeConstraint p) (convertNegExWithTimeConstraint q)
  Not p -> Not (convertNegExWithTimeConstraint p)
  _ -> fm
  where
    -- Collect all existential quantifier variables from nested Ex structure
    collectExistentialVars (Qua Ex x body) =
      let (vars, innerBody) = collectExistentialVars body
       in (x : vars, innerBody)
    collectExistentialVars body = ([], body)

    -- Extract trailing time constraints from a conjunction
    -- Returns (other conjuncts, time constraints) if time constraints are found
    -- ctx is the binder context (innermost first) for looking up bound variable sorts
    extractTrailingTimeConstraints :: [(String, LSort)] -> LNFormula -> Maybe ([LNFormula], [LNFormula])
    extractTrailingTimeConstraints ctx f =
      let conjuncts = flattenConjunctsKeepEx f
          (timeCs, others) = partition (isNegatedTimeConstraintOrLess ctx) conjuncts
       in if null timeCs then Nothing else Just (others, timeCs)

    -- Check if formula is a negated equality on time variables: not(#i = #j)
    -- Or a Less constraint: #i < #j
    -- IMPORTANT: Only match actual time variable comparisons, not term disequalities like not(b=ba)
    isNegatedTimeConstraintOrLess :: [(String, LSort)] -> LNFormula -> Bool
    isNegatedTimeConstraintOrLess ctx (Not (Ato (EqE t1 t2))) =
      -- Only match if both terms are time variables (LSortNode)
      isTimeVar ctx t1 && isTimeVar ctx t2
    isNegatedTimeConstraintOrLess _ (Ato (Less _ _)) = True  -- Less is always on time vars
    isNegatedTimeConstraintOrLess _ _ = False

    -- Check if a term is a time variable
    -- Free variables: check the sort is LSortNode
    -- Bound variables: look up the binder context to check the sort
    isTimeVar ctx t = case viewTerm t of
      Lit (Var (Free v)) -> lvarSort v == LSortNode
      Lit (Var (Bound idx)) ->
        -- Look up the sort in the context
        let i = fromIntegral idx
         in i < length ctx && snd (ctx !! i) == LSortNode
      _ -> False  -- Compound terms are not time variables

    -- Flatten a conjunction into a list, without recursing into existentials
    flattenConjunctsKeepEx :: LNFormula -> [LNFormula]
    flattenConjunctsKeepEx (Conn And p q) = flattenConjunctsKeepEx p ++ flattenConjunctsKeepEx q
    flattenConjunctsKeepEx (Qua Ex x body) = [Qua Ex x body]
    flattenConjunctsKeepEx f = [f]

    -- Build conclusion from extracted constraints
    -- For not(#i=#j), the conclusion is #i=#j (negation removed)
    -- For #i < #j, the conclusion is (#j < #i) | (#i = #j) (i.e., #i >= #j)
    buildConclusionFromConstraints :: [LNFormula] -> LNFormula
    buildConclusionFromConstraints [] = TF True
    buildConclusionFromConstraints [c] = negateTimeConstraint c
    buildConclusionFromConstraints (c:cs) =
      Conn Or (negateTimeConstraint c) (buildConclusionFromConstraints cs)

    -- Negate a time constraint for moving to conclusion
    negateTimeConstraint :: LNFormula -> LNFormula
    negateTimeConstraint (Not (Ato (EqE i j))) = Ato (EqE i j)  -- not(not(#i=#j)) = #i=#j
    negateTimeConstraint (Ato (Less i j)) =
      -- not(#i < #j) = #i >= #j = (#j < #i) | (#i = #j)
      Conn Or (Ato (Less j i)) (Ato (EqE i j))
    negateTimeConstraint f = Not f  -- fallback

-- | Move negated actions from premise to conclusion.
-- ProVerif doesn't allow negated events in queries at all.
-- Transforms: (A & not(B@t)) ==> C  into  A ==> (C | B@t)
-- This is valid because: A & not(B) ==> C  ≡  A ==> C | B
moveNegatedActionsToConclusion :: LNFormula -> LNFormula
moveNegatedActionsToConclusion fm = case fm of
  -- Handle quantifiers recursively
  Qua q x p -> Qua q x (moveNegatedActionsToConclusion p)

  -- Main transformation: (A && not(action)) ==> B becomes A ==> (B || action)
  Conn Imp premise conclusion ->
    let (negatedActions, premise') = extractNegatedActions premise
    in if null negatedActions
       then Conn Imp (moveNegatedActionsToConclusion premise') (moveNegatedActionsToConclusion conclusion)
       else Conn Imp (moveNegatedActionsToConclusion premise') (addActionsToConclusion negatedActions (moveNegatedActionsToConclusion conclusion))

  -- Recursively process other connectives
  Conn c p q -> Conn c (moveNegatedActionsToConclusion p) (moveNegatedActionsToConclusion q)
  Not p -> Not (moveNegatedActionsToConclusion p)

  -- Base cases
  _ -> fm
  where
    -- Check if a formula is a negated action, negated existential, or disjunction of negations
    -- Patterns:
    --   Not (Ato (Action ...))           -- negated bare action (usually invalid in Tamarin)
    --   Not (Qua Ex _ body)              -- negated existential, where body contains action
    --   Conn Or (Not a) (Not b)          -- disjunction of negations = not(a & b) by De Morgan
    isNegatedAction :: LNFormula -> Bool
    isNegatedAction (Not (Ato (Action _ _))) = True
    isNegatedAction (Not (Qua Ex _ _)) = True  -- negated existential
    isNegatedAction (Conn Or (Not _) (Not _)) = True  -- disjunction of negations
    isNegatedAction _ = False

    -- Extract the inner formula from a negated action pattern
    -- For Not (Ato action) -> Ato action
    -- For Not (Ex x. body) -> Ex x. body  (preserving the existential)
    -- For Conn Or (Not a) (Not b) -> Conn And a b  (De Morgan)
    extractInnerFormula :: LNFormula -> LNFormula
    extractInnerFormula (Not inner) = inner
    extractInnerFormula (Conn Or (Not a) (Not b)) = Conn And a b  -- De Morgan: not(a) | not(b) = not(a & b)
    extractInnerFormula f = f

    -- Extract negated actions from a formula in the premise
    -- Returns: (list of unnegated formulas to move to conclusion, formula without negated actions)
    extractNegatedActions :: LNFormula -> ([LNFormula], LNFormula)
    extractNegatedActions (Conn And p q) =
      -- Extract from both children
      let (actsP, p') = extractNegatedActions p
          (actsQ, q') = extractNegatedActions q
          allActs = actsP ++ actsQ
      in if null allActs
         then ([], Conn And p q)
         else
           -- At least one negated action found
           -- Build remaining formula from the non-negated parts
           case (isNegatedAction p, isNegatedAction q, actsP, actsQ) of
             -- Both p and q are directly negated actions
             (True, True, _, _) ->
               (allActs, TF True)  -- Nothing left in premise except true
             -- Only p is a direct negated action
             (True, False, _, _) ->
               (allActs, q')
             -- Only q is a direct negated action
             (False, True, _, _) ->
               (allActs, p')
             -- Neither is directly negated, but they may have nested negated actions
             (False, False, _, _) ->
               (allActs, Conn And p' q')
    extractNegatedActions f
      | isNegatedAction f = ([extractInnerFormula f], TF True)
      | otherwise = ([], f)

    -- Add unnegated actions to conclusion as disjuncts
    addActionsToConclusion :: [LNFormula] -> LNFormula -> LNFormula
    addActionsToConclusion [] conclusion = conclusion
    addActionsToConclusion (action:rest) conclusion =
      addActionsToConclusion rest (Conn Or conclusion action)

-- | Transform not(Ex x1...xn. P1 & P2 & ... & (Ex y. Q) & ... & not(Ex z. R) & ...)
-- into: All x1...xn y ... . (P1 & P2 & ... & Q & ...) ==> (Ex z. R | ...)
--
-- This transformation uses the standard approach: apply nnf to push negation inside,
-- then use pnf to pull all quantifiers to the front (with proper De Bruijn shifting).
--
-- Input: not(Ex x. P(x) & (Ex y. Q(y)) & not(Ex z. R(z)))
-- After nnf: All x. not(P(x)) | (All y. not(Q(y))) | (Ex z. R(z))
--          = All x. not(P(x) & (Ex y. Q(y))) | (Ex z. R(z))
-- After pnf: All x y. (not(P(x)) | not(Q(y))) | (Ex z. R(z))
--          = All x y. not(P(x) & Q(y)) | (Ex z. R(z))
--          = All x y. (P(x) & Q(y)) => (Ex z. R(z))
--
-- Pull only universal quantifiers here. Existential conclusion branches stay
-- branch-local so the later partitioning and renderer preserve their original
-- scopes. Over a nonempty term domain, (Ex r. A) | (Ex s. B) is equivalent to
-- Ex r s. (A | B); keeping the scopes separate is a representation choice,
-- not a claim that those formulas have different truth conditions.
transformNotExistsConjToImplication :: LNFormula -> LNFormula
transformNotExistsConjToImplication fm =
    -- Apply NNF (negation normal form) to push negation inside
    -- This converts not(Ex...) to All... and flips inner negations correctly
    let nnfFormula = nnf fm
        -- Apply custom prenex that only pulls UNIVERSAL quantifiers, not existentials
        -- This keeps existentials as separate disjuncts in the conclusion
        prenexFormula = prenexUniversalsOnly nnfFormula
        -- Convert the resulting disjunction to implication form
        -- All x y. (not(P) | not(Q) | R) becomes All x y. (P & Q) => R
    in convertDisjunctionToImplication prenexFormula
  where
    -- Custom prenex that only pulls universal quantifiers, leaving existentials in place
    prenexUniversalsOnly :: LNFormula -> LNFormula
    prenexUniversalsOnly (Qua All x body) = Qua All x (prenexUniversalsOnly body)
    prenexUniversalsOnly (Qua Ex x body) = Qua Ex x (prenexUniversalsOnly body)
    prenexUniversalsOnly (Conn And p q) = pullUniversalsOnly $ prenexUniversalsOnly p .&&. prenexUniversalsOnly q
    prenexUniversalsOnly (Conn Or p q) = pullUniversalsOnly $ prenexUniversalsOnly p .||. prenexUniversalsOnly q
    prenexUniversalsOnly f = f

    -- Pull only universal quantifiers from connectives, not existentials
    pullUniversalsOnly :: LNFormula -> LNFormula
    pullUniversalsOnly (Conn And (Qua All x p) (Qua All x' q)) | x == x' = Qua All x (pullUniversalsOnly (p .&&. q))
    pullUniversalsOnly (Conn And (Qua All x p) q) = Qua All x (pullUniversalsOnly (p .&&. shiftFreeIndices 1 q))
    pullUniversalsOnly (Conn And p (Qua All x q)) = Qua All x (pullUniversalsOnly (shiftFreeIndices 1 p .&&. q))
    pullUniversalsOnly (Conn Or (Qua All x p) q) = Qua All x (pullUniversalsOnly (p .||. shiftFreeIndices 1 q))
    pullUniversalsOnly (Conn Or p (Qua All x q)) = Qua All x (pullUniversalsOnly (shiftFreeIndices 1 p .||. q))
    -- Don't pull existentials - leave them in place!
    pullUniversalsOnly f = f

    -- Convert All x. (not(P) | Q) to All x. (P => Q)
    -- More generally: All x. (not(P1) | not(P2) | ... | Q1 | Q2 | ...)
    --              => All x. (P1 & P2 & ...) => (Q1 | Q2 | ...)
    convertDisjunctionToImplication :: LNFormula -> LNFormula
    convertDisjunctionToImplication (Qua All x body) =
        Qua All x (convertDisjunctionToImplication body)
    convertDisjunctionToImplication (Qua Ex x body) =
        -- Existential in conclusion - keep it
        Qua Ex x (convertDisjunctionToImplication body)
    convertDisjunctionToImplication disjunction =
        let (negated, positive) = partitionDisjuncts disjunction
            -- negated contains formulas that were Not(...), we take the inner part for premise
            premise = buildConjunction negated
            -- positive contains existentials and atoms for conclusion
            conclusion = buildDisjunction positive
        in if null negated
           then conclusion
           else Conn Imp premise conclusion

    -- Partition disjuncts into negated (premise) and positive (conclusion)
    partitionDisjuncts :: LNFormula -> ([LNFormula], [LNFormula])
    partitionDisjuncts (Conn Or p q) =
        let (neg1, pos1) = partitionDisjuncts p
            (neg2, pos2) = partitionDisjuncts q
        in (neg1 ++ neg2, pos1 ++ pos2)
    partitionDisjuncts (Not p) = ([p], [])  -- Negated term goes to premise
    partitionDisjuncts p = ([], [p])        -- Positive term goes to conclusion

-- | Transform Ex x. (P & not(Ex y. Q) & not(Ex z. R)) to Not(All x. P => (Ex y. Q | Ex z. R))
-- This is the dual of transformNotExistsConjToImplication.
-- The pattern Ex x. (A & not(B)) is equivalent to not(All x. A => B).
-- We reuse the not(Ex...) transformation by wrapping with Not and then transforming.
transformExistsConjToNegatedImplication :: LNFormula -> LNFormula
transformExistsConjToNegatedImplication fm =
    -- Wrap the existential formula with Not to get not(Ex x. P & not(Q))
    -- Then apply the not(Ex...) transformation which gives All x. not(P) | Q
    -- Finally the outer Not gives us not(All x. P => Q)
    let notFm = Not fm
        transformed = transformNotExistsConjToImplication notFm
    in Not transformed

-- | Flatten nested implications for axiom translation.
-- In ProVerif, axioms and restrictions don't support nested correspondences like A => (B => C).
-- This function flattens them: A => (B => C) becomes (A & B) => C
-- This is logically equivalent: A => (B => C) = ¬A ∨ (¬B ∨ C) = ¬(A ∧ B) ∨ C = (A ∧ B) => C
--
-- IMPORTANT: This transformation is ONLY valid for direct nested implications.
-- The pattern A => ((D => E) & F) CANNOT be transformed to (A & D) => (E & F)
-- because this is NOT logically equivalent. Use hasNestedImplicationInConjunction
-- to detect such unsupported patterns before calling this function.
--
-- Also, A => (All x. B => C) can only be flattened to All x. (A & B) => C if x is NOT
-- free in A. Use hasVariableCaptureInNestedImplication to detect this case.
flattenNestedImplications :: LNFormula -> LNFormula
flattenNestedImplications = go
  where
    go (Qua q x p) = Qua q x (go p)
    go (Conn Imp p (Conn Imp q r)) =
      -- A => (B => C) becomes (A & B) => C, then recurse on C
      go (Conn Imp (Conn And p q) r)
    go (Conn Imp p (Qua All x q)) =
      -- A => (All x. Q) - need to look inside the All
      -- If Q is an implication, we can potentially flatten it
      -- SOUNDNESS CHECK: x must not be free in p, otherwise variable capture occurs
      -- x is (String, LSort), frees returns [LVar], so check by name and sort
      let freeInP = frees p
          (xName, xSort) = x
          xFreeInP = any (\v -> lvarName v == xName && lvarSort v == xSort) freeInP
      in if xFreeInP
         then Conn Imp (go p) (Qua All x (go q))  -- Cannot flatten safely, just recurse
         else case go (Qua All x q) of
           Qua All x' (Conn Imp q' r') ->
             -- A => (All x. B => C) becomes All x. (A & B) => C
             -- Safe because x is not free in A
             Qua All x' (Conn Imp (Conn And (shiftFreeIndices 1 p) q') r')
           other -> Conn Imp (go p) other
    go (Conn Imp p (Conn And q r)) =
      -- A => (B & C) - we can only recurse, NOT flatten implications inside B or C
      -- The transformation A => ((D => E) & F) -> (A & D) => (E & F) is UNSOUND
      -- Just recurse on each part
      Conn Imp (go p) (Conn And (go q) (go r))
    go (Conn c p q) = Conn c (go p) (go q)
    go (Not p) = Not (go p)
    go f = f

-- | Check if a formula has nested implications inside conjunctions in the conclusion.
-- Such formulas cannot be soundly flattened and are outside ProVerif's supported fragment.
-- Pattern: A => ((B => C) & D) or A => (D & (B => C))
hasNestedImplicationInConjunction :: LNFormula -> Bool
hasNestedImplicationInConjunction = go
  where
    go (Qua _ _ p) = go p
    go (Conn Imp _ conclusion) = hasImpInConj conclusion
    go (Conn _ p q) = go p || go q
    go (Not p) = go p
    go _ = False

    -- Check if there's an implication inside a conjunction
    hasImpInConj (Conn And p q) = hasImp p || hasImp q || hasImpInConj p || hasImpInConj q
    hasImpInConj (Qua _ _ body) = hasImpInConj body
    hasImpInConj _ = False

    -- Check if the formula is or contains an implication at the top level
    hasImp (Conn Imp _ _) = True
    hasImp (Qua _ _ body) = hasImp body
    hasImp _ = False

-- | Check if a formula has variable capture issues in nested quantified implications.
-- Pattern: A => (All x. B => C) where x is free in A cannot be flattened safely.
hasVariableCaptureInNestedImplication :: LNFormula -> Bool
hasVariableCaptureInNestedImplication = go
  where
    go (Qua _ _ p) = go p
    go (Conn Imp p (Qua All x q)) =
      let freeInP = frees p
          (xName, xSort) = x
          xFreeInP = any (\v -> lvarName v == xName && lvarSort v == xSort) freeInP
      in (xFreeInP && hasNestedImp q) || go p || go q
    go (Conn _ p q) = go p || go q
    go (Not p) = go p
    go _ = False

    hasNestedImp (Conn Imp _ _) = True
    hasNestedImp (Qua _ _ body) = hasNestedImp body
    hasNestedImp _ = False

-- | Check if a formula contains not(...event...) anywhere.
-- This pattern is not supported in ProVerif axioms/restrictions.
hasNegatedEventInFormula :: LNFormula -> Bool
hasNegatedEventInFormula = go
  where
    go (Qua _ _ p) = go p
    go (Not p) = formulaContainsAction p || go p
    go (Conn _ p q) = go p || go q
    go _ = False


-- | Check if a formula has a simple negated action pattern that cannot be translated.
-- Pattern: not(Ex x. Action(x)@i) - this cannot be rewritten to a positive form
isSimpleNegatedAction :: LNFormula -> Bool
isSimpleNegatedAction (Not fm@(Qua Ex _ _)) =
  let body = getExistentialBody fm
  in isJustAction body
  where
    getExistentialBody (Qua Ex _ b) = getExistentialBody b
    getExistentialBody b = b

    isJustAction (Ato (Action _ _)) = True
    isJustAction _ = False
isSimpleNegatedAction _ = False

data TimeVarKey
  = FreeTimeVar LVar
  | BoundTimeVar Int
  deriving (Show, Eq, Ord)

data BinderInfo = BinderInfo Int LSort

pullNegationsToTop :: LNFormula -> Either LNFormula LNFormula
pullNegationsToTop fm =
  let fm_partially_rewritten = fixpoint applyPullNegationStep fm -- nots pulled out by applyPullNegationStep can enable new pull-out steps, so need to compute fixed point
   in if onlyTopLevelNot fm_partially_rewritten
        then Right fm_partially_rewritten -- in this case, formula is fully rewritten, i.e. has only 1 top-level not or no nots at all
        else Left fm_partially_rewritten -- Error with partially rewritten formula
  where

    applyPullNegationStep fm' = case fm' of
      Conn And (Not p) (Not q) -> Not $ p .||. q
      Conn Or (Not p) (Not q) -> Not $ p .&&. q
      Conn Imp p (Not q) ->
        case q of
          Not q' -> Conn Imp (applyPullNegationStep p) (applyPullNegationStep q')  -- q is ¬¬..., simplify to q' by removing double negation
          _ -> if isLessOrEqe q then Conn Imp (applyPullNegationStep p) (Not (applyPullNegationStep q)) else Not $ applyPullNegationStep p .&&. applyPullNegationStep q
      Conn Iff (Not p) q -> Not $ p .<=>. q
      Conn Iff p (Not q) -> Not $ p .<=>. q
      Conn c p q -> Conn c (applyPullNegationStep p) (applyPullNegationStep q)
      Qua All x (Not p) -> Not $ Qua Ex x p
      Qua Ex x (Not p) -> Not $ Qua All x p
      Qua qua x p -> Qua qua x $ applyPullNegationStep p
      Not (Not p) -> p
      Not (Ato (EqE t1 t2)) -> Not (Ato (EqE t1 t2))
      Not p -> Not $ applyPullNegationStep p
      _ -> fm'

    -- Don't pull nots infront of equality tests/comparisons.
    isLessOrEqe (Ato (EqE _ _)) = True
    isLessOrEqe (Ato (Less _ _)) = True
    isLessOrEqe _ = False

onlyTopLevelNot :: ProtoFormula syn s c v -> Bool
onlyTopLevelNot (Not p) = hasNoNegations p -- top-level not expected if rewriting was successful
onlyTopLevelNot p = hasNoNegations p -- no top-level not may mean the rewriting has been successful and the formula has no nots at all

hasNoNegations :: ProtoFormula syn s c v -> Bool
hasNoNegations (Not (Ato (EqE _ _))) = True -- check that there are no nots below top level (except before equality tests/comparisons)
hasNoNegations (Not (Ato (Less _ _))) = True
hasNoNegations (Not _) = False
hasNoNegations (Conn _ p q) = hasNoNegations p && hasNoNegations q
hasNoNegations (Qua _ _ p) = hasNoNegations p
hasNoNegations _ = True

-- | Check if a formula is of the form All x1 ... xn. (F => (Ex y1 ... yn. F') or All x1 ... xn. (F => (Ex y1 ... yn. F') \/ (Ex y1' ... yn'. F'').
isAllImpliesExists :: LNFormula -> Bool
isAllImpliesExists (Qua All _ body) = isAllImpliesExists body
isAllImpliesExists f@(Conn Imp p q) = isQuantifierFree f || (isQuantifierFree p && hasOnlyExistentials q)
  where
    hasOnlyExistentials (Qua Ex _ body') = isQuantifierFree body' || hasOnlyExistentials body'
    hasOnlyExistentials (Conn Or f1 f2) =
      hasOnlyExistentials f1 && hasOnlyExistentials f2
    hasOnlyExistentials fm | isConstraintAtom fm = True
    hasOnlyExistentials _ = False
isAllImpliesExists _ = False

-- | All x1..xn. not(F) is equivalent to not(Ex x1..xn. F). Return the inner
-- existential so it can be rendered as a reachability query on F with the
-- leading-negation interpretation; ProVerif has no negation in queries, so
-- rendering 'not(F)' literally would be rejected ("not unexpected in events").
universalNegationAsExists :: LNFormula -> Maybe LNFormula
universalNegationAsExists (Qua All v p) = Qua Ex v <$> go p
  where
    go (Qua All v' p') = Qua Ex v' <$> go p'
    go (Not f) = Just f
    go _ = Nothing
universalNegationAsExists _ = Nothing

-- | Query-only dualization for an event-free exists-trace property:
--
--   exists trace. forall xs. not Event(xs)
--
-- holds exactly when the all-traces correspondence
--
--   attacker(()) ==> exists xs. Event(xs)
--
-- is false. The unit attacker fact is an always-true premise. This recognizer
-- deliberately accepts only a nonempty universal prefix followed by the
-- negation of one ordinary event; attacker facts and every other formula
-- shape remain on the existing rejection path.
rewriteEventFreeExistsTrace :: LNFormula -> Maybe LNFormula
rewriteEventFreeExistsTrace fm =
  case collect fm of
    Just (v : vs, event) ->
      Just $
        rewrapBoundPrefix Ex (v : vs) $
          Conn Imp (TF True) event
    _ -> Nothing
  where
    collect (Qua All v p) = do
      (vs, event) <- collect p
      pure (v : vs, event)
    collect (Not event@(Ato (Action _ f@(Fact tag _ _))))
      | tag /= KUFact && not (isKLogFact f) = Just ([], event)
    collect _ = Nothing

-- | Query-only dualization for a positive-witness exists-trace property:
--
--   exists trace. P and U
--
-- where P is a nonempty positive witness and U is a conjunction of safety
-- conditions. The trace property holds exactly when the single all-traces
-- correspondence
--
--   P ==> violation(U)
--
-- is false. Normalizing the negation of the complete source formula keeps
-- conjunctions within each violation branch intact; in particular, it never
-- turns alternative violations into separate correspondences whose
-- counterexamples could come from different traces.
--
-- The recognizer is deliberately conservative. After NNF/PNF normalization:
--
-- * every negative top-level disjunct must be a supported atom using only
--   universal binders (the binders obtained by negating the existential
--   witness);
-- * every remaining disjunct must be a positive formula over events,
--   attacker facts, equalities, disequalities, and temporal comparisons;
-- * the premise and conclusion must each contain an action atom; and
-- * no quantifier may remain below the normalized prefix.
--
-- Rewrapping the prefix with 'All' matches ProVerif correspondence semantics:
-- variables occurring in the premise are universal, while variables that
-- occur only in the conclusion are existential.
rewritePositiveWitnessExistsTrace :: LNFormula -> Maybe LNFormula
rewritePositiveWitnessExistsTrace fm = do
  let normalized = pnf (Not (makeBinderHintsGloballyUnique fm))
      (prefix, body) = collectPrefix normalized
      disjuncts = flattenDisjuncts body
  (premiseAtoms, violationBranches) <- classifyDisjuncts prefix disjuncts
  let premise = buildConjunction premiseAtoms
      conclusion = buildDisjunction violationBranches
  if null prefix
      || null premiseAtoms
      || null violationBranches
      || not (formulaContainsAction premise)
      || not (formulaContainsAction conclusion)
    then Nothing
    else
      Just $
        rewrapBoundPrefix All (map snd prefix) $
          Conn Imp premise conclusion
  where
    collectPrefix (Qua q v body) =
      let (rest, inner) = collectPrefix body
       in ((q, v) : rest, inner)
    collectPrefix body = ([], body)


    classifyDisjuncts _ [] = Just ([], [])
    classifyDisjuncts prefix (formula : rest) = do
      (premises, violations) <- classifyDisjuncts prefix rest
      case formula of
        Not atom
          | isSupportedPremiseAtom atom,
            usesOnlyUniversalBinders prefix atom ->
              Just (atom : premises, violations)
        _
          | isSupportedViolation formula ->
              Just (premises, formula : violations)
        _ -> Nothing

    isSupportedPremiseAtom (Ato (Action _ _)) = True
    isSupportedPremiseAtom (Ato (EqE _ _)) = True
    isSupportedPremiseAtom (Ato (Less _ _)) = True
    isSupportedPremiseAtom _ = False

    isSupportedViolation (Ato (Action _ _)) = True
    isSupportedViolation (Ato (EqE _ _)) = True
    isSupportedViolation (Ato (Less _ _)) = True
    isSupportedViolation (Not (Ato (EqE _ _))) = True
    isSupportedViolation (Not (Ato (Less _ _))) = True
    isSupportedViolation (Conn And p q) =
      isSupportedViolation p && isSupportedViolation q
    isSupportedViolation (Conn Or p q) =
      isSupportedViolation p && isSupportedViolation q
    isSupportedViolation _ = False


    usesOnlyUniversalBinders prefix formula =
      all isUniversal (S.toList (boundIndices formula))
      where
        bindersByIndex = reverse (map fst prefix)
        isUniversal i =
          case drop (fromIntegral i) bindersByIndex of
            All : _ -> True
            _ -> False

    boundIndices =
      foldFormula
        (foldMap indicesInTerm)
        (const S.empty)
        id
        (const S.union)
        (\_ _ -> id)

    indicesInTerm term =
      case viewTerm term of
        Lit (Var (Bound i)) -> S.singleton i
        Lit _ -> S.empty
        FApp _ terms -> S.unions (map indicesInTerm terms)

-- | Normalize compound all-trace properties into equivalent correspondences
-- in ProVerif's supported fragment. The three recognized families are:
--
-- * @All xs. P ==> (C1 & ... & Cn)@, distributed into a conjunction of
--   independent all-trace correspondences;
-- * a universal safety guard @G@ in front of, or conjoined with the premise
--   of, a correspondence, moved to its conclusion as the positive
--   existential violation @not G@; and
-- * @not (Ex xs. A & (K1 or K2) & U)@, distributed into the conjunction of
--   the two ordinary secrecy properties.
--
-- Every rewrite is an equivalence over traces. Safety movement is accepted
-- only if negating the guard leaves an existential positive formula over
-- supported atoms; in particular, a positive universal or a negated event
-- makes the recognizer fail. This function is shared with source/reuse axiom
-- translation, while query callers additionally gate it on rejection by the
-- established pipeline.
rewriteCompoundAllTraceFormula :: LNFormula -> Maybe LNFormula
rewriteCompoundAllTraceFormula fm =
  makeBinderHintsGloballyUnique
    <$> firstRewrite
      [ distributeCorrespondenceConclusion fm,
        moveOuterSafetyGuard fm,
        moveInnerSafetyGuard fm,
        distributeAttackerDisjunction fm
      ]
  where
    firstRewrite [] = Nothing
    firstRewrite (candidate : rest) =
      case candidate of
        Just rewritten -> Just rewritten
        Nothing -> firstRewrite rest

    -- P ==> (C1 & ... & Cn) is equivalent to
    -- (P ==> C1) & ... & (P ==> Cn).
    distributeCorrespondenceConclusion formula =
      let (prefix, body) = collectQuantifierPrefix All formula
       in case (prefix, body) of
            (_ : _, Conn Imp premise conclusion@(Conn And _ _)) ->
              Just $
                buildConjunction
                  [ rewrapBoundPrefix All prefix (Conn Imp premise conjunct)
                  | conjunct <- flattenConjuncts conclusion
                  ]
            _ -> Nothing

    -- G ==> (All xs. P ==> C) is equivalent to
    -- All xs. P ==> (C or not G).
    moveOuterSafetyGuard (Conn Imp safety correspondence) = do
      violation <- negateSafetyGuard safety
      addViolationToCorrespondence violation correspondence
    moveOuterSafetyGuard _ = Nothing

    -- All xs. (G & P) ==> C is equivalent to
    -- All xs. P ==> (C or not G).
    moveInnerSafetyGuard formula =
      let (prefix, body) = collectQuantifierPrefix All formula
       in case (prefix, body) of
            (_ : _, Conn Imp premise conclusion) -> do
              (safety, remaining) <- extractOneSafetyGuard premise
              violation <- negateSafetyGuard safety
              pure $
                rewrapBoundPrefix All prefix $
                  Conn Imp (buildConjunction remaining) (Conn Or conclusion violation)
            _ -> Nothing

    -- not(Ex xs. A & (K1 or K2) & U) is equivalent to the conjunction
    -- not(Ex xs. A & K1 & U) and not(Ex xs. A & K2 & U).
    distributeAttackerDisjunction (Not existential) = do
      (prefix, body) <- collectNonemptyExPrefix existential
      (leftBody, rightBody) <- splitOneAttackerDisjunction body
      let left = Not (rewrapBoundPrefix Ex prefix leftBody)
          right = Not (rewrapBoundPrefix Ex prefix rightBody)
      if isNegatedExistsWithConjunction left
          && isNegatedExistsWithConjunction right
        then Just (Conn And left right)
        else Nothing
    distributeAttackerDisjunction _ = Nothing


    collectNonemptyExPrefix formula =
      case collectQuantifierPrefix Ex formula of
        ([], _) -> Nothing
        result -> Just result


    addViolationToCorrespondence violation formula =
      let (prefix, body) = collectQuantifierPrefix All formula
       in case (prefix, body) of
            (_ : _, Conn Imp premise conclusion) ->
              Just $
                rewrapBoundPrefix All prefix $
                  Conn Imp premise (Conn Or conclusion violation)
            _ -> Nothing

    extractOneSafetyGuard premise =
      case
        [ (candidate, take i conjuncts ++ drop (i + 1) conjuncts)
        | (i, candidate) <- zip [0 ..] conjuncts,
          isJust (negateSafetyGuard candidate)
        ] of
        [(safety, remaining@(_ : _))] -> Just (safety, remaining)
        _ -> Nothing
      where
        conjuncts = flattenConjuncts premise

    negateSafetyGuard safety
      | isUniversalSafetyGuard safety,
        let violation = simplifyFormula (nnf (Not safety)),
        isSupportedPositiveConclusion violation,
        formulaContainsAction violation =
          Just violation
      | otherwise = Nothing

    isUniversalSafetyGuard (Conn And left right) =
      isUniversalSafetyGuard left && isUniversalSafetyGuard right
    isUniversalSafetyGuard formula =
      case collectQuantifierPrefix All formula of
        (_ : _, Conn Imp premise conclusion) ->
          isQuantifierFree premise && isQuantifierFree conclusion
        _ -> False



    splitOneAttackerDisjunction body =
      case
        [ ( buildConjunction (take i conjuncts ++ [left] ++ drop (i + 1) conjuncts),
            buildConjunction (take i conjuncts ++ [right] ++ drop (i + 1) conjuncts)
          )
        | (i, Conn Or left right) <- zip [0 ..] conjuncts,
          isExistentialKAction left,
          isExistentialKAction right
        ] of
        [splitBodies] -> Just splitBodies
        _ -> Nothing
      where
        conjuncts = flattenConjuncts body


-- | Normalize a tree of guarded all-trace correspondences without reference
-- to protocol or fact names.  The transformation composes three general
-- equivalences:
--
--   * @(not E & P) ==> C@ becomes @P ==> C | E@;
--   * @(G & P) ==> C@ becomes @P ==> C | not G@ when @G@ is a universal
--     safety property whose violation is in the positive fragment; and
--   * @P ==> C1 & C2@ becomes the conjunction of the two obligations.
--
-- A guard outside a conjunction of correspondences is copied into every
-- conclusion.  Negated attacker disjunctions are distributed into separate
-- obligations.  Every moved formula is checked structurally against the
-- supported positive correspondence fragment.
rewriteGuardedAllTraceFormula :: LNFormula -> Maybe LNFormula
rewriteGuardedAllTraceFormula fm = do
  normalized <- normalizeTree [] fm
  let normalized' = makeBinderHintsGloballyUnique normalized
  if normalized' == makeBinderHintsGloballyUnique fm
    then Nothing
    else Just normalized'
  where
    normalizeTree inherited formula
      | Just (outerEscapes, propertyTree) <- extractOuterEscapes formula =
          normalizeTree (inherited ++ outerEscapes) propertyTree
    normalizeTree inherited (Conn And left right) = do
      left' <- normalizeTree inherited left
      right' <- normalizeTree inherited right
      pure (Conn And left' right')
    normalizeTree inherited formula =
      normalizeCorrespondence inherited formula

    extractOuterEscapes (Conn Imp outerGuard propertyTree)
      | looksLikePropertyTree propertyTree,
        let guardParts = flattenConjuncts outerGuard,
        not (null guardParts),
        Just escapes <- traverse positiveNegatedExistential guardParts =
          Just (escapes, propertyTree)
    extractOuterEscapes _ = Nothing

    looksLikePropertyTree (Conn And left right) =
      looksLikePropertyTree left && looksLikePropertyTree right
    looksLikePropertyTree (Qua All _ body) = looksLikePropertyTree body
    looksLikePropertyTree (Conn Imp _ _) = True
    looksLikePropertyTree _ = False

    normalizeCorrespondence outerEscapes formula =
      let (prefix, body) = collectQuantifierPrefix All formula
       in case (prefix, body) of
            (_ : _, Conn Imp premise conclusion) -> do
              let premiseParts = flattenConjuncts premise
                  localEscapes =
                    mapMaybe positiveNegatedExistential premiseParts
                  safetyViolations =
                    mapMaybe negateUniversalSafetyGuard premiseParts
                  movedParts =
                    [ part
                    | part <- premiseParts,
                      isNothing (positiveNegatedExistential part),
                      isNothing (negateUniversalSafetyGuard part)
                    ]
                  obligations = splitConclusion conclusion
                  violations =
                    outerEscapes ++ localEscapes ++ safetyViolations
                  changed =
                    not (null violations)
                      || length obligations > 1
              if not changed
                  || null movedParts
                  || not (all isSupportedPositivePremise movedParts)
                  || not (formulaContainsAction (buildConjunction movedParts))
                  || null obligations
                  || not (all isSupportedObligation obligations)
                then Nothing
                else
                  Just $
                    buildConjunction
                      [ rewrapBoundPrefix All prefix $
                          Conn Imp
                            (buildConjunction movedParts)
                            (buildDisjunction (obligation : violations))
                      | obligation <- obligations
                      ]
            _ -> Nothing

    positiveNegatedExistential (Not positive@(Qua Ex _ _))
      | isSupportedPositiveConclusion positive,
        formulaContainsAction positive =
          Just positive
    positiveNegatedExistential _ = Nothing

    negateUniversalSafetyGuard safety =
      case collectQuantifierPrefix All safety of
        (_ : _, Conn Imp premise _) ->
          let violation = simplifyFormula (nnf (Not safety))
           in if isSupportedPositivePremise premise
                && formulaContainsAction premise
                && isSupportedPositiveConclusion violation
                && formulaContainsAction violation
                then Just violation
                else Nothing
        _ -> Nothing



    splitConclusion (Conn And left right) =
      splitConclusion left ++ splitConclusion right
    splitConclusion (Not (Conn Or left right))
      | isExistentialKAction left,
        isExistentialKAction right =
          [Not left, Not right]
    splitConclusion conclusion = [conclusion]

    isSupportedObligation obligation =
      isSupportedPositiveConclusion obligation
        || isNegatedSupportedExistential obligation

    -- A negative existential whose counterexample is itself in the positive
    -- fragment is handled by the established final rewrite pipeline.  This
    -- includes both secrecy (@not exists K@) and uniqueness
    -- (@not exists Event & timepoint-disequality@) conclusions.
    isNegatedSupportedExistential (Not positive@(Qua Ex _ _)) =
      isSupportedPositiveConclusion positive && formulaContainsAction positive
    isNegatedSupportedExistential _ = False


-- | Shared all-trace normalization entry point.  Existing compound
-- correspondence rewrites retain priority for output stability; the
-- conditional existence split and guarded-correspondence pass are generic
-- fallbacks.
normalizeAllTraceFormula :: LNFormula -> Maybe LNFormula
normalizeAllTraceFormula fm =
  firstJust
    [ rewriteCompoundAllTraceFormula fm,
      rewriteConditionalExistenceCase fm,
      rewriteGuardedAllTraceFormula fm
    ]
  where
    firstJust [] = Nothing
    firstJust (candidate : rest) =
      case candidate of
        Just normalized -> Just normalized
        Nothing -> firstJust rest

-- | Check if a formula is of the form not(Ex x1 ... xn. F) where F is a conjunction
-- that may contain:
--   - Atoms (action facts)
--   - Positive existential quantifiers: Ex y. G  (e.g., Ex #j. K(s)@j)
--   - Negated existential quantifiers: not(Ex y. G)  (e.g., not(Ex #r. RevLtk(A)@r))
--
-- This covers the common secrecy pattern:
--   not(Ex A B s #i. Secret(A,B,s)@i & (Ex #j. K(s)@j) & not(Ex #r. RevLtk(A)@r) & not(Ex #r. RevLtk(B)@r))
--
-- After NNF and implication conversion, this becomes:
--   All A B s #i. Secret(A,B,s)@i & (Ex #j. K(s)@j) ==> Ex #r. RevLtk(A)@r | Ex #r. RevLtk(B)@r
--
-- Which is exactly what ProVerif can handle (K in premise becomes attacker()).
isNegatedExistsWithConjunction :: LNFormula -> Bool
isNegatedExistsWithConjunction (Not (Qua Ex _ body)) =
    isValidConjunctionBody body && hasNegatedExistential body
  where
    -- Check if body is a valid conjunction structure
    -- Valid elements: atoms, Ex quantifiers (positive or negated), and And connectives
    isValidConjunctionBody (Qua Ex _ p) = isValidConjunctionBody p
    isValidConjunctionBody (Conn And p q) = isValidConjunctionBody p && isValidConjunctionBody q
    -- Allow negated existentials: not(Ex y. G)
    isValidConjunctionBody (Not (Qua Ex _ p)) = isValidConjunctionBody p
    -- Universal quantifiers inside existential body are not supported
    isValidConjunctionBody (Qua All _ _) = False
    -- Disallow other connectives at this level (Or, Imp, Iff would break the pattern)
    isValidConjunctionBody (Conn {}) = False
    -- Atoms (including action facts) are fine
    isValidConjunctionBody (Ato _) = True
    -- TF (true/false) is fine
    isValidConjunctionBody (TF _) = True
    -- Simple negated atoms are fine (like not(A@i))
    isValidConjunctionBody (Not (Ato _)) = True
    -- Any other Not should be rejected
    isValidConjunctionBody (Not _) = False

    -- Check if body contains at least one negated existential
    -- This ensures we only apply this transformation when there's something to move to conclusion
    hasNegatedExistential (Qua Ex _ p) = hasNegatedExistential p
    hasNegatedExistential (Conn And p q) = hasNegatedExistential p || hasNegatedExistential q
    hasNegatedExistential (Not (Qua Ex _ _)) = True
    hasNegatedExistential _ = False
isNegatedExistsWithConjunction _ = False

-- | Check if a formula is of the form Ex x1 ... xn. F where F contains only negative existential quantifiers and conjunctions.
-- This pattern requires at least one negated existential to be useful for transformation.
isExistsWithNegatedExistentials :: LNFormula -> Bool
isExistsWithNegatedExistentials (Qua Ex _ body) = isExistsWithNegatedExistentials body
isExistsWithNegatedExistentials (Conn And p0 q0) = hasNegatedEx && checkNotExists p0 && checkNotExists q0
  where
    -- Check that there's at least one negated existential in the formula
    hasNegatedEx = hasNegExIn p0 || hasNegExIn q0
    hasNegExIn (Not (Qua Ex _ _)) = True
    hasNegExIn (Conn And p' q') = hasNegExIn p' || hasNegExIn q'
    hasNegExIn _ = False

    -- Check that all conjuncts are either atoms, negated existentials, or conjunctions thereof
    -- IMPORTANT: bare Qua Ex should NOT match - only negated ones
    checkNotExists (Not (Qua Ex _ p')) = checkExistsInNotExists p'
    checkNotExists (Conn And p' q') = checkNotExists p' && checkNotExists q'
    checkNotExists (Qua Ex _ _) = False  -- Bare existential - doesn't match this pattern
    checkNotExists (Conn {}) = False
    checkNotExists _ = True  -- Atoms are OK

    checkExistsInNotExists (Qua Ex _ p') = checkExistsInNotExists p'
    checkExistsInNotExists (Conn And p' q') = checkNotExists p' && checkNotExists q'
    checkExistsInNotExists (Conn {}) = False
    checkExistsInNotExists _ = True
isExistsWithNegatedExistentials _ = False

-- | Eliminate double negations: not(not(P)) ==> P
-- This should be done before any other transformations
eliminateDoubleNegations :: LNFormula -> LNFormula
eliminateDoubleNegations (Not (Not p)) = eliminateDoubleNegations p
eliminateDoubleNegations (Qua q (name, srt) p) = Qua q (name, srt) (eliminateDoubleNegations p)
eliminateDoubleNegations (Conn c p q) = Conn c (eliminateDoubleNegations p) (eliminateDoubleNegations q)
eliminateDoubleNegations (Not p) = Not (eliminateDoubleNegations p)
eliminateDoubleNegations p = p

-- | Expand negated timepoint comparisons: not(i < j) ==> (j < i) | (i = j)
-- ProVerif doesn't support not(i < j) syntax but does support <, >, <=, >=
-- We expand to the disjunction which is semantically equivalent to i >= j
expandNegatedTimepointComparisons :: LNFormula -> LNFormula
expandNegatedTimepointComparisons (Not (Ato (Less i j))) =
  -- not(i < j) becomes (j < i) || (i = j)
  Conn Or (Ato (Less j i)) (Ato (EqE i j))
expandNegatedTimepointComparisons (Qua q x p) = Qua q x (expandNegatedTimepointComparisons p)
expandNegatedTimepointComparisons (Conn c p q) = Conn c (expandNegatedTimepointComparisons p) (expandNegatedTimepointComparisons q)
expandNegatedTimepointComparisons (Not p) = Not (expandNegatedTimepointComparisons p)
expandNegatedTimepointComparisons p = p

-- | Check if a formula is of the form All x1 ... xn. A ==> (not B1) | (not B2) | ... | C1 | C2 | ...
-- where at least one disjunct is negated
-- Bare negated comparisons remain in the conclusion for later expansion.
-- Quantified negated disjuncts move only when they have an existential-only
-- prefix and a supported quantifier-free body.
isAllImpliesDisjWithNegations :: LNFormula -> Bool
isAllImpliesDisjWithNegations (Qua All _ body) = isAllImpliesDisjWithNegations body
isAllImpliesDisjWithNegations (Conn Imp _ concl) = hasMovableNegatedDisjunct concl
  where
    hasMovableNegatedDisjunct (Conn Or p q) =
      hasMovableNegatedDisjunct p || hasMovableNegatedDisjunct q
    hasMovableNegatedDisjunct (Not f) = isMovableNegatedDisjunctBody f
    hasMovableNegatedDisjunct _ = False
isAllImpliesDisjWithNegations _ = False

-- | A negated disjunct may move to an implication premise when its body is
-- quantifier-free, or has only a leading existential prefix over a supported
-- quantifier-free premise. Universals below an existential would change the
-- witness dependency when the existential is converted to a universal.
isMovableNegatedDisjunctBody :: LNFormula -> Bool
isMovableNegatedDisjunctBody formula@(Qua Ex _ _) =
  maybe False isSupportedPositivePremise (stripExistentialPrefix formula)
  where
    stripExistentialPrefix (Qua Ex _ body) = stripExistentialPrefix body
    stripExistentialPrefix body
      | isQuantifierFree body = Just body
      | otherwise = Nothing
isMovableNegatedDisjunctBody formula =
  isQuantifierFree formula
    && isSupportedPositivePremise formula
    && not (containsComparison formula)
  where
    -- Keep negated comparisons in the conclusion; they are expanded later.
    containsComparison (Ato (EqE _ _)) = True
    containsComparison (Ato (Less _ _)) = True
    containsComparison (Qua _ _ body) = containsComparison body
    containsComparison (Conn _ p q) = containsComparison p || containsComparison q
    containsComparison (Not p) = containsComparison p
    containsComparison _ = False

-- | Detect ∀x. (P ⇒ ¬Q₁ ∧ ¬Q₂ ∧ ...) pattern
-- This pattern needs to be distributed into multiple queries:
-- (∀x. P ⇒ ¬Q₁) ∧ (∀x. P ⇒ ¬Q₂) ∧ ...
-- Because ProVerif doesn't support negated events in conclusions
isAllImpliesConjWithNegations :: LNFormula -> Bool
isAllImpliesConjWithNegations (Qua All _ body) = isAllImpliesConjWithNegations body
isAllImpliesConjWithNegations (Conn Imp _ concl) = isConjOfNegatedExistentials concl
  where
    -- Check if conclusion is a conjunction where at least one conjunct is a negated existential
    isConjOfNegatedExistentials (Conn And p q) =
      (isNegatedExistential p || isConjOfNegatedExistentials p) &&
      (isNegatedExistential q || isConjOfNegatedExistentials q)
    isConjOfNegatedExistentials f = isNegatedExistential f

    isNegatedExistential (Not (Qua Ex _ _)) = True
    isNegatedExistential _ = False
isAllImpliesConjWithNegations _ = False

-- | Transform A ==> (not B1) | (not B2) | ... | C1 | C2 | ... into A & B1 & B2 & ... ==> C1 | C2 | ...
-- This moves negated disjuncts from the conclusion to the premise
-- Also pulls existential quantifiers from premise conjuncts to top level as universal quantifiers
-- When all disjuncts are negated, returns Not(A & B1 & B2 & ...) which will be handled as a leading negation
moveNegatedDisjunctsToPremise :: LNFormula -> LNFormula
moveNegatedDisjunctsToPremise fm = case fm of
  Qua All x p ->
    -- Process the body and then re-wrap with All, but also pull out any new quantifiers
    let p' = moveNegatedDisjunctsToPremise p
     in case p' of
          -- If the result has new All quantifiers at the top, merge them
          Qua All y body -> Qua All x (Qua All y body)
          _ -> Qua All x p'
  Conn Imp premise conclusion ->
    let (negatedTerms, positiveTerms) = partitionDisjuncts conclusion
     in if null negatedTerms
          then fm  -- No negated terms, return unchanged
          else
            -- Build new premise: premise & B1 & B2 & ...
            let newPremise = buildConjunction (premise : negatedTerms)
             in case positiveTerms of
                  -- All disjuncts were negated: pull Ex quantifiers and return Not(premise)
                  -- This will be properly handled as a leading negation by the existing machinery
                  [] ->
                    let prenexForm = prenex newPremise
                     in Not prenexForm
                  -- Some positive terms remain: build implication and pull Ex quantifiers
                  (t:ts) ->
                    let newConclusion = buildDisjunction (t:ts)
                        implication = Conn Imp newPremise newConclusion
                     in pullExFromPremise implication
  _ -> fm
  where
    -- Partition disjuncts into (negated terms with negation removed, positive terms)
    partitionDisjuncts :: LNFormula -> ([LNFormula], [LNFormula])
    partitionDisjuncts (Conn Or p q) =
      let (negsP, posP) = partitionDisjuncts p
          (negsQ, posQ) = partitionDisjuncts q
       in (negsP ++ negsQ, posP ++ posQ)
    partitionDisjuncts negated@(Not p)
      | isMovableNegatedDisjunctBody p = ([p], [])
      | otherwise = ([], [negated])
    partitionDisjuncts p = ([], [p])  -- Add to positive terms

    -- Pull existential quantifiers from premise conjuncts to top level as universal
    -- Transform: (A & Ex x. B) ==> C into All x. (A & B) ==> C
    -- The quantifiers are pulled out of the implication entirely
    pullExFromPremise :: LNFormula -> LNFormula
    pullExFromPremise (Conn Imp premise conclusion) =
      let premise' = convertExToAllInConj premise
          prenexPremise = prenex premise'
       in pullQuantifiersOut (Conn Imp prenexPremise conclusion)
    pullExFromPremise f = f

    -- Pull All quantifiers from the premise of an implication to the outside
    -- When moving a quantifier out, we must shift indices in the conclusion
    -- to account for the new quantifier level
    pullQuantifiersOut :: LNFormula -> LNFormula
    pullQuantifiersOut (Conn Imp (Qua All x premise) conclusion) =
      -- Shift free indices in conclusion by 1 to account for the new quantifier
      let shiftedConclusion = shiftFreeIndices 1 conclusion
       in Qua All x (pullQuantifiersOut (Conn Imp premise shiftedConclusion))
    pullQuantifiersOut f = f

    -- Convert Ex quantifiers to All quantifiers within conjunctions
    convertExToAllInConj :: LNFormula -> LNFormula
    convertExToAllInConj (Conn And p q) =
      convertExToAllInConj p .&&. convertExToAllInConj q
    convertExToAllInConj (Qua Ex x body) =
      Qua All x (convertExToAllInConj body)
    convertExToAllInConj (Qua q x body) =
      Qua q x (convertExToAllInConj body)
    convertExToAllInConj f = f

-- | Distribute implication over a conjunction of negated existentials
-- Transforms: ∀x. (P ⇒ ¬Q₁ ∧ ¬Q₂) into (∀x. P ⇒ ¬Q₁) ∧ (∀x. P ⇒ ¬Q₂)
-- which is equivalent to: not(∃x. P ∧ Q₁) ∧ not(∃x. P ∧ Q₂)
-- This produces a top-level conjunction that will be split by splitTopLvlConns
-- Each resulting formula will be processed independently with leading negation
distributeImplicationOverConjunction :: LNFormula -> LNFormula
distributeImplicationOverConjunction fm = case fm of
  Qua All x body ->
    case distributeImplicationOverConjunction body of
      -- If the body became a conjunction, distribute the All over it
      -- Then recursively process each part to convert Qua All (Not (Qua Ex ...)) to Not (Qua Ex ...)
      Conn And p q ->
        let leftProcessed = distributeImplicationOverConjunction (Qua All x p)
            rightProcessed = distributeImplicationOverConjunction (Qua All x q)
        in Conn And leftProcessed rightProcessed
      -- If the body is Not (Qua Ex ...), pull the Not outside and convert All to Ex
      -- All x. not(Ex y. P) is equivalent to not(Ex x y. P)
      Not (Qua Ex y innerBody) -> Not (Qua Ex x (Qua Ex y innerBody))
      -- If the body is a single Not (Qua Ex ...) without nested Qua Ex
      Not innerBody -> Not (Qua Ex x innerBody)
      body' -> Qua All x body'
  Conn Imp premise (Conn And concl1 concl2) ->
    -- Distribute: (P => Q1 & Q2) becomes (P => Q1) & (P => Q2)
    -- Then recursively process in case there are more conjuncts
    let left = distributeImplicationOverConjunction (Conn Imp premise concl1)
        right = distributeImplicationOverConjunction (Conn Imp premise concl2)
     in Conn And left right
  Conn Imp premise (Not (Qua Ex x body)) ->
    -- For a single negated existential: P => not(Ex x. Q)
    -- Transform to: not(Ex x. P & Q)
    -- This is done by moving P into the existential and negating the whole thing
    let -- Shift premise indices to account for the new quantifier
        shiftedPremise = shiftFreeIndices 1 premise
        -- The body already contains nested existentials, just add the conjunction
        newBody = Conn And shiftedPremise body
     in Not (Qua Ex x newBody)
  _ -> fm

splitTopLevel :: TraceQuantifier -> LNFormula -> [LNFormula]
splitTopLevel AllTraces (Conn And left right) =
  splitTopLevel AllTraces left ++ splitTopLevel AllTraces right
splitTopLevel ExistsTrace (Conn Or left right) =
  splitTopLevel ExistsTrace left ++ splitTopLevel ExistsTrace right
splitTopLevel _ formula = [formula]
timeVarKey ::
  [BinderInfo] ->
  VTerm Name (BVar LVar) ->
  Maybe TimeVarKey
timeVarKey ctx timeVar =
  case viewTerm timeVar of
    Lit (Var (Free v))
      | lvarSort v == LSortNode -> Just (FreeTimeVar v)
    Lit (Var (Bound i)) ->
      case drop (fromIntegral i) ctx of
        BinderInfo bid LSortNode : _ -> Just (BoundTimeVar bid)
        _ -> Nothing
    _ -> Nothing

collectActionsWithTimepoints :: LNFormula -> M.Map TimeVarKey [String]
collectActionsWithTimepoints fm = snd (collectActions [] 0 fm M.empty)
  where
    collectActions ctx nextId (Ato (Action timeVar (Fact tag _ _))) acc =
      let updatedAcc = case timeVarKey ctx timeVar of
            Just key -> M.insertWith (++) key [factTagName tag] acc
            Nothing -> acc
       in (nextId, updatedAcc)
    collectActions _ctx nextId (Ato _) acc = (nextId, acc)
    collectActions _ctx nextId (TF _) acc = (nextId, acc)
    collectActions ctx nextId (Not p) acc = collectActions ctx nextId p acc
    collectActions ctx nextId (Conn _ p q) acc =
      let (nextAfterP, acc') = collectActions ctx nextId p acc
       in collectActions ctx nextAfterP q acc'
    collectActions ctx nextId (Qua _ (_, varSort) body) acc =
      let binder = BinderInfo nextId varSort
       in collectActions (binder : ctx) (nextId + 1) body acc

-- | Resolve the endpoints of temporal equalities by binder identity, not by
-- binder hint. Independently quantified variables are allowed to reuse the
-- same human-readable hint, and must never be treated as one timepoint.
collectTemporalEqKeyPairs :: LNFormula -> [(TimeVarKey, TimeVarKey)]
collectTemporalEqKeyPairs fm = snd (collect [] 0 fm)
  where
    collect ctx nextId (Ato (EqE left right)) =
      (nextId, pairOf ctx left right)
    collect ctx nextId (Not (Ato (Less left right))) =
      (nextId, pairOf ctx left right)
    collect _ nextId (Ato _) = (nextId, [])
    collect _ nextId (TF _) = (nextId, [])
    collect ctx nextId (Not body) = collect ctx nextId body
    collect ctx nextId (Conn _ left right) =
      let (nextAfterLeft, leftPairs) = collect ctx nextId left
          (nextAfterRight, rightPairs) =
            collect ctx nextAfterLeft right
       in (nextAfterRight, leftPairs ++ rightPairs)
    collect ctx nextId (Qua _ (_, varSort) body) =
      let binder = BinderInfo nextId varSort
       in collect (binder : ctx) (nextId + 1) body

    pairOf ctx left right =
      case (timeVarKey ctx left, timeVarKey ctx right) of
        (Just leftKey, Just rightKey)
          | leftKey /= rightKey -> [(leftKey, rightKey)]
        _ -> []

-- | Find events that share timepoints in a formula
eventsSharingTimepoints :: LNFormula -> S.Set String
eventsSharingTimepoints fm =
  let actionMap = collectActionsWithTimepoints fm
      sharedTimepoints = M.filter ((> 1) . length) actionMap
   in S.fromList . concatMap (S.toList . S.fromList) $ M.elems sharedTimepoints

-- | Check if a formula has any shared timepoints
formulaHasSharedTimepoints :: LNFormula -> Bool
formulaHasSharedTimepoints = not . S.null . eventsSharingTimepoints
isAllActionsImpliesNotExists :: LNFormula -> Bool
isAllActionsImpliesNotExists (Qua All _ body) = isAllActionsImpliesNotExists body
isAllActionsImpliesNotExists (Conn Imp p (Not q)) = onlyActionAtoms p && hasOnlyExistentials q
  where
    hasOnlyExistentials (Qua Ex _ body') = hasOnlyExistentials body'
    hasOnlyExistentials (Ato a) = isActionAtom a
    hasOnlyExistentials _ = False
    -- Check if formula contains only action atoms (possibly connected by conjunctions)
    onlyActionAtoms (Ato at) = isActionAtom at
    onlyActionAtoms (Conn And p1 p2) = onlyActionAtoms p1 && onlyActionAtoms p2
    onlyActionAtoms _ = False
isAllActionsImpliesNotExists _ = False

-- Check if a formula is of the form "All x1 .. xn tA. A(x1 ... xn)@tA ==> Ex y1 ... yn tB. B(y1 ... yn)@tB & tB < tA"
-- If so, remove the less (it's implicit as we translate to a basic correspondence).
allImplExLessWoTmps :: LNFormula -> LNFormula
allImplExLessWoTmps (Qua All x p) = Qua All x $ allImplExLessWoTmps p
allImplExLessWoTmps (Conn Imp (Ato (Action tA fA)) q) = Conn Imp (Ato (Action tA fA)) $ case q of
  (Qua Ex x p) -> Qua Ex x $ hasOnlyExistentials p
  f -> f
  where
    hasOnlyExistentials (Qua Ex x p) = Qua Ex x $ hasOnlyExistentials p
    hasOnlyExistentials f@(Conn And (Ato (Action tB fB)) (Ato (Less tB' tA'))) = if tA == tA' && tB == tB' then Ato (Action tB fB) else f
    hasOnlyExistentials f = f
allImplExLessWoTmps f = f
