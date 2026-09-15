-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Sapic processes to ProVerif
module Export.ProVerif
  ( ProVerifOptions (..),
    prettyProVerifTheory,
    loadQueries,
  )
where

import Data.Char (isSpace)
import Data.List as List
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Maybe
import Data.Sequence qualified as Seq
import Data.Set qualified as S
import Export.Name
import Export.Diagnostic
import Export.ProVerif.Formula
import Export.ProVerif.Header
import Export.ProVerif.Instrumentation
import Export.ProVerif.Property
import Export.ProVerif.Render
import Export.ProVerif.Rule
import Export.Sapic
import Export.Types
import Sapic.Typing
import Text.PrettyPrint.Class
import Theory
import Theory.Module
import Theory.Tools.Wellformedness (formulaFacts)

-- | Classification for how a lemma should be translated
data LemmaTranslationMode
  = AsQuery       -- ^ Regular lemma, translate as query
  | AsAxiom       -- ^ Reuse/source lemma, translate as axiom
  | ExcludeLemma  -- ^ Don't translate at all
  deriving (Eq, Ord, Show)

data ProVerifOptions = ProVerifOptions
  { omitReuseLemmas :: Bool,
    omitSourceLemmas :: Bool,
    omitRestrictions :: Bool,
    omitMultisetTranslation :: Bool,
    omitPreciseActions :: Bool,
    selectSpecificLemmas :: Bool
  }
  deriving (Eq, Ord, Show)

-- | The assembled sections of a ProVerif trace-export document.
data ProVerifDocument = ProVerifDocument
  { documentSkipPreciseActions :: Bool,
    documentHeaders :: [Doc],
    documentQueries :: [Doc],
    documentRestrictions :: [Doc],
    documentAxioms :: [Doc],
    documentLemmas :: [Doc],
    documentMacroProcesses :: [Doc],
    documentRuleProcesses :: [Doc],
    documentMainProcess :: Doc,
    documentComments :: [Doc]
  }

proverifTemplate :: ProVerifDocument -> Doc
proverifTemplate document =
  (if document.documentSkipPreciseActions then emptyDoc else text "set preciseActions = true." $$ text "")
    $$ vcat document.documentHeaders
    $$ vcat document.documentQueries
    $$ section "(* Restrictions *)" document.documentRestrictions
    $$ section "(* Axioms from reuse/source lemmas *)" document.documentAxioms
    $$ section "(* Queries *)" document.documentLemmas
    $$ section
      "(* Processes *)"
      (document.documentMacroProcesses ++ document.documentRuleProcesses)
    $$ text ""
    $$ text "process"
    $$ nest 4 document.documentMainProcess
    $--$ vcat (intersperse (text "") document.documentComments)
  where
    section title docs = case filter (not . all isSpace . render) docs of
      [] -> emptyDoc
      nonBlank ->
        text ""
          $$ text title
          $$ text ""
          $$ vcat (intersperse (text "") nonBlank)

prettyProVerifTheory ::
  ModuleType ->
  ProVerifOptions ->
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  (OpenTheory, TypingEnvironment) ->
  IO (Either ExportError ExportResult)
prettyProVerifTheory m options lemSel (thy', typEnv) =
  captureExport diagnostics $ do
    headersTheory <- loadHeaders propertyEventTags tc thy typEnv -- load headers from theory
    let headersTranslation =
          [ baseHeaders, -- base headers for translation
            prochd, -- headers from the process
            macroprochd, -- headers from the macroprocess
            ruleHeaders, -- headers from the rules
            lemmaHeaders, -- headers from the lemmas
            restrictionHeaders -- headers from the restrictions
          ]
    headers <- finalizeHeaders headersTheory headersTranslation
    let hd = attribHeaders tc headers
    pure $
      proverifTemplate
        ProVerifDocument
          { documentSkipPreciseActions = skipPrecise tc,
            documentHeaders = hd,
            documentQueries = queries,
            documentRestrictions = restrictions,
            documentAxioms = axioms,
            documentLemmas = lemmas,
            documentMacroProcesses = macroproc,
            documentRuleProcesses = ruleproc,
            documentMainProcess = proc',
            documentComments = comments
          }
  where
    noReuseLemmas = options.omitReuseLemmas
    noSourceLemmas = options.omitSourceLemmas
    noRestrictions = options.omitRestrictions
    noMultiset = options.omitMultisetTranslation
    noPrecise = options.omitPreciseActions
    hasSpecificLemmas = options.selectSpecificLemmas
    thy = if noMultiset then thy' else multisetTheory thy'

    tc =
      emptyTC
        { predicates = theoryPredicates thy,
          skipReuseLemmas = noReuseLemmas,
          skipSourceLemmas = noSourceLemmas,
          skipRestrictions = noRestrictions,
          skipPrecise = noPrecise
        }
    completionEvent = allocateCompletionEvent typEnv thy
    (proc, prochd, hasBoundState, hasUnboundState) = loadProc renderSapicFormula tc thy
    proc'
      | null (theoryProcesses thy) = ruleComb
      | null (theoryRules thy) = proc
      | otherwise = proc <-> text "|" <-> ruleComb
    baseHeaders = if hasUnboundState then stateHeaders else S.empty
    -- Analyze every included query and helper axiom after the same generic
    -- all-trace normalization used by their renderers.  Instrumentation is
    -- therefore driven solely by the translated properties, including
    -- helper axioms that were not selected on the command line.
    selectedQueryLemmas =
      [ lemma
      | lemma <- theoryLemmas thy,
        classifyLemma hasSpecificLemmas tc lemSel lemma == AsQuery
      ]
    unannotatedQueryPlans =
      [ (lemma._lName, prepareProperty completionEvent typEnv (QueryProperty lemma))
      | lemma <- selectedQueryLemmas
      ]
    emittedQueryPlans =
      [ prepared
      | (_, PropertyEmitted prepared) <- unannotatedQueryPlans
      ]
    selectedAxiomLemmas =
      [ lemma
      | lemma <- theoryLemmas thy,
        classifyLemma hasSpecificLemmas tc lemSel lemma == AsAxiom
      ]
    unannotatedAxiomPlans =
      [ (lemma._lName, prepareProperty completionEvent typEnv (AxiomProperty lemma))
      | lemma <- selectedAxiomLemmas
      ]
    emittedAxiomPlans =
      [ prepared
      | (_, PropertyEmitted prepared) <- unannotatedAxiomPlans
      ]
    unannotatedRestrictionPlans
      | skipRestrictions tc = []
      | otherwise =
          [ (restriction._rstrName, prepareProperty completionEvent typEnv (RestrictionProperty restriction))
          | restriction <- theoryRestrictions thy
          ]
    emittedRestrictionPlans =
      [ prepared
      | (_, PropertyEmitted prepared) <- unannotatedRestrictionPlans
      ]
    lemmaSharedEvents =
      S.unions
        ( [ preparedFormulaRuleIdEvents queryFormula.preparedQueryBody
          | prepared <- emittedQueryPlans,
            queryFormula <- NE.toList prepared.preparedQueryFormulas
          ]
            ++ concatMap
              (map preparedFormulaRuleIdEvents . NE.toList . preparedAxiomFormulas)
              emittedAxiomPlans
        )
    completionTriggerEvents =
      S.unions
        ( map preparedQueryCompletionTriggers emittedQueryPlans
            ++ map preparedAxiomCompletionTriggers emittedAxiomPlans
        )
    restrictionSharedEvents =
      S.unions
        [ preparedFormulaRuleIdEvents restrictionFormula
        | prepared <- emittedRestrictionPlans,
          restrictionFormula <- NE.toList prepared.preparedRestrictionFormulas
        ]
    sharedEventTags = lemmaSharedEvents `S.union` restrictionSharedEvents
    preparedQueryPlans =
      [ (name, mapPropertyOutcome (annotateQueryProperty sharedEventTags) outcome)
      | (name, outcome) <- unannotatedQueryPlans
      ]
    preparedAxiomPlans =
      [ (name, mapPropertyOutcome (annotateAxiomProperty sharedEventTags) outcome)
      | (name, outcome) <- unannotatedAxiomPlans
      ]
    preparedRestrictionPlans =
      [ (name, mapPropertyOutcome (annotateRestrictionProperty sharedEventTags) outcome)
      | (name, outcome) <- unannotatedRestrictionPlans
      ]
    instrumentationPlan =
      InstrumentationPlan
        { instrumentationCompletionEvent = completionEvent,
          instrumentationRuleIdEvents = sharedEventTags,
          instrumentationCompletionTriggers = completionTriggerEvents
        }
    propertyEventTags = instrumentationPropertyEvents instrumentationPlan
    (restrictions, restrictionHeaders) =
      if skipRestrictions tc
        then ([], S.empty)
        else loadRestrictions sharedEventTags typEnv preparedRestrictionPlans thy
    queries = loadQueries thy
    (axioms, lemmas, lemmaHeaders) =
      loadLemmas preparedQueryPlans preparedAxiomPlans propertyEventTags hasSpecificLemmas lemSel tc typEnv thy
    (ruleproc, ruleComb, ruleHeaders) = loadRules instrumentationPlan thy m
    (macroproc, macroprochd) =
      -- if stateM is not empty, we have inlined the process calls, so we don't reoutput them
      if hasBoundState then ([text ""], S.empty) else loadMacroProc renderSapicFormula tc thy
    comments = formalCommentDocs thy
    diagnostics =
      collectProVerifDiagnostics hasSpecificLemmas lemSel tc preparedQueryPlans preparedAxiomPlans preparedRestrictionPlans thy
        <> collectTypingDiagnostics typEnv


collectProVerifDiagnostics ::
  Bool ->
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  TranslationContext ->
  [(String, PropertyOutcome PreparedQueryProperty)] ->
  [(String, PropertyOutcome PreparedAxiomProperty)] ->
  [(String, PropertyOutcome PreparedRestrictionProperty)] ->
  OpenTheory ->
  Seq.Seq ExportDiagnostic
collectProVerifDiagnostics hasSpecificLemmas lemSel tc preparedQueryPlans preparedAxiomPlans preparedRestrictionPlans thy =
  collectBuiltinDiagnostics thy
    <> Seq.fromList (lemmaDiagnostics ++ restrictionDiagnostics)
  where
    classified =
      [ (lemma, classifyLemma hasSpecificLemmas tc lemSel lemma)
      | lemma <- theoryLemmas thy
      ]
    lemmaDiagnostics = concatMap diagnosticForLemma classified
    diagnosticForLemma (lemma, AsQuery) =
      case lookup lemma._lName preparedQueryPlans of
        Just (PropertyOmitted reason) ->
          [ ExportDiagnostic
              "PV-GOAL-OMITTED"
              UntranslatedGoal
              (LemmaSubject lemma._lName)
              ("produced no ProVerif query: " ++ reason)
          ]
        Just (PropertyEmitted prepared) ->
          splitNotice prepared ++ polarityNotice prepared
        _ -> []
      where
        splitNotice prepared = case prepared.preparedQueryRecombination of
          Nothing -> []
          Just _ ->
            [ ExportDiagnostic
                "PV-GOAL-SPLIT"
                Informational
                (LemmaSubject lemma._lName)
                ( "was emitted as "
                    ++ show (length prepared.preparedQueryFormulas)
                    ++ " queries; follow the adjacent reconstruction instruction"
                )
            ]
        polarityNotice prepared
          | any ((== InvertResult) . preparedQueryPolarity) prepared.preparedQueryFormulas =
              [ ExportDiagnostic
                  "PV-GOAL-INVERTED"
                  Informational
                  (LemmaSubject lemma._lName)
                  "contains an inverted query result; follow the adjacent interpretation instruction"
              ]
          | otherwise = []
    diagnosticForLemma (lemma, AsAxiom) =
      case lookup lemma._lName preparedAxiomPlans of
        Just (PropertyOmitted reason) ->
          [ ExportDiagnostic
              "PV-AXIOM-OMITTED"
              ChangedAssumptions
              (AxiomSubject lemma._lName)
              ( "was not emitted; this may affect proof search but does not"
                  ++ " make the trace model incomplete: "
                  ++ reason
              )
          ]
        Just (PropertyEmitted prepared) ->
          case prepared.preparedAxiomApproximation of
            Nothing -> []
            Just reason ->
              [ ExportDiagnostic
                  "PV-AXIOM-APPROXIMATED"
                  ChangedAssumptions
                  (AxiomSubject lemma._lName)
                  reason
              ]
        _ -> []
    diagnosticForLemma (_, ExcludeLemma) = []
    restrictionDiagnostics
      | skipRestrictions tc = []
      | otherwise = mapMaybe diagnosticForRestriction (theoryRestrictions thy)
    diagnosticForRestriction restriction =
      case lookup restriction._rstrName preparedRestrictionPlans of
        Just (PropertyOmitted reason) ->
          Just
            ( ExportDiagnostic
                "PV-RESTRICTION-OMITTED"
                ChangedAssumptions
                (RestrictionSubject restriction._rstrName)
                ( "was not emitted; the translated trace model is incomplete: "
                    ++ reason
                )
            )
        Just (PropertyEmitted prepared) ->
          ExportDiagnostic
            "PV-RESTRICTION-APPROXIMATED"
            ChangedAssumptions
            (RestrictionSubject restriction._rstrName)
            <$> prepared.preparedRestrictionApproximation
        _ -> Nothing


allocateCompletionEvent :: TypingEnvironment -> OpenTheory -> String
allocateCompletionEvent typeEnvironment thy =
  case targetEventText allocatedTarget of
    'e' : factName -> factName
    targetName -> targetName
  where
    (allocatedTarget, _) = allocateEvent "eRuleCompleted" allocator
    allocator =
      reserveNames GlobalNamespace reservedTargetNames emptyNameAllocator
    reservedTargetNames =
      S.fromList
        ( mapMaybe getProVerifHeaderIdentifier declarationHeaders
            ++ map (('e' :) . factTagName) sourceEventTags
        )
    declarationHeaders =
      S.toList
        ( foldMap headerOfFunSym (theoryFunctionTypingInfos thy)
            `S.union` foldMap builtinHeaders (theoryBuiltins thy)
        )
    builtinHeaders name =
      case builtins name of
        AccurateBuiltin headers -> S.fromList headers
        BestEffortBuiltin headers -> S.fromList headers
        NotSupportedBuiltin _ -> S.empty
    sourceEventTags =
      M.keys typeEnvironment.events
        ++ [ factTag fact
           | OpenProtoRule rule _ <- theoryRules thy,
             fact <- rule._rActs
           ]
        ++ [ factTag fact
           | lemma <- theoryLemmas thy,
             fact <- formulaFacts lemma._lFormula
           ]
        ++ [ factTag fact
           | restriction <- theoryRestrictions thy,
             fact <- formulaFacts restriction._rstrFormula
           ]

loadQueries :: Theory sig c b p TranslationElement -> [Doc]
loadQueries thy =
  map (text . (._eText)) (lookupExportInfo "queries" thy)

-- | Render the prepared axiom and query plans and collect their headers.
loadLemmas ::
  [(String, PropertyOutcome PreparedQueryProperty)] ->
  [(String, PropertyOutcome PreparedAxiomProperty)] ->
  S.Set String ->  -- sharedEventTags: events that need rule IDs
  Bool ->  -- hasSpecificLemmas: whether --lemma flag was used
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  TranslationContext ->
  TypingEnvironment ->
  OpenTheory ->
  ([Doc], [Doc], S.Set ProVerifHeader)  -- (axioms, queries, headers)
loadLemmas preparedQueryPlans preparedAxiomPlans sharedEventTags hasSpecificLemmas lemSel tc te thy = (axiomDocs, queryDocs, headers)
  where
    thyLemmas = theoryLemmas thy

    -- Classify all lemmas
    classified = [(lem, classifyLemma hasSpecificLemmas tc lemSel lem) | lem <- thyLemmas]

    -- Separate into axioms and queries
    axiomsLemmas = [lem | (lem, AsAxiom) <- classified]
    queryLemmas = [lem | (lem, AsQuery) <- classified]

    -- Translate axioms using ppAxiomLemma
    axiomDocs =
      [ ppAxiomLemma
          sharedEventTags
          te
          lemma
          (planOutcome lemma._lName preparedAxiomPlans)
      | lemma <- axiomsLemmas
      ]

    -- Render exactly the query plans used during instrumentation analysis.
    queryDocs =
      [ ppLemma
          sharedEventTags
          te
          lemma
          (planOutcome lemma._lName preparedQueryPlans)
      | lemma <- queryLemmas
      ]

    allFacts =
      filter (not . isKnowledgeFact)
        [ fact
        | formula <- preparedFormulas,
          fact <- formulaFacts formula
        ]
    preparedFormulas =
      [ queryFormula.preparedQueryBody.preparedFormula
      | (_, PropertyEmitted prepared) <- preparedQueryPlans,
        queryFormula <- NE.toList prepared.preparedQueryFormulas
      ]
        ++ [ preparedFormulaPlan.preparedFormula
           | (_, PropertyEmitted prepared) <- preparedAxiomPlans,
             preparedFormulaPlan <- NE.toList prepared.preparedAxiomFormulas
           ]
    headers = makeEventHeaders sharedEventTags allFacts

-- | Classify how a lemma should be translated based on selector and attributes
classifyLemma ::
  Bool ->  -- ^ hasSpecificLemmas: whether --lemma flag was used
  TranslationContext
  -> (Lemma ProofSkeleton -> Bool)  -- ^ lemSel selector
  -> Lemma ProofSkeleton
  -> LemmaTranslationMode
classifyLemma hasSpecificLemmas tc lemSel lem
  -- If lemma doesn't pass module condition, exclude it
  | not (moduleCondition lem) = ExcludeLemma

  -- If specific lemmas were targeted AND this lemma is selected
  | hasSpecificLemmas && lemSel lem =
      -- Direct targeting: always treat as query (strip reuse/source behavior)
      AsQuery

  -- If specific lemmas targeted, this one is NOT selected, BUT it's reuse/source
  | hasSpecificLemmas && not (lemSel lem) && isReuseOrSource lem =
      if shouldSkipHelperLemma lem
        then ExcludeLemma
        else AsAxiom

  -- If specific lemmas targeted, this one is NOT selected, and NOT reuse/source
  | hasSpecificLemmas && not (lemSel lem) = ExcludeLemma

  -- If NO specific lemmas targeted (default: all lemmas), and is reuse/source
  | not hasSpecificLemmas && isReuseOrSource lem =
      if shouldSkipHelperLemma lem
        then ExcludeLemma
        else AsAxiom

  -- If NO specific lemmas targeted and lemma is NOT reuse/source
  | otherwise = AsQuery
  where
    shouldSkipHelperLemma l =
      (skipReuseLemmas tc && ReuseLemma `elem` l._lAttributes)
        || (skipSourceLemmas tc && SourceLemma `elem` l._lAttributes)

    isReuseOrSource l =
      ReuseLemma `elem` l._lAttributes || SourceLemma `elem` l._lAttributes

    moduleCondition l =
      let modules = concat [ls | LemmaModule ls <- l._lAttributes]
       in null modules || exportModule (trans tc) `elem` modules

loadRestrictions ::
  S.Set String ->
  TypingEnvironment ->
  [(String, PropertyOutcome PreparedRestrictionProperty)] ->
  OpenTheory ->
  ([Doc], S.Set ProVerifHeader)
loadRestrictions sharedEventTags te preparedRestrictionPlans thy =
  let rs = theoryRestrictions thy
      docs =
        [ ppRestr
            sharedEventTags
            te
            restriction
            (planOutcome restriction._rstrName preparedRestrictionPlans)
        | restriction <- rs
        ]
      allFacts =
        [ fact
        | (_, PropertyEmitted prepared) <- preparedRestrictionPlans,
          preparedFormulaPlan <- NE.toList prepared.preparedRestrictionFormulas,
          fact <- formulaFacts preparedFormulaPlan.preparedFormula
        ]
      validFacts =
        [ f
        | f@(Fact tag _ _) <- allFacts,
          not (isKnowledgeFact f),
          factTagName tag `notElem` ["OnlyOnce", "DistinctFact"]
        ]
      headers = makeEventHeaders sharedEventTags validFacts
   in (docs, headers)
