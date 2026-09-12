-- |
-- Rendering and warning-policy integration for structured export diagnostics.
module Export.Diagnostic
  ( diagnosticIsProofRelevant,
    diagnosticsToWfReport,
    renderExportDiagnostics,
    collectBuiltinDiagnostics,
    collectTypingDiagnostics,
  )
where

import Data.Foldable (toList)
import Data.List (intersperse)
import Data.Maybe (mapMaybe)
import Data.Map qualified as M
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set qualified as S
import Export.ProVerif.Header (BuiltinTranslation (..), builtins)
import Export.Types
import Sapic.Typing
import Text.PrettyPrint.Class
import Theory
import Theory.Tools.Wellformedness (WfErrorReport, underlineTopic)

diagnosticIsProofRelevant :: ExportDiagnostic -> Bool
diagnosticIsProofRelevant diagnostic =
  case diagnostic.diagnosticImpact of
    Informational -> False
    UntranslatedGoal -> True
    ChangedAssumptions -> True
    ChangedProcessSemantics -> True

diagnosticsToWfReport :: Seq ExportDiagnostic -> WfErrorReport
diagnosticsToWfReport =
  map (\diagnostic -> (underlineTopic "Export translation", diagnosticDoc diagnostic))
    . filter diagnosticIsProofRelevant
    . toList

renderExportDiagnostics :: Seq ExportDiagnostic -> Doc
renderExportDiagnostics diagnostics
  | null entries = emptyDoc
  | otherwise = vcat (intersperse (text "") (banner ++ sections))
  where
    entries = toList diagnostics
    proofRelevant = filter diagnosticIsProofRelevant entries
    banner =
      [ text "WARNING: export omitted or approximated proof-relevant input."
      | not (null proofRelevant)
      ]
    sections =
      mapMaybe
        (uncurry renderSection)
        [ ("Changed assumptions", ChangedAssumptions),
          ("Untranslated goals", UntranslatedGoal),
          ("Changed process semantics", ChangedProcessSemantics),
          ("Export notes", Informational)
        ]
    renderSection heading impact =
      case filter ((== impact) . (.diagnosticImpact)) entries of
        [] -> Nothing
        matching ->
          Just
            ( text heading
                $$ text (replicate (length heading) '=')
                $$ vcat (map ((text "- " <>) . diagnosticDoc) matching)
            )

diagnosticDoc :: ExportDiagnostic -> Doc
diagnosticDoc diagnostic =
  text (subjectLabel diagnostic.diagnosticSubject)
    <> text ": "
    <> text diagnostic.diagnosticMessage
    <> text " ["
    <> text diagnostic.diagnosticCode
    <> text "]"

subjectLabel :: DiagnosticSubject -> String
subjectLabel ProcessSubject = "Process"
subjectLabel (LemmaSubject name) = "Lemma `" ++ name ++ "`"
subjectLabel (AxiomSubject name) = "Axiom `" ++ name ++ "`"
subjectLabel (RestrictionSubject name) = "Restriction `" ++ name ++ "`"
subjectLabel (BuiltinSubject name) = "Builtin `" ++ name ++ "`"

collectBuiltinDiagnostics :: OpenTheory -> Seq.Seq ExportDiagnostic
collectBuiltinDiagnostics thy =
  Seq.fromList
    [ ExportDiagnostic
        "PV-BUILTIN-APPROXIMATED"
        ChangedProcessSemantics
        (BuiltinSubject name)
        "uses a best-effort target encoding"
    | name <- theoryBuiltins thy,
      BestEffortBuiltin _ <- [builtins name]
    ]

collectTypingDiagnostics :: TypingEnvironment -> Seq.Seq ExportDiagnostic
collectTypingDiagnostics typeEnvironment =
  Seq.fromList
    [ ExportDiagnostic
        "PV-SORT-COERCED"
        ChangedProcessSemantics
        ProcessSubject
        ( "variable `"
            ++ name
            ++ "` of sort "
            ++ show variableSort
            ++ " is encoded as ProVerif bitstring"
        )
    | LVar name variableSort _ <- S.toList distinctVariables,
      variableSort `elem` [LSortPub, LSortFresh, LSortNat]
    ]
  where
    distinctVariables = S.fromList (M.keys typeEnvironment.vars)
