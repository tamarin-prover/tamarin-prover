-- |
-- ProVerif observational-equivalence backend entry point.
module Export.ProVerifEquivalence (prettyProVerifEquivTheory) where

import Data.List (intersperse)
import Data.Set qualified as Set
import Export.Diagnostic
import Export.ProVerif (loadQueries)
import Export.ProVerif.Header (attribHeaders, finalizeHeaders, stateHeaders)
import Export.ProVerif.Render (renderSapicFormula)
import Export.Sapic
import Export.Types
import Sapic.Typing (TypingEnvironment)
import Text.PrettyPrint.Class
import Theory

prettyProVerifEquivTheory ::
  (OpenTheory, TypingEnvironment) ->
  IO (Either ExportError ExportResult)
prettyProVerifEquivTheory (thy, typeEnvironment) =
  captureExport diagnostics $ do
    theoryHeaders <- loadHeaders Set.empty context thy typeEnvironment
    let translationHeaders =
          [ baseHeaders,
            equivalenceHeaders,
            diffEquivalenceHeaders,
            macroHeaders
          ]
    headers <- finalizeHeaders theoryHeaders translationHeaders
    processes <- finalProcesses
    pure $
      proVerifEquivalenceTemplate
        (attribHeaders context headers)
        queries
        processes
        macroProcesses
        comments
  where
    context = emptyTC {predicates = theoryPredicates thy}
    (equivalenceLemmas, equivalenceHeaders, hasBoundState, hasUnboundState) =
      loadEquivProc renderSapicFormula context thy
    (diffEquivalenceLemmas, diffEquivalenceHeaders, _, diffHasUnboundState) =
      loadDiffProc renderSapicFormula context thy
    baseHeaders
      | hasUnboundState || diffHasUnboundState = stateHeaders
      | otherwise = Set.empty
    finalProcesses
      | length equivalenceLemmas + length diffEquivalenceLemmas > 1 =
          translationFail "ProVerif supports at most one equivalence or diff-equivalence query."
      | otherwise = pure (equivalenceLemmas ++ diffEquivalenceLemmas)
    queries = loadQueries thy
    (macroProcesses, macroHeaders)
      | hasBoundState = ([text ""], Set.empty)
      | otherwise = loadMacroProc renderSapicFormula context thy
    comments = formalCommentDocs thy
    diagnostics = collectBuiltinDiagnostics thy <> collectTypingDiagnostics typeEnvironment

proVerifEquivalenceTemplate :: (Document d) => [d] -> [d] -> [d] -> [d] -> [d] -> d
proVerifEquivalenceTemplate headers queries equivalenceLemmas macroProcesses comments =
  vcat headers
    $$ vcat queries
    $$ vcat macroProcesses
    $$ vcat equivalenceLemmas
    $--$ vcat (intersperse (text "") comments)
