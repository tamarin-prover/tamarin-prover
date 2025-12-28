module Lemma (
  LemmaAttribute(..)
  , TraceQuantifier(..)
  , ProtoLemma(..)
  , DiffLemma(..)
  , lemmaSourceKind
  , applyMacroInLemma
  , addLeftLemma
  , addRightLemma
  , toSystemTraceQuantifier
  , isSourceLemma
  , isLeftLemma
  , isRightLemma
  , module Items.LemmaItem
  , prettyLemma
  , prettyLemmaName
  , prettyLemmaAttribute
  , prettyDiffLemmaName
  , prettyTraceQuantifier
  , prettyDiffLemma
  , prettyEitherLemma) where

import Theory.Constraint.System
import Items.LemmaItem
import Optics.Core (set)


import Text.PrettyPrint.Highlight
import Term.Macro
import Theory.Text.Pretty
import Theory.Model
--import Theory.Constraint.Solver
import Data.List (intercalate)
import Data.Maybe(fromMaybe)


-- | The source kind allowed for a lemma.
lemmaSourceKind :: Lemma p -> SourceKind
lemmaSourceKind lem
  | SourceLemma `elem` lem.attributes = RawSource
  | otherwise                         = RefinedSource

-- | Adds the LHS lemma attribute.
addLeftLemma :: ProtoLemma f p -> ProtoLemma f p
addLeftLemma lem =
     set #attributes (LHSLemma:lem.attributes) lem

-- | Adds the RHS lemma attribute.
addRightLemma :: ProtoLemma f p -> ProtoLemma f p
addRightLemma lem =
     set #attributes (RHSLemma:lem.attributes) lem

-- Lemma queries
----------------------------------

-- | Convert a trace quantifier to a sequent trace quantifier.
toSystemTraceQuantifier :: TraceQuantifier -> SystemTraceQuantifier
toSystemTraceQuantifier AllTraces   = ExistsNoTrace
toSystemTraceQuantifier ExistsTrace = ExistsSomeTrace

-- | True iff the lemma can be used as a source lemma.
isSourceLemma :: Lemma p -> Bool
isSourceLemma lem =
     (AllTraces == lem.traceQuantifier)
  && (SourceLemma `elem` lem.attributes)

-- | True iff the lemma is a LHS lemma.
isLeftLemma :: ProtoLemma f p -> Bool
isLeftLemma lem =
     (LHSLemma `elem` lem.attributes)

-- | True iff the lemma is a RHS lemma.
isRightLemma :: ProtoLemma f p -> Bool
isRightLemma lem =
     (RHSLemma `elem` lem.attributes)

-- -- | True iff the lemma is a Both lemma.
-- isBothLemma :: Lemma p -> Bool
-- isBothLemma lem =
--      (BothLemma `elem` L.get lAttributes lem)

-- | Apply macros to a lemma
applyMacroInLemma :: [LNMacro] -> Lemma p -> Lemma p
applyMacroInLemma macros lemma = 
  let originalFormula = lemma.formula
      expandedFormula = applyMacroInFormula macros originalFormula
  in set #originalFormula (Just originalFormula) $
     set #formula expandedFormula lemma

-- | Pretty print the lemma name together with its attributes.
prettyLemmaName :: HighlightDocument d => Lemma p -> d
prettyLemmaName l = case l.attributes of
      [] -> text l.name
      as -> text l.name <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)

prettyLemmaAttribute :: Document d => LemmaAttribute -> d
prettyLemmaAttribute SourceLemma        = text "sources"
prettyLemmaAttribute ReuseLemma         = text "reuse"
prettyLemmaAttribute ReuseDiffLemma     = text "diff_reuse"
prettyLemmaAttribute InvariantLemma     = text "use_induction"
prettyLemmaAttribute (HideLemma s)      = text ("hide_lemma=" ++ s)
prettyLemmaAttribute (LemmaHeuristic h) = text ("heuristic=" ++ (prettyGoalRankings h))
prettyLemmaAttribute (LemmaModule h)    = text ("output=[" ++ intercalate "," (map show h)  ++ "]")
prettyLemmaAttribute LHSLemma           = text "left"
prettyLemmaAttribute RHSLemma           = text "right"
prettyLemmaAttribute _                  = emptyDoc
--     prettyLemmaAttribute BothLemma      = text "both"


-- | Pretty print the diff lemma name
prettyDiffLemmaName :: HighlightDocument d => DiffLemma p -> d
prettyDiffLemmaName l = text l.name

-- | Pretty print a lemma.
prettyLemma :: HighlightDocument d => (p -> d) -> Lemma p -> d
prettyLemma ppPrf lem =
    kwLemma <-> prettyLemmaName lem <> colon $-$
    (nest 2 $
      sep [ prettyTraceQuantifier lem.traceQuantifier
          , doubleQuotes $ prettyLNFormula (fromMaybe expandedFormula ogFormula)
          ]
    )
    $-$
    ppLNFormulaGuarded expandedFormula
    $-$
    ppPrf lem.proof
  where
    expandedFormula = lem.formula
    ogFormula = lem.originalFormula
    ppLNFormulaGuarded fm = case formulaToGuarded fm of
        Left err -> multiComment $
            text "conversion to guarded formula failed:" $$
            nest 2 err
        Right gf -> case toSystemTraceQuantifier lem.traceQuantifier of
          ExistsNoTrace -> multiComment
            ( text "guarded formula characterizing all counter-examples:" $-$
              doubleQuotes (prettyGuarded (gnot gf)) )
          ExistsSomeTrace -> multiComment
            ( text "guarded formula characterizing all satisfying traces:" $-$
              doubleQuotes (prettyGuarded gf) )

-- | Pretty print an Either lemma.
prettyEitherLemma :: HighlightDocument d => (p -> d) -> (Side, Lemma p) -> d
prettyEitherLemma ppPrf (_, lem) =
    kwLemma <-> prettyLemmaName lem <> colon $-$
    (nest 2 $
      sep [ prettyTraceQuantifier lem.traceQuantifier
          , doubleQuotes $ prettyLNFormula (fromMaybe expandedFormula ogFormula)
          ]
    )
    $-$
    ppLNFormulaGuarded expandedFormula
    $-$
    ppPrf lem.proof
  where
    expandedFormula = lem.formula
    ogFormula = lem.originalFormula
    ppLNFormulaGuarded fm = case formulaToGuarded fm of
        Left err -> multiComment $
            text "conversion to guarded formula failed:" $$
            nest 2 err
        Right gf -> case toSystemTraceQuantifier lem.traceQuantifier of
          ExistsNoTrace -> multiComment
            ( text "guarded formula characterizing all counter-examples:" $-$
              doubleQuotes (prettyGuarded (gnot gf)) )
          ExistsSomeTrace -> multiComment
            ( text "guarded formula characterizing all satisfying traces:" $-$
              doubleQuotes (prettyGuarded gf) )

-- | Pretty print a diff lemma.
prettyDiffLemma :: HighlightDocument d => (p -> d) -> DiffLemma p -> d
prettyDiffLemma ppPrf lem =
    kwDiffLemma <-> prettyDiffLemmaName lem <> colon
    $-$
    ppPrf lem.proof

-- | Pretty print a 'TraceQuantifier'.
prettyTraceQuantifier :: Document d => TraceQuantifier -> d
prettyTraceQuantifier ExistsTrace = text "exists-trace"
prettyTraceQuantifier AllTraces   = text "all-traces"
-- FIXME: Sort instances into the right files
