module Lemma (
  LemmaAttribute(..)
  , TraceQuantifier(..)
  , ProtoLemma(..)
  , DiffLemma(..)
  , lemmaSourceKind
  , addLeftLemma
  , addRightLemma
  , toSystemTraceQuantifier
  , isSourceLemma
  , isLeftLemma
  , isRightLemma
  ,module Items.LemmaItem

) where

import Data.Label as L
import Theory.Constraint.System
import Items.LemmaItem



-- | The source kind allowed for a lemma.
lemmaSourceKind :: Lemma p -> SourceKind
lemmaSourceKind lem
  | SourceLemma `elem` L.get lAttributes lem = RawSource
  | otherwise                                = RefinedSource

-- | Adds the LHS lemma attribute.
addLeftLemma :: ProtoLemma f p -> ProtoLemma f p
addLeftLemma lem =
     L.set lAttributes (LHSLemma:(L.get lAttributes lem)) lem

-- | Adds the RHS lemma attribute.
addRightLemma :: ProtoLemma f p -> ProtoLemma f p
addRightLemma lem =
     L.set lAttributes (RHSLemma:(L.get lAttributes lem)) lem

-- Lemma queries
----------------------------------

-- | Convert a trace quantifier to a sequent trace quantifier.
toSystemTraceQuantifier :: TraceQuantifier -> SystemTraceQuantifier
toSystemTraceQuantifier AllTraces   = ExistsNoTrace
toSystemTraceQuantifier ExistsTrace = ExistsSomeTrace

-- | True iff the lemma can be used as a source lemma.
isSourceLemma :: Lemma p -> Bool
isSourceLemma lem =
     (AllTraces == L.get lTraceQuantifier lem)
  && (SourceLemma `elem` L.get lAttributes lem)

-- | True iff the lemma is a LHS lemma.
isLeftLemma :: ProtoLemma f p -> Bool
isLeftLemma lem =
     (LHSLemma `elem` L.get lAttributes lem)

-- | True iff the lemma is a RHS lemma.
isRightLemma :: ProtoLemma f p -> Bool
isRightLemma lem =
     (RHSLemma `elem` L.get lAttributes lem)

-- -- | True iff the lemma is a Both lemma.
-- isBothLemma :: Lemma p -> Bool
-- isBothLemma lem =
--      (BothLemma `elem` L.get lAttributes lem)