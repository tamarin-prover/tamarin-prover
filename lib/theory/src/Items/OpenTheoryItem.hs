module Items.OpenTheoryItem (
    module Items.OpenTheoryItem
) where

import Rule
import Theory.ProofSkeleton
import Theory.Model
import TheoryObject
import Prelude hiding (id, (.))

-- | Open theories can be extended. Invariants:
--   1. Lemma names are unique.
type OpenTheory =
    Theory SignaturePure [IntrRuleAC] OpenProtoRule ProofSkeleton SapicElement

type OpenTheoryItem = TheoryItem OpenProtoRule ProofSkeleton SapicElement

-- | Open theories can be extended. Invariants:
--   1. Lemma names are unique.
--   2. All SapicItems are translated
type OpenTranslatedTheory =
    Theory SignaturePure [IntrRuleAC] OpenProtoRule ProofSkeleton ()

-- | Open diff theories can be extended. Invariants:
--   1. Lemma names are unique.
type OpenDiffTheory =
    DiffTheory SignaturePure [IntrRuleAC] DiffProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton

-- | Either Therories can be Either a normal or a diff theory

-- type EitherTheory = Either Theory  DiffTheory
type EitherOpenTheory = Either OpenTheory OpenDiffTheory
