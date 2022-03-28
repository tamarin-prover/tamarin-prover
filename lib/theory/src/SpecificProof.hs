module SpecificProof (
    module SpecificProof
) where

import           Prelude                             hiding (id, (.))

import           Theory.Proof
import Lemmas
import Theory.Model

------------------------------------------------------------------------------
-- Specific proof types
------------------------------------------------------------------------------

-- | Proof skeletons are used to represent proofs in open theories.
type ProofSkeleton    = Proof ()

-- | Convert a proof skeleton to an incremental proof without any sequent
-- annotations.
skeletonToIncrementalProof :: ProofSkeleton -> IncrementalProof
skeletonToIncrementalProof = fmap (fmap (const Nothing))

-- | Convert an incremental proof to a proof skeleton by dropping all
-- annotations.
incrementalToSkeletonProof :: IncrementalProof -> ProofSkeleton
incrementalToSkeletonProof = fmap (fmap (const ()))

-- | Proof skeletons are used to represent proofs in open theories.
type DiffProofSkeleton    = DiffProof ()

-- | Convert a proof skeleton to an incremental proof without any sequent
-- annotations.
skeletonToIncrementalDiffProof :: DiffProofSkeleton -> IncrementalDiffProof
skeletonToIncrementalDiffProof = fmap (fmap (const Nothing))

-- | Convert an incremental proof to a proof skeleton by dropping all
-- annotations.
incrementalToSkeletonDiffProof :: IncrementalDiffProof -> DiffProofSkeleton
incrementalToSkeletonDiffProof = fmap (fmap (const ()))

-- Lemma construction/modification
----------------------------------

-- | Create a new unproven lemma from a formula modulo E.
unprovenLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> LNFormula
              -> Lemma ProofSkeleton
unprovenLemma name atts qua fm = Lemma name qua fm atts (unproven ())

skeletonLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> f -> p -> ProtoLemma f p
skeletonLemma name atts qua fm = Lemma name qua fm atts

-- | Create a new unproven diff lemma.
unprovenDiffLemma :: String -> [LemmaAttribute]
              -> DiffLemma DiffProofSkeleton
unprovenDiffLemma name atts = DiffLemma name atts (diffUnproven ())

skeletonDiffLemma :: String -> [LemmaAttribute] -> DiffProofSkeleton -> DiffLemma DiffProofSkeleton
skeletonDiffLemma name atts = DiffLemma name atts
