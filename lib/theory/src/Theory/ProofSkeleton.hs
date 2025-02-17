module Theory.ProofSkeleton
  ( ProofSkeleton,
    DiffProofSkeleton,
    skeletonToIncrementalProof,
    incrementalToSkeletonProof,
    skeletonToIncrementalDiffProof,
    unprovenLemma,
    skeletonLemma,
    unprovenDiffLemma,
    skeletonDiffLemma,
    incrementalToSkeletonDiffProof,
  prettyIncrementalProof, prettyIncrementalDiffProof)
where

import           Prelude                             hiding (id, (.))

import           Theory.Proof
import Lemma
import Theory.Model
import Text.PrettyPrint.Highlight
import Theory.Text.Pretty
import Control.Category
import Data.Maybe

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
unprovenLemma name atts qua fm = Lemma name "Unpr_inSkeleton" False qua fm atts (unproven ())

skeletonLemma :: String -> String -> Bool -> [LemmaAttribute] -> TraceQuantifier -> f -> p -> ProtoLemma f p
skeletonLemma name ptxt m atts qua fm = Lemma name ptxt m qua fm atts

-- | Create a new unproven diff lemma.
unprovenDiffLemma :: String -> [LemmaAttribute]
              -> DiffLemma DiffProofSkeleton
unprovenDiffLemma name atts = DiffLemma name atts (diffUnproven ())

skeletonDiffLemma :: String -> [LemmaAttribute] -> DiffProofSkeleton -> DiffLemma DiffProofSkeleton
skeletonDiffLemma = DiffLemma




prettyIncrementalProof :: HighlightDocument d => IncrementalProof -> d
prettyIncrementalProof = prettyProofWith ppStep (const id)
  where
    ppStep step = sep
      [ prettyProofMethod (psMethod step)
      , if isNothing (psInfo step) then multiComment_ ["unannotated"]
                                   else emptyDoc
      ]

prettyIncrementalDiffProof :: HighlightDocument d => IncrementalDiffProof -> d
prettyIncrementalDiffProof = prettyDiffProofWith ppStep (const id)
  where
    ppStep step = sep
      [ prettyDiffProofMethod (dpsMethod step)
      , if isNothing (dpsInfo step) then multiComment_ ["unannotated"]
                                    else emptyDoc
      ]



