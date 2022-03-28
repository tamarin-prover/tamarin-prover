{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


module Lemma (
  LemmaAttribute(..)
  , TraceQuantifier(..)
  , ProtoLemma(..)
  , Lemma(..)
  , SyntacticLemma(..)
  , DiffLemma(..)
  , lName
  , lTraceQuantifier 
  , lFormula        
  , lAttributes     
  , lProof
  , lDiffName
  , lDiffAttributes
  , lDiffProof
  , lemmaSourceKind
  , addLeftLemma
  , addRightLemma
  , toSystemTraceQuantifier
  , isSourceLemma
  , isLeftLemma
  , isRightLemma

) where


import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Theory.Constraint.Solver (GoalRanking)
import Theory.Model
import Data.Label as L
import Theory.Constraint.System

------------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------------

-- | An attribute for a 'Lemma'.
data LemmaAttribute =
         SourceLemma
       | ReuseLemma
       | ReuseDiffLemma
       | InvariantLemma
       | HideLemma String
       | LHSLemma
       | RHSLemma
       | LemmaHeuristic [GoalRanking]
--        | BothLemma
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A 'TraceQuantifier' stating whether we check satisfiability of validity.
data TraceQuantifier = ExistsTrace | AllTraces
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A lemma describes a property that holds in the context of a theory
-- together with a proof of its correctness.
data ProtoLemma f p = Lemma
       { _lName            :: String
       , _lTraceQuantifier :: TraceQuantifier
       , _lFormula         :: f
       , _lAttributes      :: [LemmaAttribute]
       , _lProof           :: p
       }
       deriving( Generic)
$(mkLabels [''ProtoLemma])

type Lemma = ProtoLemma LNFormula
type SyntacticLemma = ProtoLemma SyntacticLNFormula

deriving instance Eq p => Eq (Lemma p)
deriving instance Ord p => Ord (Lemma p)
deriving instance Show p => Show (Lemma p)
deriving instance NFData p => NFData (Lemma p)
deriving instance Binary p => Binary  (Lemma p)



-- | A diff lemma describes a correspondence property that holds in the context of a theory
-- together with a proof of its correctness.
data DiffLemma p = DiffLemma
       { _lDiffName            :: String
--        , _lTraceQuantifier :: TraceQuantifier
--        , _lFormula         :: LNFormula
       , _lDiffAttributes      :: [LemmaAttribute]
       , _lDiffProof           :: p
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''DiffLemma])



-- | An accountability Lemma describes a property that holds in the context
-- of a theory and some parties with a verdict function
--data AccLemma v p par = AccLemma
--       { _acName            :: String
--       , _acTraceQuantifier :: TraceQuantifier
--       , _acFormula         :: LNFormula
--       , _acAttributes      :: [LemmaAttribute]
--       , _acVerdict         :: v
--       , _acProof           :: p
--       , _acParties         :: par
--       }
--       deriving( Eq, Ord, Show, Generic, NFData, Binary )


-- Instances
------------

instance Functor Lemma where
    fmap f (Lemma n qua fm atts prf) = Lemma n qua fm atts (f prf)

instance Foldable Lemma where
    foldMap f = f . L.get lProof

instance Traversable Lemma where
    traverse f (Lemma n qua fm atts prf) = Lemma n qua fm atts <$> f prf

instance Functor DiffLemma where
    fmap f (DiffLemma n atts prf) = DiffLemma n atts (f prf)

instance Foldable DiffLemma where
    foldMap f = f . L.get lDiffProof

instance Traversable DiffLemma where
    traverse f (DiffLemma n atts prf) = DiffLemma n atts <$> f prf


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