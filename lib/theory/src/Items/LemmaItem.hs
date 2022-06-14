{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Items.LemmaItem (
    module Items.LemmaItem
) where

import GHC.Records
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Theory.Constraint.Solver (GoalRanking)
import Theory.Model
import Data.Label as L
import Theory.Module

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
       | LemmaModule [ModuleType]
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

type HasLemmaName l = HasField "lName" l String

instance HasField "lName" (ProtoLemma f p) String where
  getField = _lName
instance HasField "lName" (DiffLemma p) String where
  getField = _lDiffName

type HasLemmaAttributes l = HasField "lAttributes" l [LemmaAttribute]

instance HasField "lAttributes" (ProtoLemma f p) [LemmaAttribute] where
  getField = _lAttributes
instance HasField "lAttributes" (DiffLemma p) [LemmaAttribute] where
  getField = _lDiffAttributes


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