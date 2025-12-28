{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Items.LemmaItem (
    module Items.LemmaItem
) where

import GHC.Records
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Optics.TH (makeFieldLabelsNoPrefix)
import Theory.Constraint.Solver (GoalRanking, ProofContext)
import Theory.Model
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
       | LemmaHeuristic [GoalRanking ProofContext]
       | LemmaTactic String
       | LemmaModule [ModuleType]
--        | BothLemma
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A 'TraceQuantifier' stating whether we check satisfiability of validity.
data TraceQuantifier = ExistsTrace | AllTraces
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A lemma describes a property that holds in the context of a theory
-- together with a proof of its correctness.
data ProtoLemma f p = Lemma
       { name            :: String
       , plaintext       :: String
       , modified        :: Bool
       , traceQuantifier :: TraceQuantifier
       , formula         :: f
       , originalFormula :: Maybe f
       , attributes      :: [LemmaAttribute]
       , proof           :: p
       }
       deriving( Generic)

makeFieldLabelsNoPrefix ''ProtoLemma

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
       { name            :: String
--       , traceQuantifier :: TraceQuantifier
--       , formula         :: LNFormula
       , attributes      :: [LemmaAttribute]
       , proof           :: p
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

makeFieldLabelsNoPrefix ''DiffLemma

type HasLemmaName l = HasField "lName" l String

instance HasField "lName" (ProtoLemma f p) String where
  getField = (.name)
instance HasField "lName" (DiffLemma p) String where
  getField = (.name)

type HasLemmaPlaintext l = HasField "lPlaintext" l String

instance HasField "lPlaintext" (ProtoLemma f p) String where
  getField = (.plaintext)


type HasLemmaAttributes l = HasField "lAttributes" l [LemmaAttribute]

instance HasField "lAttributes" (ProtoLemma f p) [LemmaAttribute] where
  getField = (.attributes)
instance HasField "lAttributes" (DiffLemma p) [LemmaAttribute] where
  getField = (.attributes)


-- Instances
------------

instance Functor Lemma where
    fmap f (Lemma n p m qua fm ofm atts prf) = Lemma n p m qua fm ofm atts (f prf)

instance Foldable Lemma where
    foldMap f = f . (.proof)

instance Traversable Lemma where
    traverse f (Lemma n p m qua fm ofm atts prf) = Lemma n p m qua fm ofm atts <$> f prf

instance Functor DiffLemma where
    fmap f (DiffLemma n atts prf) = DiffLemma n atts (f prf)

instance Foldable DiffLemma where
    foldMap f = f . (.proof)

instance Traversable DiffLemma where
    traverse f (DiffLemma n atts prf) = DiffLemma n atts <$> f prf
