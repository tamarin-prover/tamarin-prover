{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Before translation, a process is annotated. This defines these
-- annotations.
module Sapic.Annotation
  ( ProcessAnnotation(..)
  , AnnotatedProcess
  , AnnotatedSapicException
  , annLock
  , annSecretChannel
  , annDestructorEquation
  , annUnlock
  , toAnProcess
  , toProcess
  , AnVar (..)
  , AnProcess (..)
  , unAnProcess
  , getProcessNames
  , setProcessNames
  , annElse
  ) where

import Data.Binary
import Data.Data
import GHC.Generics (Generic)
import Term.LTerm
import Term.Substitution
import Theory.Sapic
import Sapic.Exceptions

-- | Variables used to annotate locks. Encapsulated in newtype because of
-- Semigroup instance below
newtype AnVar v = AnVar v
     deriving( Typeable, Data, Generic, Binary, Show )
     -- original definition: deriving( Typeable, Data, Generic, NFData, Binary )

instance Semigroup (AnVar v) where  -- override annotations if necessary
    (<>) _ b = b

-- | Annotations used in the translation
-- Reuses ProcessParsedAnnotation
data ProcessAnnotation v = ProcessAnnotation
  { parsingAnn    :: ProcessParsedAnnotation -- annotations recovered during parsing, includes
                                             -- processes identifiers recovered from "let P = "  bindings
  , lock          :: Maybe (AnVar v)   -- Fresh variables annotating locking action and unlocking actions.
  , unlock        :: Maybe (AnVar v)   -- Matching actions should have the same variables.
  , secretChannel :: Maybe (AnVar v)   -- If a channel is secret, we can perform a silent transition.
  , destructorEquation :: Maybe (LNTerm, LNTerm) -- the two terms that can be matched to model a let binding with a destructor on the right hand side.
  , elseBranch         :: Bool --- do we have a non-zero else branch? Used for let translation
  , pureState :: Bool -- anotates locks, inserts and lookup that correspond to a Pure state, so that they are optimized.
                      -- A pure state corresponds to a process of form `insert k,v` or `lock k; lookup k; .. ; insert k,v; unlock k` or similar (see States.hs)
  , stateChannel ::  Maybe (AnVar v) -- anotates state operations with the corresponding name identifier when possible.
  , isStateChannel :: Maybe SapicTerm -- annotates binding of channels that corresponds to state channels with their corresponding identifier.
  } deriving (Show, Typeable)

instance GoodAnnotation (ProcessAnnotation v)
    where
        getProcessParsedAnnotation = parsingAnn
        setProcessParsedAnnotation pn an = an { parsingAnn = pn }
        defaultAnnotation   = mempty

mayMerge :: Maybe a -> Maybe a -> Maybe a
mayMerge t@(Just _) _ = t
mayMerge _ t@(Just _) = t
mayMerge Nothing Nothing = Nothing

instance Monoid (ProcessAnnotation v) where
    mempty = ProcessAnnotation mempty mempty mempty mempty Nothing True False mempty Nothing

instance Semigroup (ProcessAnnotation v) where
  (<>)  p1 p2 = ProcessAnnotation
        (parsingAnn p1 <> parsingAnn p2)
        (lock p1 <> lock p2)
        (unlock p1 <> unlock p2)
        (secretChannel p1 <> secretChannel p2)
        (mayMerge (destructorEquation p1) (destructorEquation p2))
        (elseBranch p2)
        (pureState p1 || pureState p2)
        (stateChannel p1 <> stateChannel p2)
        (mayMerge (isStateChannel p1) (isStateChannel p2))

getProcessNames :: GoodAnnotation ann => ann -> [String]
getProcessNames = processnames . getProcessParsedAnnotation

setProcessNames :: GoodAnnotation a => [String] -> a -> a
setProcessNames pn = setProcessParsedAnnotation (mempty {processnames = pn})

instance (Apply s SapicTerm) => (Apply s (ProcessAnnotation v)) where
    apply = applyAnn

-- newtype AnnotatedProcess = LProcess (ProcessAnnotation LVar)
--     deriving (Typeable, Monoid,Semigroup,Show)

newtype AnProcess ann = AnProcess (LProcess ann)
    deriving (Typeable, Show)

type AnnotatedProcess = LProcess (ProcessAnnotation LVar)
type AnnotatedSapicException = SapicException (ProcessAnnotation LVar)

-- This instance is useful for modifying annotations, but not for much more.
instance Functor AnProcess where
    fmap f (AnProcess process) = AnProcess (f' process)
        where
        f' (ProcessNull an) = ProcessNull (f an)
        f' (ProcessAction a an p)   =  ProcessAction a (f an) (f' p)
        f' (ProcessComb c an pl pr)  = ProcessComb c (f an) (f' pl) (f' pr)

unAnProcess :: AnProcess ann -> LProcess ann
unAnProcess (AnProcess p) = p

-- | quickly create Annotations from variable names for locking and
-- unlocking
annLock :: AnVar v -> ProcessAnnotation v
annLock v = mempty {lock = Just v}

annUnlock :: AnVar v -> ProcessAnnotation v
annUnlock v = mempty {unlock = Just v}

annSecretChannel :: AnVar v -> ProcessAnnotation v
annSecretChannel v = mempty { secretChannel = Just v}

annDestructorEquation :: LNTerm -> LNTerm -> Bool -> ProcessAnnotation v
annDestructorEquation v1 v2 b =  mempty { destructorEquation = Just (v1, v2), elseBranch = b }

annElse ::  Bool -> ProcessAnnotation v
annElse b = mempty {elseBranch = b}

-- | Convert to and from Process, i.e., LProcess with processnames only.
toAnProcess :: GoodAnnotation an => PlainProcess -> LProcess an
toAnProcess = unAnProcess . fmap f . AnProcess
  where
        -- f :: ProcessParsedAnnotation -> an
        f l = mappendProcessParsedAnnotation l defaultAnnotation

toProcess :: GoodAnnotation an => LProcess an -> PlainProcess
toProcess = unAnProcess . fmap f . AnProcess
    where
        f = getProcessParsedAnnotation
