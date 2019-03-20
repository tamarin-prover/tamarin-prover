{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- {-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Before translation, a process is annotated. This defines these
-- annotations.
module Sapic.Annotation (
    ProcessAnnotation(..)
    , AnnotatedProcess
    , annLock
    , annUnlock
    , toAnProcess
    , toProcess
    , AnLVar (..)
    , GoodAnnotation
) where
import           Data.Data
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
-- import Control.Monad.Catch
-- import Sapic.Exceptions
-- import Theory
import Theory.Sapic
import           GHC.Generics                     (Generic)
import           Data.Binary
-- import Theory.Model.Rule
-- import Data.Typeable
-- import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh
-- import Control.Monad.Trans.FastFresh
import Term.LTerm

-- | Variables used to annotate locks. Encapsulated in newtype because of
-- Semigroup instance below
newtype AnLVar = AnLVar LVar
     deriving( Typeable, Data, Generic, Binary, Show )
     -- original definition: deriving( Typeable, Data, Generic, NFData, Binary )

instance Semigroup AnLVar where  -- override annotations if necessary
    (<>) _ b = b

-- | Annotations used in the translation
data ProcessAnnotation = ProcessAnnotation {
    processnames :: [String] -- processes identifiers recovered from "let P = "  bindings
  , lock :: Maybe AnLVar     -- Fresh variables annotating locking action and unlocking actions. 
  , unlock :: Maybe AnLVar   -- Matching actions should have the same variables.
  } deriving (Show, Typeable)


-- | Any annotation that is good enough to be converted back into a Process
--  can at least recover the names of the processes used to bind
--  subprocesses
-- annotate the multiset rewrite rules with:
--      - the Name or Names of the process (e.g., [A, B] in let B = 0 let A = B | 0)
class GoodAnnotation a where
    getProcessNames :: a ->  [String]

instance GoodAnnotation ProcessAnnotation
    where
        getProcessNames = processnames
  
instance Monoid ProcessAnnotation where
    mempty = ProcessAnnotation [] Nothing Nothing
    mappend p1 p2 = ProcessAnnotation 
        (processnames p1 `mappend` processnames p2)
        (lock p1 `mappend` lock p2)
        (unlock p1 `mappend` unlock p2)

instance Semigroup ProcessAnnotation where
    (<>) p1 p2 = ProcessAnnotation 
        (processnames p1 `mappend` processnames p2)
        (lock p1 <> lock p2)
        (unlock p1 <> unlock p2)

newtype AnnotatedProcess = AnProcess ProcessAnnotation
    deriving (Typeable, Monoid,Semigroup,Show)

-- | quickly create Annotations from variable names for locking and
-- unlocking
annLock :: AnLVar -> ProcessAnnotation
annLock v = ProcessAnnotation { processnames = [], lock = Just v, unlock = Nothing }
annUnlock :: AnLVar -> ProcessAnnotation
annUnlock v = ProcessAnnotation { processnames = [], lock = Nothing, unlock = Just v }

-- | Convert to and from Process, i.e., AnProcess with processnames only.
toAnProcess :: Process -> AnProcess ProcessAnnotation
toAnProcess = fmap f
    where
        f l = ProcessAnnotation { processnames = l, lock = Nothing, unlock = Nothing }

toProcess :: GoodAnnotation an => AnProcess an -> Process
toProcess = fmap f
    where
        f l = getProcessNames l

