{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric              #-}

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
    , annSecretChannel
    , annDestructorEquation
    , annUnlock
    , toAnProcess
    , toProcess
    , AnVar (..)
    , AnProcess (..)
    , unAnProcess
    , GoodAnnotation(..)
    , getProcessNames
    , setProcessNames
,annElse) where
import           Data.Data
-- import Data.List
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
newtype AnVar v = AnVar v
     deriving( Typeable, Data, Generic, Binary, Show )
     -- original definition: deriving( Typeable, Data, Generic, NFData, Binary )

instance Semigroup (AnVar v) where  -- override annotations if necessary
    (<>) _ b = b

-- | Annotations used in the translation
-- Reuses ProcessParsedAnnotation
data ProcessAnnotation v = ProcessAnnotation {
    parsingAnn    :: ProcessParsedAnnotation -- annotations recovered during parsing, includes 
                                             -- processes identifiers recovered from "let P = "  bindings
  , lock          :: Maybe (AnVar v)   -- Fresh variables annotating locking action and unlocking actions.
  , unlock        :: Maybe (AnVar v)   -- Matching actions should have the same variables.
  , secretChannel :: Maybe (AnVar v)   -- If a channel is secret, we can perform a silent transition.
  , destructorEquation :: Maybe (LNTerm, LNTerm) -- the two terms that can be matched to model a let binding with a destructor on the right hand side.
  , elseBranch         :: Bool --- do we have a non-zero else branch? Used for let translation
  } deriving (Show, Typeable)

-- | Any annotation that is good enough to be converted back into a Process
--  can at least recover the names of the processes used to bind
--  subprocesses
-- annotate the multiset rewrite rules with:
--      - the Name or Names of the process (e.g., [A, B] in let B = 0 let A = B | 0)
class GoodAnnotation a where
    getProcessParsedAnnotation :: a ->  ProcessParsedAnnotation
    setProcessParsedAnnotation :: ProcessParsedAnnotation -> a -> a
    defaultAnnotation :: a

instance GoodAnnotation (ProcessAnnotation v)
    where
        getProcessParsedAnnotation = parsingAnn
        setProcessParsedAnnotation pn an = an { parsingAnn = pn }
        defaultAnnotation   = mempty

instance GoodAnnotation (ProcessParsedAnnotation)
    where
        getProcessParsedAnnotation = id
        setProcessParsedAnnotation pn _ = pn
        defaultAnnotation   = mempty

instance Monoid (ProcessAnnotation v) where
    mempty = ProcessAnnotation mempty mempty mempty mempty Nothing True
    mappend p1 p2 = ProcessAnnotation
        (parsingAnn p1 `mappend` parsingAnn p2)
        (lock p1 `mappend` lock p2)
        (unlock p1 `mappend` unlock p2)
        (secretChannel p1 `mappend` secretChannel p2)
        (destructorEquation p2)
        (elseBranch p2)

getProcessNames :: GoodAnnotation ann => ann -> [String]
getProcessNames = processnames . getProcessParsedAnnotation

setProcessNames :: GoodAnnotation a => [String] -> a -> a
setProcessNames pn = setProcessParsedAnnotation (mempty {processnames = pn})


instance Semigroup (ProcessAnnotation v) where
    (<>) =  mappend

newtype AnnotatedProcess = LProcess (ProcessAnnotation LVar)
    deriving (Typeable, Monoid,Semigroup,Show)

data AnProcess ann = AnProcess (LProcess ann)
    deriving (Typeable, Show)

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
        f l = setProcessParsedAnnotation l defaultAnnotation

toProcess :: GoodAnnotation an => LProcess an -> PlainProcess
toProcess = unAnProcess . fmap f . AnProcess
    where
        f l = getProcessParsedAnnotation l
