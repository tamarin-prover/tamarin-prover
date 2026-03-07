{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
-- |
-- Copyright   : (c) 2021 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Standard annotations for SAPIC processes after parsing
module Theory.Sapic.Annotation (
    -- types
      ProcessParsedAnnotation(..)
    -- utilities
    , mapProcessParsedAnnotation
    , mappendProcessParsedAnnotation
    -- type classes
    , GoodAnnotation(..)
,applyAnn) where

import Data.Binary
import Data.Data
import GHC.Generics (Generic)
import Control.Parallel.Strategies
import Term.Substitution
import Theory.Sapic.Term

-- | After parsing, the process is already annotated wth a list of process
--   identifiers. Any identifier in this in this list was inlined to give this
--   comment, e.g.,
--    let A = 0
--    let B = A | A
--    !B
--    has two Null-rules with annotation [A,B].
--  This will be helpful to recognise protocols roles and visualise them.

data ProcessParsedAnnotation = ProcessParsedAnnotation {
    -- String used in annotation to identify processes. Always a singleton list
      processnames      :: [String]
    -- additional information for Isolated Execution Environments feature
    , location       :: Maybe SapicTerm
    -- substitution to rename variables in subprocess back to how the user input them.
    -- 1. empty until process is renamed for uniqueness
    -- 2. only applies to variables bound at this subprocess
    -- 3. maps variables to variable terms
    , backSubstitution :: Subst Name LVar
    }
    deriving (Eq, Ord, Show, Generic)
instance NFData ProcessParsedAnnotation
instance Binary ProcessParsedAnnotation

-- deriving instance Data SapicSubst
deriving instance Data (Subst Name LVar)
deriving instance Data ProcessParsedAnnotation

instance Monoid ProcessParsedAnnotation where
    mempty = ProcessParsedAnnotation [] Nothing emptySubst

instance Semigroup ProcessParsedAnnotation where
    (<>) p1 p2 = ProcessParsedAnnotation
        (processnames p1 ++ processnames p2)
        (case (location p1, location p2) of
             (Nothing, Just l2) -> Just l2
             (l1, Nothing) -> l1
             (_, l2) -> l2)
        (backSubstitution p1 `compose` backSubstitution p2)

-- | Any annotation that is good enough to be converted back into a Process
--  can at least recover the names of the processes used to bind
--  subprocesses
-- annotate the multiset rewrite rules with:
--      - the Name or Names of the process (e.g., [A, B] in let B = 0 let A = B | 0)
class GoodAnnotation a where
    getProcessParsedAnnotation :: a ->  ProcessParsedAnnotation
    setProcessParsedAnnotation :: ProcessParsedAnnotation -> a -> a -- overwrites process annotation
    defaultAnnotation :: a

instance GoodAnnotation ProcessParsedAnnotation
    where
        getProcessParsedAnnotation = id
        setProcessParsedAnnotation pn _ = pn
        defaultAnnotation   = mempty

-- | apply @f@ to ProcessParsedAnnotation within @ann@
mapProcessParsedAnnotation :: GoodAnnotation a =>
    (ProcessParsedAnnotation -> ProcessParsedAnnotation) -> a -> a
mapProcessParsedAnnotation f ann =
    setProcessParsedAnnotation (f $ getProcessParsedAnnotation ann) ann

-- | mappend (i.e., overwrite or add as needed) to processParsedAnnotation
mappendProcessParsedAnnotation :: GoodAnnotation a => ProcessParsedAnnotation -> a -> a
mappendProcessParsedAnnotation pn = mapProcessParsedAnnotation (<> pn)

applyProcessParsedAnnotation :: Apply s SapicTerm => s -> ProcessParsedAnnotation -> ProcessParsedAnnotation
applyProcessParsedAnnotation subst ann =
        ann {location = fmap (apply subst) (location ann)
                    -- , backSubstitution = undefined
                    -- WARNING: we do not apply the substitution to the back
                    -- translation, as this is not always possible. If variables
                    -- are renamed, modify the backtranslation by hand.
                    }

applyAnn :: (GoodAnnotation a, Apply t' SapicTerm) => t' -> a -> a
applyAnn subst = mapProcessParsedAnnotation (applyProcessParsedAnnotation subst)

instance (Apply (Subst Name LVar) ProcessParsedAnnotation) where
    apply = applyAnn
