{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric        #-}
-- |
-- Copyright   : (c) 2021 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Standard annotations for SAPIC processes after parsing
{-# LANGUAGE FlexibleContexts #-}
module Theory.Sapic.Annotation (
    -- types
      ProcessParsedAnnotation(..)
    -- utilities
    , modifyProcessParsedAnnotation
    -- type classes
    , GoodAnnotation(..)
) where

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
    -- 2. only apply to variables bound at this subprocess
    -- 3. maps variables to variable terms
    , backSubstitution :: SapicSubst
    }
    deriving (Eq, Ord, Show, Data, Generic)
instance NFData ProcessParsedAnnotation
instance Binary ProcessParsedAnnotation

instance Monoid ProcessParsedAnnotation where
    mempty = ProcessParsedAnnotation [] Nothing emptySubst
    mappend p1 p2 = ProcessParsedAnnotation
        (processnames p1 `mappend` processnames  p2)
        (case (location p1, location p2) of
             (Nothing, l2) -> l2
             (l1, Nothing) -> l1
             (_, l2) -> l2)
        (backSubstitution p1 `compose` backSubstitution p2)

instance Semigroup ProcessParsedAnnotation where
    (<>) p1 p2 = p1 `mappend` p2

-- | Any annotation that is good enough to be converted back into a Process
--  can at least recover the names of the processes used to bind
--  subprocesses
-- annotate the multiset rewrite rules with:
--      - the Name or Names of the process (e.g., [A, B] in let B = 0 let A = B | 0)
class GoodAnnotation a where
    getProcessParsedAnnotation :: a ->  ProcessParsedAnnotation
    setProcessParsedAnnotation :: ProcessParsedAnnotation -> a -> a
    defaultAnnotation :: a

instance GoodAnnotation ProcessParsedAnnotation
    where
        getProcessParsedAnnotation = id
        setProcessParsedAnnotation pn _ = pn
        defaultAnnotation   = mempty

modifyProcessParsedAnnotation :: GoodAnnotation a =>
    (ProcessParsedAnnotation -> ProcessParsedAnnotation) -> a -> a
modifyProcessParsedAnnotation f ann =
    setProcessParsedAnnotation (f $ getProcessParsedAnnotation ann) ann

applyProcessParsedAnnotation :: Apply t' SapicTerm => t' -> ProcessParsedAnnotation -> ProcessParsedAnnotation
applyProcessParsedAnnotation subst ann = 
        ann {location = fmap (apply subst) (location ann)
                    -- , backSubstitution = undefined 
                    -- WARNING: we do not apply the substitution to the back
                    -- translation, as this is not always possible. If variables
                    -- are renamed, modify the backtranslation by hand.
                    }

instance {-# INCOHERENT #-} (GoodAnnotation a) => Apply SapicSubst a
-- INCOHERENT ensures that this instance is selected if other candidates remain (barring knowledge about the context
-- see https://ghc.readthedocs.io/en/8.0.1/glasgow_exts.html?highlight=incoherentinstances#instance-overlap)
    where
        apply subst ann = 
            let ann' = applyProcessParsedAnnotation subst $ getProcessParsedAnnotation ann
            in
            setProcessParsedAnnotation ann' ann
