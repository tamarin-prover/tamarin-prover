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
import qualified Data.Set as S
import GHC.Generics (Generic)
import Control.Parallel.Strategies
import Theory.Sapic.Term

-- | After parsing, the process is already annotated wth a list of process
--   identifiers. Any identifier in this in this list was inlined to give this
--   comment, e.g.,
--    let A = 0
--    let B = A | A
--    !B
--    has two Null-rules with annotation [A,B].
--  This will be helpful to recognise protocols roles and visualise them.

data ProcessParsedAnnotation = ProcessParsedAnnotation
    { processnames      :: [String]
    -- String used in annotation to identify processes. Always a singleton list
    , location       :: Maybe SapicTerm
    -- additional information for Isolated Execution Environments feature
    , matchVars :: S.Set SapicLVar
    -- Variables in in() or let-actions that are intended to match already bound variables
    }
    deriving (Eq, Ord, Show, Data, Generic)
instance NFData ProcessParsedAnnotation
instance Binary ProcessParsedAnnotation

instance Monoid ProcessParsedAnnotation where
    mempty = ProcessParsedAnnotation [] Nothing S.empty
    mappend p1 p2 = ProcessParsedAnnotation
        (processnames p1 `mappend` processnames  p2)
        (case (location p1, location p2) of
             (Nothing, l2) -> l2
             (l1, Nothing) -> l1
             (_, l2) -> l2)
        (matchVars p1 `mappend` matchVars p2)

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

modifyProcessParsedAnnotation :: (GoodAnnotation a1, GoodAnnotation a2) =>
    ((a2 -> ProcessParsedAnnotation) -> a1 -> ProcessParsedAnnotation)
    -> a1 -> a1
modifyProcessParsedAnnotation f ann =
    setProcessParsedAnnotation (f getProcessParsedAnnotation ann) ann
