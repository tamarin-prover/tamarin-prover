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
module Theory.Sapic.Annotation (
    -- types
      ProcessParsedAnnotation(..)
    , PlainProcess
    -- utilities
    , paddAnn
) where

import Data.Binary
import Data.Data
import qualified Data.Set as S
import GHC.Generics (Generic)
import Control.Parallel.Strategies
import Theory.Sapic.Term
import Theory.Sapic.Process

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

type PlainProcess = LProcess ProcessParsedAnnotation

-- | Add another element to the existing annotations, e.g., yet another identifier.
paddAnn :: PlainProcess -> ProcessParsedAnnotation -> PlainProcess
paddAnn (ProcessNull ann) ann' = ProcessNull $ ann `mappend` ann'
paddAnn (ProcessComb c ann pl pr ) ann' = ProcessComb c (ann `mappend` ann')  pl pr
paddAnn (ProcessAction a ann p ) ann' = ProcessAction a (ann `mappend` ann')  p
