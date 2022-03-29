
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
module Items.PredicateItem (
    module Items.PredicateItem
) where

import Control.DeepSeq
import Data.Binary (Binary)
import Data.Label as L
import GHC.Generics
import Term.LTerm
import Theory.Model
import Prelude hiding (id, (.))


------------------------------------------------------------------------------
-- Predicates
------------------------------------------------------------------------------

data Predicate = Predicate
        { _pFact            :: Fact LVar
        , _pFormula         :: LNFormula
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''Predicate])

-- generate accessors for Predicate data structure records