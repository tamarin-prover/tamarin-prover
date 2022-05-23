{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Items.CaseTestItem (
    module Items.CaseTestItem
) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Label as L
import Theory.Model
import Theory.Syntactic.Predicate

------------------------------------------------------------------------------
-- Case Tests
------------------------------------------------------------------------------

type CaseIdentifier = String

data CaseTest = CaseTest 
       { _cName       :: CaseIdentifier
       , _cFormula    :: SyntacticLNFormula
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''CaseTest])

caseTestToPredicate :: CaseTest -> Maybe Predicate
caseTestToPredicate caseTest = fmap (Predicate fact) formula
  where
    fact = protoFact Linear name (frees formula)
    name = L.get cName caseTest
    formula = toLNFormula (L.get cFormula caseTest)
