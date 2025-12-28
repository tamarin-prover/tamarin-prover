{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Items.CaseTestItem (
    module Items.CaseTestItem
) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Optics.TH (makeFieldLabelsNoPrefix)
import Theory.Model
import Theory.Syntactic.Predicate
import Text.PrettyPrint.Highlight (HighlightDocument, Document (nest, (<->), ($-$), text, sep), colon, doubleQuotes)

------------------------------------------------------------------------------
-- Case Tests
------------------------------------------------------------------------------

type CaseIdentifier = String

data CaseTest = CaseTest
       { name       :: CaseIdentifier
       , formula    :: SyntacticLNFormula
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

makeFieldLabelsNoPrefix ''CaseTest

caseTestToPredicate :: CaseTest -> Maybe Predicate
caseTestToPredicate caseTest = fmap (mkPredicate name) formula
  where
    name = caseTest.name
    formula = toLNFormula caseTest.formula

prettyCaseTest :: HighlightDocument d => CaseTest -> d
prettyCaseTest caseTest =
    text "test" <-> text caseTest.name <> colon $-$
    (nest 2 $
      sep [  doubleQuotes $ prettySyntacticLNFormula caseTest.formula
          ]
    )
