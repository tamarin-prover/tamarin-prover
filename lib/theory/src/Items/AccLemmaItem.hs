{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Items.AccLemmaItem (
    module Items.AccLemmaItem
) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.List
import Optics.TH (makeFieldLabelsNoPrefix)
import Text.PrettyPrint.Highlight
import Theory.Text.Pretty
import Theory.Model
import Lemma
import Items.CaseTestItem

------------------------------------------------------------------------------
-- Accountability Lemmas
------------------------------------------------------------------------------

-- | An accountability lemma describes an accountability property that holds in the context of a theory
data AccLemma = AccLemma
       { name            :: String
       , attributes      :: [LemmaAttribute]
       , caseIdentifiers :: [CaseIdentifier]
       , caseTests       :: [CaseTest]
       , formula         :: SyntacticLNFormula
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

makeFieldLabelsNoPrefix ''AccLemma

defineCaseTests :: AccLemma -> [CaseTest] -> AccLemma
defineCaseTests accLem caseTests = accLem { caseTests = caseTests }

prettyAccLemmaName :: HighlightDocument d => AccLemma -> d
prettyAccLemmaName l = case l.attributes of
      [] -> text l.name
      as -> text l.name <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)

prettyAccLemma :: HighlightDocument d => AccLemma -> d
prettyAccLemma alem =
    kwLemma <-> prettyAccLemmaName alem <> colon $-$
    (nest 2 $
      text (intercalate ", " alem.caseIdentifiers) <-> account $-$
      sep [  doubleQuotes $ prettySyntacticLNFormula alem.formula
          ]
    )
    where
        account | length alem.caseIdentifiers == 1 = text "accounts for"
                | otherwise                         = text "accounts for"
