{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Items.AccLemmaItem (
    module Items.AccLemmaItem
) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.List
import Data.Label as L
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
       { _aName            :: String
       , _aAttributes      :: [LemmaAttribute]
       , _aCaseIdentifiers :: [CaseIdentifier]
       , _aCaseTests       :: [CaseTest]
       , _aFormula         :: SyntacticLNFormula
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''AccLemma])

defineCaseTests :: AccLemma -> [CaseTest] -> AccLemma
defineCaseTests accLem caseTests = accLem { _aCaseTests = caseTests }

prettyAccLemmaName :: HighlightDocument d => AccLemma -> d
prettyAccLemmaName l = case L.get aAttributes l of
      [] -> text (L.get aName l)
      as -> text (L.get aName l) <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)

prettyAccLemma :: HighlightDocument d => AccLemma -> d
prettyAccLemma alem =
    kwLemma <-> prettyAccLemmaName alem <> colon $-$
    (nest 2 $
      text (intercalate ", " (L.get aCaseIdentifiers alem)) <-> account $-$
      sep [  doubleQuotes $ prettySyntacticLNFormula $ L.get aFormula alem
          ]
    )
    where
        account | length (L.get aCaseIdentifiers alem) == 1 = text "accounts for"
                | otherwise                                 = text "accounts for"