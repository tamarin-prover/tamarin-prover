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
import Data.Label as L
import Text.PrettyPrint.Highlight
import Theory.Text.Pretty
import Theory.Constraint.Solver
import Theory.Model

import Items.CaseTestItem
import Items.LemmaItem

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
  where
    prettyLemmaAttribute SourceLemma        = text "sources"
    prettyLemmaAttribute ReuseLemma         = text "reuse"
    prettyLemmaAttribute InvariantLemma     = text "use_induction"
    prettyLemmaAttribute (HideLemma s)      = text ("hide_lemma=" ++ s)
    prettyLemmaAttribute (LemmaHeuristic h) = text ("heuristic=" ++ (prettyGoalRankings h))
    prettyLemmaAttribute LHSLemma           = text "left"
    prettyLemmaAttribute RHSLemma           = text "right"

prettyAccLemma :: HighlightDocument d => AccLemma -> d
prettyAccLemma alem =
    kwLemma <-> prettyAccLemmaName alem <> colon $-$
    (nest 2 $
      sep [  doubleQuotes $ prettySyntacticLNFormula $ L.get aFormula alem
          ]
    )