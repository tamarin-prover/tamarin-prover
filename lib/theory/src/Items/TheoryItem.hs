
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module Items.TheoryItem (
    module Items.TheoryItem
) where 

import Theory.Sapic
import GHC.Generics
import Data.Binary (Binary)
import Theory.Model.Restriction
import Theory.Constraint.Solver

import Items.ProcessItem
import Items.PredicateItem
import Items.CaseTestItem
import Items.AccLemmaItem
import Lemma
import           Prelude                             hiding (id, (.))
import           Control.DeepSeq
import           Prelude                             hiding (id, (.))

------------------------------------------------------------------------------
-- Theories
------------------------------------------------------------------------------

-- | A formal comment is a header together with the body of the comment.

type FormalComment = (String, String)

-- | TranslationItems can be processes, accountability lemmas, and case tests
data TranslationElement =
        ProcessItem Process
      | ProcessDefItem ProcessDef
      | AccLemmaItem AccLemma
      | CaseTestItem CaseTest
      deriving( Show, Eq, Ord, Generic, NFData, Binary )

-- | A theory item built over the given rule type.
data TheoryItem r p s =
       RuleItem r
     | LemmaItem (Lemma p)
     | RestrictionItem Restriction
     | TextItem FormalComment
     | PredicateItem Predicate
     | TranslationItem s
     deriving( Show, Eq, Ord, Functor, Generic, NFData, Binary )

-- | A diff theory item built over the given rule type.
--   This includes
--   - Diff Rules, which are then decomposed in either rules for both sides
--   - the Diff Lemmas, stating observational equivalence
--   - the either lemmas and restrictions, stating properties about either side
--   - and comments
data DiffTheoryItem r r2 p p2 =
       DiffRuleItem r
     | EitherRuleItem (Side, r2)
     | DiffLemmaItem (DiffLemma p)
     | EitherLemmaItem (Side, Lemma p2)
     | EitherRestrictionItem (Side, Restriction)
     | DiffTextItem FormalComment
     deriving( Show, Eq, Ord, Functor, Generic, NFData, Binary )



