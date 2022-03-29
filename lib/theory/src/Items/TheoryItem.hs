
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
import Theory.Constraint.Solver.Heuristics
import Data.Label as L
import Theory.Model.Restriction
import Theory.Constraint.Solver

import Items.OptionItem
import Items.ProcessItem
import Items.PredicateItem
import Lemma
import           Prelude                             hiding (id, (.))
import           Control.DeepSeq
import           Prelude                             hiding (id, (.))

------------------------------------------------------------------------------
-- Theories
------------------------------------------------------------------------------

-- | A formal comment is a header together with the body of the comment.

type FormalComment = (String, String)

-- | SapicItems can be processes and accountability lemmas
data SapicElement=
      ProcessItem Process
      | ProcessDefItem ProcessDef
      deriving( Show, Eq, Ord, Generic, NFData, Binary )

-- | A theory item built over the given rule type.
data TheoryItem r p s =
       RuleItem r
     | LemmaItem (Lemma p)
     | RestrictionItem Restriction
     | TextItem FormalComment
     | PredicateItem Predicate
     | SapicItem s
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

-- | A theory contains a single set of rewriting rules modeling a protocol
-- and the lemmas that
data Theory sig c r p s = Theory {
         _thyName      :: String
       , _thyHeuristic :: [GoalRanking]
       , _thySignature :: sig
       , _thyCache     :: c
       , _thyItems     :: [TheoryItem r p s]
       , _thyOptions   :: Option
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''Theory])


-- | A diff theory contains a set of rewriting rules with diff modeling two instances
data DiffTheory sig c r r2 p p2 = DiffTheory {
         _diffThyName           :: String
       , _diffThyHeuristic      :: [GoalRanking]
       , _diffThySignature      :: sig
       , _diffThyCacheLeft      :: c
       , _diffThyCacheRight     :: c
       , _diffThyDiffCacheLeft  :: c
       , _diffThyDiffCacheRight :: c
       , _diffThyItems          :: [DiffTheoryItem r r2 p p2]
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''DiffTheory])


