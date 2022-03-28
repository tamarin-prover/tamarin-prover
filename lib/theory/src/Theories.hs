
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
module Theories (
    LemmaAttribute(..)
  , TraceQuantifier(..)
  , Lemma
  , SyntacticLemma
  , ProtoLemma(..)
  , Theory(..)
  , DiffTheory(..)
  , TheoryItem(..)
  , DiffTheoryItem(..)
  , DiffLemma(..)
  , ProcessDef(..)
  , Predicate(..)
  , Option(..)
  , FormalComment
  , SapicElement (..)
  , lName
  , lTraceQuantifier 
  , lFormula        
  , lAttributes     
  , lProof
  , lDiffName
  , lDiffAttributes
  , lDiffProof
  , pName
  , pBody
  , thyName     
  , thyHeuristic
  , thySignature
  , thyCache    
  , thyItems    
  , thyOptions 
  , pFact           
  , pFormula
  --, transAllowPatternMatchinginLookup   
  --, transProgress            
  --, transReliable            
  --, transReport  
  , diffThyName           
  , diffThyHeuristic      
  , diffThySignature      
  , diffThyCacheLeft      
  , diffThyCacheRight     
  , diffThyDiffCacheLeft  
  , diffThyDiffCacheRight 
  , diffThyItems
  , lemmaSourceKind
  , addLeftLemma
  , addRightLemma
  , module Options
) where

import Theory.Sapic
import GHC.Generics
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Theory.Model (LNFormula)
import Theory.Constraint.Solver.Heuristics
import Theory.Model.Formula (SyntacticLNFormula)
import Data.Label as L
import Theory.Model.Restriction
import Theory.Model.Fact
import Term.LTerm
import Theory.Constraint.Solver

import Options
import Lemmas

------------------------------------------------------------------------------
-- Processes
------------------------------------------------------------------------------

data ProcessDef = ProcessDef
        { _pName            :: String
        , _pBody            :: Process
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''ProcessDef])

-- generate accessors for ProcessDef data structure records


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









