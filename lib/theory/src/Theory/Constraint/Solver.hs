-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- The public interface of the constraint solver, which implements all
-- constraint reduction rules and together with a rule application heuristic.
module Theory.Constraint.Solver (

  -- * Constraint systems
    module Theory.Constraint.System

--   , ProofContext(..)
--   , DiffProofContext(..)
--   , pcSignature
--   , pcRules
--   , pcSources
--   , pcUseInduction
--   , pcSourceKind
--   , pcTraceQuantifier
--   , pcInjectiveFactInsts
-- 
--   , InductionHint(..)
-- 
--   , ClassifiedRules(..)
--   , joinAllRules
--   , crProtocol
--   , crConstruct
--   , crDestruct

  -- * Constraint reduction rules

  -- ** Contradictions
  -- | All rules that reduce a constraint system to the empty set of
  -- constraint systems. The 'Contradiction' datatype stores the information
  -- about the contradiction for later display to the user.
  , Contradiction
  , contradictions

--   , Source
--   , cdGoal
--   , cdCases

  , precomputeSources
  , refineWithSourceAsms
  , unsolvedChainConstraints

  -- * Proof methods
  -- | Proof methods are the external to the constraint solver. They allow its
  -- small step execution. This module also provides the heuristics for
  -- selecting the best proof method to apply to a constraint system.
  , module Theory.Constraint.Solver.ProofMethod

  -- ** Convenience export
  , module Logic.Connectives

  ) where

import           Logic.Connectives
import           Theory.Constraint.Solver.Sources
import           Theory.Constraint.Solver.Contradictions
import           Theory.Constraint.Solver.ProofMethod
-- import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System


