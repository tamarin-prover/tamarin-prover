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

  -- * Proof contexts
  -- | The proof context captures all relevant information about the context
  -- in which we are using the constraint solver. These are things like the
  -- signature of the message theory, the multiset rewriting rules of the
  -- protocol, the available precomputed case distinctions, whether induction
  -- should be applied or not, whether typed or untyped case distinctions are
  -- used, and whether we are looking for the existence of a trace or proving
  -- the absence of any trace satisfying the constraint system.
  , ProofContext(..)
  , pcSignature
  , pcRules
  , pcCaseDists
  , pcUseInduction
  , pcCaseDistKind
  , pcTraceQuantifier

  , InductionHint(..)

  , ClassifiedRules(..)
  , joinAllRules
  , crProtocol
  , crConstruct
  , crDestruct

  -- * Constraint reduction rules

  -- ** Contradictions
  -- | All rules that reduce a constraint system to the empty set of
  -- constraint systems. The 'Contradiction' datatype stores the information
  -- about the contradiction for later display to the user.
  , Contradiction
  , contradictions

  -- ** Precomputed case distinctions
  -- | For better speed, we precompute case distinctions. This is especially
  -- important for getting rid of all chain constraints before actually
  -- starting to verify security properties.
  , CaseDistinction
  , cdGoal
  , cdCases

  , precomputeCaseDistinctions
  , refineWithTypingAsms
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
import           Theory.Constraint.Solver.CaseDistinctions
import           Theory.Constraint.Solver.Contradictions
import           Theory.Constraint.Solver.ProofMethod
import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System


