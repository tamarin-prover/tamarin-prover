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

  -- ** The Reduction monad
  -- | This monad manages the state of the implementation of a constraint
  -- reduction rule. This is essentially the list of all constraint systems
  -- resulting from a constraint reduction step.
  , Reduction
  , execReduction
  , runReduction

  -- ** Simplification
  -- | All rules that do not result in case distinctions and equation solving.
  -- Note that a few of these rules are implemented directly in the methods
  -- for inserting constraints to the constraint system. These methods are
  -- provided by "Theory.Constraint.Solver.Reduction".
  , simplifySystem

  -- ** Goals
  -- | A goal represents a possible application of a rule that may result in
  -- multiple cases or even non-termination (if applied repeatedly). These
  -- goals are computed as the list of 'openGoals'. A heuristic is used to
  -- order the goals such that more worthwhile goals are preferred. If this
  -- list is empty, then the constraint system is solved and we can extract a
  -- trace from it. Solving a goal means applying the corresponding constraint
  -- reduction rule.
  , Goal(..)
  , openGoals
  , solveGoal

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

  , solveWithCaseDistinction

  -- * Pretty-printing
  , prettyContradiction

  -- ** Convenience export
  , module Logic.Connectives

  ) where

import           Logic.Connectives
import           Theory.Constraint.Solver.CaseDistinctions
import           Theory.Constraint.Solver.Contradictions
import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.Solver.Simplify
import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System



