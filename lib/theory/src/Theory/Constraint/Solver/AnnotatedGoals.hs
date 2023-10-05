-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Exporting the object AnnotatedGoal to make it accessible by Heuristic.hs and Signature.hs

module Theory.Constraint.Solver.AnnotatedGoals
  ( Usefulness(..)
  , AnnotatedGoal
  )
where

import Theory.Constraint.System.Constraints

data Usefulness =
    Useful
  -- ^ A goal that is likely to result in progress.
  | LoopBreaker
  -- ^ A goal that is delayed to avoid immediate termination.
  | ProbablyConstructible
  -- ^ A goal that is likely to be constructible by the adversary.
  | CurrentlyDeducible
  -- ^ A message that is deducible for the current solution.
  deriving (Show, Eq, Ord)

-- | Goals annotated with their number and usefulness.
type AnnotatedGoal = (Goal, (Integer, Usefulness))