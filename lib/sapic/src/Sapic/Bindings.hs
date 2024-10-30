module Sapic.Bindings
  ( bindings
  , bindingsAct
  , bindingsComb
  , accBindings
  , capturedVariables
  ) where

import Theory.Sapic
import Data.List
import Data.Set qualified as S

-- | bindings returns the variables bound precisely at this point. Guarantees that no duplicates are in the list.
--   we need the annotations to handle patterns correctly
bindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
bindings (ProcessComb c ann _ _) = bindingsComb ann c
bindings (ProcessAction ac ann _) = bindingsAct ann ac
bindings (ProcessNull _) = []

-- | bindings for actions without duplicates
bindingsAct :: GoodAnnotation a => a -> SapicAction SapicLVar -> [SapicLVar]
bindingsAct  _ ac
    | (New v) <- ac = [v]
    | (ChIn _ t vs) <- ac = nub (freesSapicTerm t) \\ S.toList vs
    | (MSR l _ _ _ mv) <- ac = nub (foldMap freesSapicFact l) \\ S.toList mv
    | otherwise = []

-- | bindings for process combinators without duplicates
bindingsComb :: GoodAnnotation a => a -> ProcessCombinator SapicLVar -> [SapicLVar]
bindingsComb _ c
    | (Lookup _ v) <- c = [v]
    | (Let t1 _ mv)   <- c = nub (freesSapicTerm t1) \\  S.toList mv
    | otherwise = []

-- | accumulate all bound variables in a list
accBindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
accBindings = pfoldMap bindings

-- | Find out which variables or names bound in the subprocess are captured *by the current process*
capturedVariablesAt :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
capturedVariablesAt (ProcessAction ac ann p)  = bindingsAct ann ac `intersect` accBindings p
capturedVariablesAt (ProcessComb c ann pl pr) = bindingsComb ann c `intersect` (accBindings pl `union` accBindings pr)
capturedVariablesAt (ProcessNull _) = []

-- | List all variables or names captured somewhere in theprocess
capturedVariables :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
capturedVariables = pfoldMap capturedVariablesAt
