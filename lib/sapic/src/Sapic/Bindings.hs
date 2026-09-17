module Sapic.Bindings
  ( bindings
  , bindingsAct
  , bindingsComb
  , accBindings
  , capturedVariables
  ) where

import Theory.Sapic
import Data.Map.Strict qualified as M

-- | bindings returns the variables bound precisely at this point. Guarantees that no duplicates are in the list.
bindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
bindings (ProcessComb c ann _ _) = bindingsComb ann c
bindings (ProcessAction ac ann _) = bindingsAct ann ac
bindings (ProcessNull _) = []

-- | bindings for actions without duplicates
bindingsAct :: GoodAnnotation a => a -> SapicAction SapicLVar -> [SapicLVar]
bindingsAct _ = actionBinders

-- | Binders whose scope is the success continuation only.
bindingsComb :: GoodAnnotation a => a -> ProcessCombinator SapicLVar -> [SapicLVar]
bindingsComb _ = combinatorBinders

-- | accumulate all bound variables in a list
accBindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
accBindings = pfoldMap bindings

-- | Detect rebinding in one scoped traversal. Keep the outer source occurrence
-- for diagnostics while comparing type-independent LVar identities. Siblings
-- and let/lookup failure branches retain their incoming binding environment.
capturedVariables :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
capturedVariables = check M.empty
  where
    extend bound vars = foldr (\v -> M.insertWith (\_ original -> original) (toLVar v) v) bound vars
    collisions bound vars = [original | v <- vars, Just original <- [M.lookup (toLVar v) bound]]
    check _ (ProcessNull _) = []
    check bound (ProcessAction ac _ rest) =
      let vars = actionBinders ac
      in collisions bound vars ++ check (extend bound vars) rest
    check bound (ProcessComb comb _ left right) =
      let vars = combinatorBinders comb
      in collisions bound vars ++ check (extend bound vars) left ++ check bound right
