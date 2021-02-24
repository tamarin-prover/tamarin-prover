module Sapic.Bindings(
    bindings
) where

import Theory
import Theory.Sapic
import Data.List

-- | bindings returns the variables bound precisely at this point.
bindings (ProcessComb c ann pl pr) 
    | c <- (Lookup _ v) = [v]
    | c <- (Let t1 _) = freeSapicTerms t1 `
  let new_acc = acc ++ bindingsComb c acc in
    bindings pl new_acc ++ bindings pr new_acc

bindings (ProcessAction ac _ p) acc =
  let new_acc = acc ++ bindingsAct ac acc in
    bindings p new_acc
bindings (ProcessNull _) acc = [acc]

bindingsComb 
  case viewTerm t1 of
    Lit (Var v) -> [v]   -- if we are in a single variable let declaration, we return the variable v
    _ -> let v = freesSapicTerm t1 in -- else, we have a pattern matching, and return the difference with currently bound variables.
      -- TODO, if we actually have an explicit = appearing in the pattern matching, we should check that there is no double variable bindings
      v 
bindingsComb _  _           = []

-- | Note that inputs can contain matched variables, which are contained in this
-- functions output and need to be removed using the annotation.
bindingsAct (New v) = [v]
bindingsAct (ChIn _ t) = freesSapicTerm t 
bindingsAct _       _ = []
