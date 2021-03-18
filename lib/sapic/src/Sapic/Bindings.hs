{-# LANGUAGE PatternGuards         #-}
module Sapic.Bindings(
    bindings
,   bindingsAct
,   bindingsComb
,   accBindings
) where

import Theory.Sapic
import Sapic.Annotation
import Data.List
import qualified Data.Set as S

-- | bindings returns the variables bound precisely at this point. Guarantees that no duplicates are in the list.
--   we need the annotations to handle patterns correctly
bindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
bindings (ProcessComb c ann _ _) = bindingsComb ann c
bindings (ProcessAction ac ann _) = bindingsAct ann ac
bindings (ProcessNull _) = []

-- | bindings for actions without duplicates
bindingsAct :: GoodAnnotation a => a -> SapicAction SapicLVar -> [SapicLVar]
bindingsAct  ann ac
    | (New v) <- ac = [v]
    | (ChIn _ t) <- ac = nub (freesSapicTerm t) \\ S.toList (matchVars $ getProcessParsedAnnotation ann)
    | (MSR (l,_,_,_)) <- ac = nub (foldMap freesSapicFact l) \\ S.toList (matchVars $ getProcessParsedAnnotation ann)
    | otherwise = []

-- | bindings for process combinators without duplicates
bindingsComb :: GoodAnnotation a => a -> ProcessCombinator SapicLVar -> [SapicLVar]
bindingsComb ann c
    | (Lookup _ v) <- c = [v]
    | (Let t1 _)   <- c = nub (freesSapicTerm t1) \\  S.toList (matchVars $ getProcessParsedAnnotation ann)
    | otherwise = []

-- | accumulate all bound variables in a list
accBindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
accBindings = pfoldMap bindings
