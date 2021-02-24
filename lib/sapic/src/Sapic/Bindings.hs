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

-- | bindings returns the variables bound precisely at this point. Guarantees uniqueness of the list.
--   we need the annotations to handle patterns correctly   
bindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
bindings (ProcessComb c ann _ _) = bindingsComb ann c
bindings (ProcessAction ac ann _) = bindingsAct ann ac
bindings (ProcessNull _) = []

-- | for convenience
bindingsAct :: GoodAnnotation a => a -> SapicAction SapicLVar -> [SapicLVar]
bindingsAct  ann ac
    | (New v) <- ac = [v]
    | (ChIn _ t) <- ac = nub (freesSapicTerm t) \\ S.toList (matchVars $ getProcessParsedAnnotation ann)
    | (MSR (l,_,r,_)) <- ac = nub (foldMap freesSapicFact r) \\ foldMap freesSapicFact l
    | otherwise = []

bindingsComb :: GoodAnnotation a => a -> ProcessCombinator SapicLVar -> [SapicLVar]
bindingsComb ann c
    | (Lookup _ v) <- c = [v]
    | (Let t1 _)   <- c = nub (freesSapicTerm t1) \\  S.toList (matchVars $ getProcessParsedAnnotation ann)
    | otherwise = []

-- | accumulate all bound variables in a list
accBindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
accBindings = pfoldMap bindings
