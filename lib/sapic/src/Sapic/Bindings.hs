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

-- | bindings returns the variables bound precisely at this point.
bindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
bindings (ProcessComb c ann _ _) 
    | (Lookup _ v) <- c = [v]
    | (Let t1 _)   <- c = freesSapicTerm t1 \\  S.toList (matchVars $ getProcessParsedAnnotation ann)
    | otherwise = []
bindings (ProcessAction ac ann _) 
    | (New v) <- ac = [v]
    | (ChIn _ t) <- ac = freesSapicTerm t \\ S.toList (matchVars $ getProcessParsedAnnotation ann)
    | (MSR (l,_,r,_)) <- ac = (foldMap freesSapicFact r) \\ (foldMap freesSapicFact l)
    | otherwise = []
bindings (ProcessNull _) = []

-- | for convenience
bindingsAct :: Monoid ann => ann -> SapicAction v -> Process ann v
bindingsAct  ann ac = (ProcessAction ac ann (ProcessNull mempty))

bindingsComb :: Monoid ann => ann -> ProcessCombinator v -> Process ann v
bindingsComb ann c  = (ProcessComb c ann (ProcessNull mempty) (ProcessNull mempty))

-- | accumulate all bound variables in a list
accBindings :: GoodAnnotation a => Process a SapicLVar -> [SapicLVar]
accBindings p = pfoldMap bindings p
