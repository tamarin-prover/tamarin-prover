{-# LANGUAGE ViewPatterns #-} 
-- |
-- Copyright   : (c) 2023 - Thiebaux Valentin
-- License     : GPL v3 (see LICENSE)
--
-- Macro substitution and application

module Term.Macro (
    Macro
    , LNMacro
    , BNMacro
    , applyMacros
    , macroToFunSym
    , lnMacrosToBNMacros
) where

import           Term.Substitution

import qualified Data.ByteString            as B
import           Data.List                  (find)

type Macro c v = (B.ByteString, [v], Term (Lit c v))
-- | Standard type for macros
type LNMacro = Macro Name LVar
-- | Type used to handle macros in formulas
type BNMacro = Macro Name (BVar LVar)

-- | Change a Macro to a FunSym
macroToFunSym :: Macro c v -> FunSym
macroToFunSym (op, args, _) = NoEq (op, (length args, Private, Destructor))      

-- | Apply and substitute a single macro
applyMacro :: IsConst c => IsVar v => FunSym -> [v] -> VTerm c v -> VTerm c v -> VTerm c v
applyMacro mc margs mout (viewTerm -> FApp f targs)
    | mc == f = apply (substFromList $ zip margs (map (applyMacro mc margs mout) targs)) mout
    | otherwise = fApp f $ map (applyMacro mc margs mout) targs
applyMacro _ _ _ t = t

-- | Apply and substitute all the macros
applyMacros :: IsConst c => IsVar v => [Macro c v] -> VTerm c v -> VTerm c v
applyMacros macros term = 
    case viewTerm term of
    FApp f args -> 
        case findMatchingMacro f macros of
            Just (_, margs, mout) -> 
                let processedArgs = map (applyMacros macros) args
                    subst = substFromList $ zip margs processedArgs
                in applyMacros macros (apply subst mout)
            Nothing -> 
                fApp f $ map (applyMacros macros) args
    Lit l -> lit l
  where
    findMatchingMacro :: FunSym -> [Macro c v] -> Maybe (Macro c v)
    findMatchingMacro f = find (\m -> macroToFunSym m == f)

lnMacroToBNMacro :: LNMacro -> BNMacro
lnMacroToBNMacro (op, args, out) = (op, map freeLNTerm args, freeTerm out)

lnMacrosToBNMacros :: [LNMacro] -> [BNMacro]
lnMacrosToBNMacros = map lnMacroToBNMacro