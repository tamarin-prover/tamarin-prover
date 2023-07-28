{-# LANGUAGE ViewPatterns #-} 
-- |
-- Copyright   : (c) 2023 - Thiebaux Valentin
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Macro substitution and application

module Term.Macro (
    Macro
    , applyMacros
) where

import           Term.Maude.Process
import           Term.Substitution
import           Term.SubtermRule
import           Term.Positions
import           Term.LTerm

import qualified Data.ByteString            as B

type Macro = (B.ByteString, [LVar], Term (Lit Name LVar))

-- | Change a Macro to a FunSym
macroToFunSym :: Macro -> FunSym
macroToFunSym (op, args, _) = NoEq (op, (length args, Private, Destructor))      

-- | Apply and substitute the macro on a LNTerm
applyMacro :: FunSym -> [LVar] -> LNTerm -> LNTerm -> LNTerm
applyMacro mc margs mout t@(viewTerm -> FApp f targs)
    | mc == f = apply (substFromList $ zip margs (map (applyMacro mc margs mout) targs)) mout
    | otherwise = fApp f $ map (applyMacro mc margs mout) targs
applyMacro _ _ _ t = t

switchApplyMacro :: LNTerm -> Macro -> LNTerm
switchApplyMacro t (op, args, out) = applyMacro (macroToFunSym (op, args, out)) args out t 

-- | Apply and substitute all the macros on a LNTerm
applyMacros :: [Macro] -> LNTerm -> LNTerm
applyMacros [] t     = t
applyMacros [m] t    = switchApplyMacro t m
applyMacros (m:ms) t = switchApplyMacro (applyMacros ms t) m