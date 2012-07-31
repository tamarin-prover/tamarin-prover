{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
  -- for ByteString
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Term Algebra and related notions.
module Term.Term (

    -- ** Pretty printing and query functions.
      prettyTerm
    , showFunSymName
    , lits

    -- ** Smart constructors
    , fAppOne
    , fAppExp
    , fAppInv
    , fAppPMult
    , fAppEMap
    , fAppPair
    , fAppFst
    , fAppSnd

    -- ** Destructors and classifiers
    , isPair
    , isInverse
    , isProduct
    , isUnion
    , isEMap
    , isNullaryFunction

    -- * AC, C, and NonAC funcion symbols
    , FunSym(..)
    , ACSym(..)
    , CSym(..)
    , NoEqSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , expSymString
    , invSymString
    , pmultSymString
    , emapSymString
    , unionSymString
    
    -- ** Function symbols
    , expSym
    , pmultSym

    -- ** concrete signatures
    , dhFunSig
    , bpFunSig
    , msetFunSig
    , pairFunSig
    , dhReducibleFunSig
    , bpReducibleFunSig
    , implicitFunSig

    , module Term.Term.Classes
    , module Term.Term.Raw

    ) where

import           Data.Monoid
import           Data.Foldable (Foldable, foldMap)

import qualified Data.ByteString.Char8 as BC
import           Extension.Data.ByteString ()


import           Text.PrettyPrint.Class
import           Term.Term.Classes
import           Term.Term.FunctionSymbols
import           Term.Term.Raw

----------------------------------------------------------------------
-- Smart Constructors
----------------------------------------------------------------------

-- | Smart constructors for one, zero.
fAppOne :: Term a
fAppOne = fAppNoEq oneSym []

-- | Smart constructors for pair, exp, pmult, and emap.
fAppPair, fAppExp,fAppPMult, fAppEMap :: Ord a => (Term a, Term a) -> Term a
fAppPair (x,y)  = fAppNoEq pairSym  [x, y]
fAppExp  (b,e)  = fAppNoEq expSym   [b, e]
fAppPMult (s,p) = fAppNoEq pmultSym [s, p]
fAppEMap  (x,y) = fAppC    EMap     [x, y]

-- | Smart constructors for inv, fst, and snd.
fAppInv, fAppFst, fAppSnd :: Term a -> Term a
fAppInv e = fAppNoEq invSym [e]
fAppFst a = fAppNoEq fstSym [a]
fAppSnd a = fAppNoEq sndSym [a]

-- | @lits t@ returns all literals that occur in term @t@. List can contain duplicates.
lits :: Ord a => Term a -> [a]
lits = foldMap return

----------------------------------------------------------------------
-- Classifiers
----------------------------------------------------------------------

-- | 'True' iff the term is a well-formed pair.
isPair :: Show a => Term a -> Bool
isPair (viewTerm2 -> FPair _ _) = True
isPair _                        = False

-- | 'True' iff the term is a well-formed inverse.
isInverse :: Show a => Term a -> Bool
isInverse (viewTerm2 -> FInv _) = True
isInverse _                     = False

-- | 'True' iff the term is a well-formed product.
isProduct :: Show a => Term a -> Bool
isProduct (viewTerm2 -> FMult _) = True
isProduct _                      = False

-- | 'True' iff the term is a well-formed emap.
isEMap :: Show a => Term a -> Bool
isEMap (viewTerm2 -> FEMap _ _) = True
isEMap _                        = False

-- | 'True' iff the term is a well-formed union.
isUnion :: Show a => Term a -> Bool
isUnion (viewTerm2 -> FUnion _) = True
isUnion _                       = False

-- | 'True' iff the term is a nullary, public function.
isNullaryFunction :: Term a -> Bool
isNullaryFunction (viewTerm -> FApp (NoEq (_, 0)) _) = True
isNullaryFunction _                                  = False

----------------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------------

-- | Convert a function symbol to its name.
showFunSymName :: FunSym -> String
showFunSymName (NoEq (bs, _)) = BC.unpack bs
showFunSymName (AC op)        = show op
showFunSymName (C op )        = show op
showFunSymName List           = "List"

-- | Pretty print a term.
prettyTerm :: (Document d, Show l) => (l -> d) -> Term l -> d
prettyTerm ppLit = ppTerm
  where
    ppTerm t = case viewTerm t of
        Lit l                                       -> ppLit l
        FApp (AC o)        ts                       -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)     [t1,t2]   | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)     _         | s == pairSym -> ppTerms ", " 1 "<" ">" (split t)
        FApp (NoEq (f,_)) ts                       -> ppFun f ts
        FApp (C EMap)      ts                       -> ppFun emapSymString ts
        FApp List          ts                       -> ppFun "LIST" ts

    ppACOp Mult  = "*"
    ppACOp Union = "+"

    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts

    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split t                          = [t]

    ppFun f ts =
        text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
