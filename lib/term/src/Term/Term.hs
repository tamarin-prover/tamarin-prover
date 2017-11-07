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
    , fAppDiff
    , fAppExp
    , fAppInv
    , fAppPMult
    , fAppEMap
    , fAppPair
    , fAppFst
    , fAppSnd

    -- ** Destructors and classifiers
    , isPair
    , isDiff
    , isInverse
    , isProduct
    , isUnion
    , isEMap
    , isNullaryPublicFunction
    , isPrivateFunction
    , getLeftTerm
    , getRightTerm

    -- * AC, C, and NonAC funcion symbols
    , FunSym(..)
    , ACSym(..)
    , CSym(..)
    , Privacy(..)
    , NoEqSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , diffSymString
    , expSymString
    , invSymString
    , pmultSymString
    , emapSymString
    , unionSymString
    , oneSymString
    , multSymString
    
    -- ** Function symbols
    , diffSym
    , expSym
    , pmultSym
    , oneSym

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
-- import           Data.Foldable (foldMap)

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

-- | Smart constructors for diff, pair, exp, pmult, and emap.
fAppDiff, fAppPair, fAppExp,fAppPMult :: (Term a, Term a) -> Term a
fAppDiff (x,y)  = fAppNoEq diffSym  [x, y]
fAppPair (x,y)  = fAppNoEq pairSym  [x, y]
fAppExp  (b,e)  = fAppNoEq expSym   [b, e]
fAppPMult (s,p) = fAppNoEq pmultSym [s, p]
fAppEMap :: Ord a => (Term a, Term a) -> Term a
fAppEMap  (x,y) = fAppC    EMap     [x, y]

-- | Smart constructors for inv, fst, and snd.
fAppInv, fAppFst, fAppSnd :: Term a -> Term a
fAppInv e = fAppNoEq invSym [e]
fAppFst a = fAppNoEq fstSym [a]
fAppSnd a = fAppNoEq sndSym [a]

-- | @lits t@ returns all literals that occur in term @t@. List can contain duplicates.
lits :: Term a -> [a]
lits = foldMap return

----------------------------------------------------------------------
-- Classifiers
----------------------------------------------------------------------

-- | 'True' iff the term is a well-formed pair.
isPair :: Show a => Term a -> Bool
isPair (viewTerm2 -> FPair _ _) = True
isPair _                        = False

-- | 'True' iff the term is a well-formed diff term.
isDiff :: Show a => Term a -> Bool
isDiff (viewTerm2 -> FDiff _ _) = True
isDiff _                        = False

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
isNullaryPublicFunction :: Term a -> Bool
isNullaryPublicFunction (viewTerm -> FApp (NoEq (_, (0, Public))) _) = True
isNullaryPublicFunction _                                            = False

isPrivateFunction :: Term a -> Bool
isPrivateFunction (viewTerm -> FApp (NoEq (_, (_,Private))) _) = True
isPrivateFunction _                                            = False

----------------------------------------------------------------------
-- Convert Diff Terms
----------------------------------------------------------------------

getSide :: DiffType -> Term a -> Term a
getSide _  (LIT l) = LIT l
getSide dt (FAPP (NoEq o) [t1,t2]) = case dt of
    DiffLeft  | o == diffSym -> getSide dt t1
    DiffRight | o == diffSym -> getSide dt t2
    DiffBoth  | o == diffSym -> FAPP (NoEq o) [(getSide dt t1),(getSide dt t2)]
    DiffNone  | o == diffSym -> error $ "getSide: illegal use of diff"
    _                        -> FAPP (NoEq o) [(getSide dt t1),(getSide dt t2)]
getSide dt (FAPP sym ts) = FAPP sym (map (getSide dt) ts)

getLeftTerm :: Term a -> Term a
getLeftTerm t = getSide DiffLeft t

getRightTerm :: Term a -> Term a
getRightTerm t = getSide DiffRight t

----------------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------------

-- | Convert a function symbol to its name.
showFunSymName :: FunSym -> String
showFunSymName (NoEq (bs, _)) = BC.unpack bs
showFunSymName (AC op)        = show op
showFunSymName (C op )           = show op
showFunSymName List              = "List"

-- | Pretty print a term.
prettyTerm :: (Document d, Show l) => (l -> d) -> Term l -> d
prettyTerm ppLit = ppTerm
  where
    ppTerm t = case viewTerm t of
        Lit l                                     -> ppLit l
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)      _       | s == pairSym -> ppTerms ", " 1 "<" ">" (split t)
        FApp (NoEq (f, _)) []                     -> text (BC.unpack f)
        FApp (NoEq (f, _)) ts                     -> ppFun f ts
        FApp (C EMap)      ts                     -> ppFun emapSymString ts
        FApp List          ts                     -> ppFun "LIST" ts

    ppACOp Mult  = "*"
    ppACOp Union = "+"

    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts

    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split t                          = [t]

    ppFun f ts =
        text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
