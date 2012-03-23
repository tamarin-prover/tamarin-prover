{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveDataTypeable, ViewPatterns #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Term Algebra and related notions.
module Term.Term (
    -- * Signatures and function symbols
      FunSym(..)
    , ACSym(..)
    , NonACSym
    , expSym
    , pairSym
    , invSym
    , oneSym
    , emptySym
    , zeroSym
    , FunSig


    -- * Terms
    , Term
    , TermView (..)
    , viewTerm

    , traverseTerm
    , fmapTerm
    , bindTerm
    , lits
    , prettyTerm
    
    -- ** Smart constructors
    , lit
    , fApp
    , fAppAC
    , fAppNonAC
    , fAppList
    , unsafefApp
    , listToTerm

    -- ** Destrutors
    , destPair
    , destInv

    , module Term.Classes
    ) where

import Data.List
import Data.Monoid
import Data.Foldable (Foldable, foldMap)
import Data.Traversable
import Data.Typeable
import Data.Generics
import Data.DeriveTH
import Data.Binary

import Control.DeepSeq
import Control.Basics

import Text.Isar

import Term.Classes

----------------------------------------------------------------------
-- AC operators for terms
----------------------------------------------------------------------

-- | AC function symbols.
data ACSym = MUn | Xor | Mult
  deriving (Eq, Ord, Typeable, Data, Show)

-- | non-AC function symbols
type NonACSym = (String, Int)

-- | Function symbols
data FunSym = NonAC NonACSym  -- ^ a non-AC function function symbol of a given arity
            | AC    ACSym     -- ^ an AC function symbol, can be used n-ary
            | List            -- ^ a non-AC n-ary function symbol of TOP sort
  deriving (Eq, Ord, Typeable, Data, Show)

-- | Function signatures.
type FunSig = [NonACSym]



pairSym, expSym, invSym, oneSym, zeroSym, emptySym :: NonACSym
-- | Pairing.
pairSym  = ("pair",2)
-- | Exponentiation.
expSym   = ("exp",2)
-- | The inverse in the groups of exponents.
invSym   = ("inv",1) 
-- | The one in the group of exponents.
oneSym   = ("one", 0)
-- | The zero for Xor.
zeroSym  = ("zero",0)
-- | The empty multiset.
emptySym = ("empty",0)

----------------------------------------------------------------------
-- Terms
----------------------------------------------------------------------

-- | A term in T(Sigma,a).
data Term a = LIT a                 -- ^ atomic terms (constants, variables, ..)
            | FAPP FunSym [Term a]  -- ^ function applications
  deriving (Eq, Ord, Typeable, Data )

-- | Destruct a top-level function application.
{-# INLINE destFunApp #-}
destFunApp :: FunSym -> Term a -> Maybe [Term a]
destFunApp fsym (FAPP fsym' args) | fsym == fsym' = Just args
destFunApp _    _                                = Nothing

-- | Destruct a top-level pair.
destPair :: Term a -> Maybe (Term a, Term a)
destPair t = do [t1, t2] <- destFunApp (NonAC pairSym) t; return (t1, t2)

-- | Destruct a top-level inverse in the group of exponents.
destInv :: Term a -> Maybe (Term a)
destInv t = do [t1] <- destFunApp (NonAC invSym) t; return t1

data TermView a = Lit a
                | FApp FunSym [Term a]
  deriving (Show, Eq, Ord)

{-# INLINE viewTerm #-}
viewTerm :: Term a -> TermView a
viewTerm (LIT l) = Lit l
viewTerm (FAPP sym ts) = FApp sym ts

-- | @fApp fsym as@ creates an application of @fsym@ to @as@. The function
-- ensures that the resulting term is in AC-normal-form.
fApp :: Ord a => FunSym -> [Term a] -> Term a
fApp   (AC _) []  = error "Term.fApp: empty argument list"
fApp   (AC _) [a] = a
fApp o@(AC _) as  =
    FAPP o (sort (o_as ++ non_o_as))
  where
    isOTerm (FAPP o' _) | o' == o = True
    isOTerm _                                 = False
    (o_as0, non_o_as) = partition isOTerm as
    o_as              = [ a | FAPP _ ts <- o_as0, a <- ts ]
fApp o ts = FAPP o ts

fAppAC :: Ord a => ACSym -> [Term a] -> Term a
fAppAC acsym = fApp (AC acsym)

{-# INLINE fAppNonAC #-}
fAppNonAC :: NonACSym -> [Term a] -> Term a
fAppNonAC nacsym = FAPP (NonAC nacsym)

{-# INLINE fAppList #-}
fAppList :: [Term a] -> Term a
fAppList = FAPP List

-- | @lit l@ create a term from the literal @l@.
{-# INLINE lit #-}
lit :: a -> Term a
lit l = LIT l

-- | @unsafefApp fsym as@ creates an application of @fsym@ to as. The
--   caller has to ensure that the resulting term is in AC-normal-form.
unsafefApp :: FunSym -> [Term a] -> Term a
unsafefApp fsym as = FAPP fsym as

-- Instances
------------

{-# INLINE traverseTerm #-}
traverseTerm :: (Applicative f, Ord a, Ord b) => (a -> f b) -> Term a -> f (Term b)
traverseTerm f (LIT x)         = LIT <$> f x
traverseTerm f (FAPP fsym  as) = fApp fsym <$> traverse (traverseTerm f) as

{-# INLINE fmapTerm #-}
fmapTerm :: (Ord a, Ord b) => (a -> b) -> Term a -> Term b
fmapTerm f = foldTerm (lit . f) fApp

{-# INLINE bindTerm #-}
bindTerm :: (Ord a, Ord b) => Term a -> (a -> Term b) -> Term b
bindTerm m f = foldTerm f fApp m

instance Foldable Term where
    {-# INLINE foldMap #-}
    foldMap f = foldTerm f (const mconcat)

instance Show a => Show (Term a) where
    show (LIT l)                  = show l
    show (FAPP   (NonAC (s,_)) []) = s
    show (FAPP   (NonAC (s,_)) as) = s++"("++(intercalate "," (map show as))++")"
    show (FAPP   List as)          = "LIST"++"("++(intercalate "," (map show as))++")"
    show (FAPP   (AC o) as)        = show o++"("++(intercalate "," (map show as))++")"



-- | The fold function for @Term a@.
{-# INLINE foldTerm #-}
foldTerm :: (t -> b) -> (FunSym -> [b] -> b)
         -> Term t -> b
foldTerm fLIT fFAPP t = go t
  where go (LIT a)       = fLIT a
        go (FAPP fsym a) = fFAPP fsym $ map go a


instance Sized a => Sized (Term a) where
    size = foldTerm size (const $ \xs -> sum xs + 1)

-- | @lits t@ returns all literals that occur in term @t@. List can contain duplicates.
lits :: Ord a => Term a -> [a]
lits = foldMap return

-- | @listToTerm ts@ returns a term that represents @ts@.
listToTerm :: [Term a] -> Term a
listToTerm ts = FAPP List ts

----------------------------------------------------------------------
-- Positions
----------------------------------------------------------------------

-- | Takes flattened AC operators into account, i.e., @*[t1,t2,..,tk]@ is
-- interpreted as @t1*(t2*(..(tk-1*tk)..)@.
-- atPos :: Term a -> Term a


----------------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------------

-- | Pretty print a term.
prettyTerm :: Document d => (l -> d) -> Term l -> d
prettyTerm ppLit = ppTerm
  where
    ppTerm t = case t of
        LIT l                           -> ppLit l
        FAPP (AC o)             ts      -> ppTerms (ppACOp o) 1 "(" ")" ts
        FAPP (NonAC ("exp",2))  [t1,t2] -> ppTerm t1 <> text "^" <> ppTerm t2
        FAPP (NonAC ("pair",2)) _       -> ppTerms ", " 1 "<" ">" (split t)
        FAPP (NonAC (f,_))      ts      -> ppFun f ts
        FAPP List               ts      -> ppFun "LIST" ts

    ppACOp Mult = "*"
    ppACOp MUn  = "#"
    ppACOp Xor  = "+"

    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) . 
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts

    split (FAPP (NonAC ("pair",2)) [t1,t2]) = t1 : split t2
    split t                                 = [t]

    ppFun f ts =
        text (f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"

-- Derived instances
--------------------

$( derive makeNFData ''FunSym)
$( derive makeNFData ''ACSym)
$( derive makeNFData ''Term )

$( derive makeBinary ''FunSym)
$( derive makeBinary ''ACSym)
$( derive makeBinary ''Term )


