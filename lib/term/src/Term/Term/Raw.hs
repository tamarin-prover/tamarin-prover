{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Term Algebra and related notions.
module Term.Term.Raw (
    -- * Terms
      Term(..)
    , TermView (..)
    , viewTerm
    , TermView2 (..)
    , viewTerm2
    , termViewToTerm

    -- * Diff Type
    , DiffType (..)

    -- ** Standard function
    , traverseTerm
    , fmapTerm
    , bindTerm
    
    -- ** Smart constructors
    , lit
    , fApp
    , fAppAC
    , fAppC
    , fAppNoEq
    , fAppList
    , unsafefApp

    ) where

import           GHC.Generics (Generic)
import           Data.List
-- import           Data.Monoid
-- import           Data.Foldable (Foldable, foldMap)
-- import           Data.Traversable
import           Data.Typeable
import           Data.Binary
import           Data.Data

import           Control.DeepSeq
-- import           Control.Basics

import qualified Data.ByteString.Char8 as BC
import           Extension.Data.ByteString ()

import           Term.Term.Classes
import           Term.Term.FunctionSymbols

----------------------------------------------------------------------
-- Terms
----------------------------------------------------------------------

-- | A term in T(Sigma,a). Its constructors are kept abstract. Use 'viewTerm'
-- or 'viewTerm2' to inspect it.
data Term a = LIT a                 -- ^ atomic terms (constants, variables, ..)
            | FAPP FunSym [Term a]  -- ^ function applications
  deriving (Eq, Ord, Typeable, Data, Generic, NFData, Binary )

----------------------------------------------------------------------
-- Diff Type - whether left/right interpretation of diff is desired,
--             or no diff should occur
----------------------------------------------------------------------
data DiffType = DiffLeft | DiffRight | DiffNone | DiffBoth

----------------------------------------------------------------------
-- Views and smart constructors
----------------------------------------------------------------------

-- | View on terms that corresponds to representation.
data TermView a = Lit a
                | FApp FunSym [Term a]
  deriving (Show, Eq, Ord)

-- | Return the 'TermView' of the given term.
{-# INLINE viewTerm #-}
viewTerm :: Term a -> TermView a
viewTerm (LIT l) = Lit l
viewTerm (FAPP sym ts) = FApp sym ts

-- | Return the term of the given TermView.
termViewToTerm :: TermView a -> Term a
termViewToTerm (Lit l) = LIT l
termViewToTerm (FApp sym ts) = FAPP sym ts


-- | @fApp fsym as@ creates an application of @fsym@ to @as@. The function
-- ensures that the resulting term is in AC-normal-form.
{-# INLINE fApp #-}
fApp :: Ord a => FunSym -> [Term a] -> Term a
fApp (AC acSym)  ts = fAppAC acSym ts
fApp (C o)       ts = fAppC o ts
fApp List        ts = FAPP List ts
fApp s@(NoEq _)  ts = FAPP s ts

-- | Smart constructor for AC terms.
fAppAC :: Ord a => ACSym -> [Term a] -> Term a
fAppAC _     []  = error "Term.fAppAC: empty argument list"
fAppAC _     [a] = a
fAppAC acsym as  =
    FAPP (AC acsym) (sort (o_as ++ non_o_as))
  where
    o = AC acsym
    isOTerm (FAPP o' _) | o' == o = True
    isOTerm _                     = False
    (o_as0, non_o_as) = partition isOTerm as
    o_as              = [ a | FAPP _ ts <- o_as0, a <- ts ]

-- | Smart constructor for C terms.
fAppC :: Ord a => CSym -> [Term a] -> Term a
fAppC nacsym as = FAPP (C nacsym) (sort as)

-- | Smart constructor for non-AC/C terms.
{-# INLINE fAppNoEq #-}
fAppNoEq :: NoEqSym -> [Term a] -> Term a
fAppNoEq freesym = FAPP (NoEq freesym)

-- | Smart constructor for list terms.
{-# INLINE fAppList #-}
fAppList :: [Term a] -> Term a
fAppList = FAPP List

-- | @lit l@ creates a term from the literal @l@.
{-# INLINE lit #-}
lit :: a -> Term a
lit l = LIT l

-- | @unsafefApp fsym as@ creates an application of @fsym@ to as. The
--   caller has to ensure that the resulting term is in AC-normal-form.
unsafefApp :: FunSym -> [Term a] -> Term a
unsafefApp fsym as = FAPP fsym as

-- | View on terms that distinguishes function application of builtin symbols like exp.
data TermView2 a = FExp (Term a) (Term a)   | FInv (Term a) | FMult [Term a] | One
                 | FPMult (Term a) (Term a) | FEMap (Term a) (Term a)
                 | FUnion [Term a]
                 | FPair (Term a) (Term a)
                 | FDiff (Term a) (Term a)
                 | FAppNoEq NoEqSym [Term a]
                 | FAppC CSym [Term a]
                 | FList [Term a]
                 | Lit2 a
  deriving (Show, Eq, Ord)

-- | Returns the 'TermView2' of the given term.
viewTerm2 :: Show a => Term a -> TermView2 a
viewTerm2 (LIT l) = Lit2 l
viewTerm2 (FAPP List ts) = FList ts
viewTerm2 t@(FAPP (AC o) ts)
  | length ts < 2 = error $ "viewTerm2: malformed term `"++show t++"'"
  | otherwise     = (acSymToConstr o) ts
  where
    acSymToConstr Mult  = FMult
    acSymToConstr Union = FUnion
viewTerm2 (FAPP (C EMap) [ t1 ,t2 ]) = FEMap t1 t2
viewTerm2 t@(FAPP (C _)  _)          = error $ "viewTerm2: malformed term `"++show t++"'"
viewTerm2 t@(FAPP (NoEq o) ts) = case ts of
    [ t1, t2 ] | o == expSym    -> FExp   t1 t2  -- ensure here that FExp is always exp, never a user-defined symbol
    [ t1, t2 ] | o == pmultSym  -> FPMult t1 t2
    [ t1, t2 ] | o == pairSym   -> FPair  t1 t2
    [ t1, t2 ] | o == diffSym   -> FDiff  t1 t2
    [ t1 ]     | o == invSym    -> FInv   t1
    []         | o == oneSym    -> One
    _          | o `elem` ssyms -> error $ "viewTerm2: malformed term `"++show t++"'"
    _                           -> FAppNoEq o ts
  where
    -- special symbols
    ssyms = [ expSym, pairSym, diffSym, invSym, oneSym, pmultSym ]

----------------------------------------------------------------------
-- Instances
----------------------------------------------------------------------

{-# INLINE traverseTerm #-}
traverseTerm :: (Applicative f, Ord a, Ord b) => (a -> f b) -> Term a -> f (Term b)
traverseTerm f (LIT x)         = LIT <$> f x
traverseTerm f (FAPP fsym  as) = fApp fsym <$> traverse (traverseTerm f) as

{-# INLINE fmapTerm #-}
fmapTerm :: Ord b => (a -> b) -> Term a -> Term b
fmapTerm f = foldTerm (lit . f) fApp

{-# INLINE bindTerm #-}
bindTerm :: Ord b => Term a -> (a -> Term b) -> Term b
bindTerm m f = foldTerm f fApp m

instance Foldable Term where
    {-# INLINE foldMap #-}
    foldMap f = foldTerm f (const mconcat)

instance Show a => Show (Term a) where
    show t =
      case viewTerm t of
        Lit l                  -> show l
        FApp   (NoEq (s,_)) [] -> BC.unpack s
        FApp   (NoEq (s,_)) as -> BC.unpack s++"("++(intercalate "," (map show as))++")"
        FApp   (C EMap) as     -> BC.unpack emapSymString++"("++(intercalate "," (map show as))++")"
        FApp   List as         -> "LIST"++"("++(intercalate "," (map show as))++")"
        FApp   (AC o) as       -> show o++"("++(intercalate "," (map show as))++")"

-- | The fold function for @Term a@.
{-# INLINE foldTerm #-}
foldTerm :: (t -> b) -> (FunSym -> [b] -> b)
         -> Term t -> b
foldTerm fLIT fFAPP t = go t
  where go (LIT a)       = fLIT a
        go (FAPP fsym a) = fFAPP fsym $ map go a

instance Sized a => Sized (Term a) where
    size = foldTerm size (const $ \xs -> sum xs + 1)

