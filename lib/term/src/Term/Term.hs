{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
  -- for ByteString
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
    , FunSig
    , dhFunSig
    , xorFunSig
    , msetFunSig
    , pairFunSig
    , dhReducibleFunSig
    , implicitFunSig

    -- * Terms
    , Term
    , TermView (..)
    , viewTerm
    , TermView2 (..)
    , viewTerm2

    , traverseTerm
    , fmapTerm
    , bindTerm
    , lits
    , showFunSymName
    , prettyTerm

    -- ** Smart constructors
    , lit
    , fApp
    , fAppAC
    , fAppNonAC
    , fAppList
    , unsafefApp

    , fAppMult
    , fAppOne
    , fAppExp
    , fAppInv
    , fAppXor
    , fAppZero
    , fAppUnion
    , fAppEmpty
    , fAppPair
    , fAppFst
    , fAppSnd

    -- ** exp symbol
    , expSymString
    , invSymString

    -- ** Destructors and classifiers
    , destPair
    , destInverse
    , destProduct
    , destXor
    , destUnion

    , isPair
    , isInverse
    , isProduct
    , isXor
    , isUnion
    , isNullaryFunction

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
import Data.Maybe (isJust)

import Control.DeepSeq
import Control.Basics

import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC
import Extension.Data.ByteString ()

import Data.Set (Set)
import qualified Data.Set as S

import Text.PrettyPrint.Class

import Term.Classes

----------------------------------------------------------------------
-- AC operators for terms
----------------------------------------------------------------------

-- | AC function symbols.
data ACSym = Union | Xor | Mult
  deriving (Eq, Ord, Typeable, Data, Show)

-- | non-AC function symbols
type NonACSym = (ByteString, Int)

-- | Function symbols
data FunSym = NonAC NonACSym  -- ^ a non-AC function function symbol of a given arity
            | AC    ACSym     -- ^ an AC function symbol, can be used n-ary
            | List            -- ^ a non-AC n-ary function symbol of TOP sort
  deriving (Eq, Ord, Typeable, Data, Show)

-- | Function signatures.
type FunSig = Set NonACSym

expSymString :: ByteString
expSymString = "exp"

invSymString :: ByteString
invSymString = "inv"

pairSym, expSym, invSym, oneSym, zeroSym, emptySym, fstSym, sndSym :: NonACSym
-- | Pairing.
pairSym  = ("pair",2)
-- | Exponentiation.
expSym   = (expSymString,2)
-- | The inverse in the groups of exponents.
invSym   = (invSymString,1)
-- | The one in the group of exponents.
oneSym   = ("one", 0)
-- | The zero for Xor.
zeroSym  = ("zero",0)
-- | The empty multiset.
emptySym = ("empty",0)
-- | Projection of first component of pair. Only required for pairFunSig.
fstSym     = ("fst",1)
-- | Projection of second component of pair. Only required for pairFunSig.
sndSym     = ("snd",1)


-- | The signature for the non-AC Diffie-Hellman function symbols.
dhFunSig :: FunSig
dhFunSig = S.fromList [ expSym, oneSym, invSym ]

-- | The signature for the non-AC Xor function symbols.
xorFunSig :: FunSig
xorFunSig = S.fromList [ zeroSym ]

-- | The signature for then non-AC multiset function symbols.
msetFunSig :: FunSig
msetFunSig = S.fromList [ emptySym ]

-- | The signature for pairing.
pairFunSig :: FunSig
pairFunSig = S.fromList [ pairSym, fstSym, sndSym ]

-- | Reducible non-AC symbols for DH.
dhReducibleFunSig :: FunSig
dhReducibleFunSig = S.fromList [ expSym, invSym ]

-- | Implicit non-AC symbols.
implicitFunSig :: FunSig
implicitFunSig = S.fromList [ invSym, pairSym ]

----------------------------------------------------------------------
-- Terms
----------------------------------------------------------------------

-- | A term in T(Sigma,a). Its constructors are kept abstract. Use 'viewTerm'
-- or 'viewTerm2' to inspect it.
data Term a = LIT a                 -- ^ atomic terms (constants, variables, ..)
            | FAPP FunSym [Term a]  -- ^ function applications
  deriving (Eq, Ord, Typeable, Data )

-- | Destruct a top-level function application.
{-# INLINE destFunApp #-}
destFunApp :: FunSym -> Term a -> Maybe [Term a]
destFunApp fsym (FAPP fsym' args) | fsym == fsym' = Just args
destFunApp _    _                                 = Nothing

-- | Destruct a top-level pair.
destPair :: Term a -> Maybe (Term a, Term a)
destPair t = do [t1, t2] <- destFunApp (NonAC pairSym) t; return (t1, t2)

-- | Destruct a top-level inverse in the group of exponents.
destInverse :: Term a -> Maybe (Term a)
destInverse t = do [t1] <- destFunApp (NonAC invSym) t; return t1

-- | Destruct a top-level product.
destProduct :: Term a -> Maybe [Term a]
destProduct (FAPP (AC Mult) ts) = return ts
destProduct _                   = Nothing

-- | Destruct a top-level product.
destXor :: Term a -> Maybe [Term a]
destXor (FAPP (AC Xor) ts) = return ts
destXor _                  = Nothing

-- | Destruct a top-level multiset union.
destUnion :: Term a -> Maybe [Term a]
destUnion (FAPP (AC Union) ts) = return ts
destUnion _                    = Nothing

-- | 'True' iff the term is a well-formed pair.
isPair :: Term a -> Bool
isPair = isJust . destPair

-- | 'True' iff the term is a well-formed inverse.
isInverse :: Term a -> Bool
isInverse = isJust . destInverse

-- | 'True' iff the term is a well-formed product.
isProduct :: Term a -> Bool
isProduct = isJust . destProduct

-- | 'True' iff the term is a well-formed xor'ing.
isXor :: Term a -> Bool
isXor = isJust . destXor

-- | 'True' iff the term is a well-formed xor'ing.
isUnion :: Term a -> Bool
isUnion = isJust . destXor

-- | 'True' iff the term is a nullary, public function.
isNullaryFunction :: Term a -> Bool
isNullaryFunction (viewTerm -> FApp (NonAC (_, 0)) _) = True
isNullaryFunction _                                   = False

-- | View on terms that corresponds to representation.
data TermView a = Lit a
                | FApp FunSym [Term a]
  deriving (Show, Eq, Ord)

{-# INLINE viewTerm #-}
-- | Return the 'TermView' of the given term.
viewTerm :: Term a -> TermView a
viewTerm (LIT l)       = Lit l
viewTerm (FAPP sym ts) = FApp sym ts

-- | @fApp fsym as@ creates an application of @fsym@ to @as@. The function
-- ensures that the resulting term is in AC-normal-form.
{-# INLINE fApp #-}
fApp :: Ord a => FunSym -> [Term a] -> Term a
fApp (AC acSym) ts = fAppAC acSym ts
fApp o          ts = FAPP o ts

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

-- | Smart constructor for non-AC terms.
{-# INLINE fAppNonAC #-}
fAppNonAC :: NonACSym -> [Term a] -> Term a
fAppNonAC nacsym = FAPP (NonAC nacsym)

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
data TermView2 a = FExp (Term a) (Term a) | FInv (Term a) | FMult [Term a] | One
                 | FXor [Term a] | Zero
                 | FUnion [Term a] | Empty
                 | FPair (Term a) (Term a)
                 | FAppNonAC NonACSym [Term a]
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
    acSymToConstr Xor   = FXor
    acSymToConstr Union = FUnion
viewTerm2 t@(FAPP (NonAC o) ts) = case ts of
    [ t1, t2 ] | o == expSym    -> FExp  t1 t2
    [ t1, t2 ] | o == pairSym   -> FPair t1 t2
    [ t1 ]     | o == invSym    -> FInv  t1
    []         | o == oneSym    -> One
    []         | o == zeroSym   -> Zero
    []         | o == emptySym  -> Empty
    _          | o `elem` ssyms -> error $ "viewTerm2: malformed term `"++show t++"'"
    _                           -> FAppNonAC o ts
  where
    -- special symbols
    ssyms = [ expSym, pairSym, invSym, oneSym, zeroSym, emptySym ]


-- | Smart constructors for mult, union, and xor.
fAppMult, fAppUnion, fAppXor :: Ord a => [Term a] -> Term a
fAppMult ts  = fApp (AC Mult)  ts
fAppUnion ts = fApp (AC Union) ts
fAppXor ts   = fApp (AC Xor)   ts

-- | Smart constructors for one, zero, and empty.
fAppOne, fAppZero, fAppEmpty :: Term a
fAppOne   = fAppNonAC oneSym   []
fAppZero  = fAppNonAC zeroSym  []
fAppEmpty = fAppNonAC emptySym []

-- | Smart constructors for pair and exp.
fAppPair, fAppExp :: (Term a, Term a) -> Term a
fAppPair (x,y) = fAppNonAC pairSym [x, y]
fAppExp  (b,e) = fAppNonAC expSym  [b, e]

-- | Smart constructors for inv, fst, and snd.
fAppInv, fAppFst, fAppSnd :: Term a -> Term a
fAppInv e = fAppNonAC invSym [e]
fAppFst a = fAppNonAC fstSym [a]
fAppSnd a = fAppNonAC sndSym [a]


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
    show (FAPP   (NonAC (s,_)) []) = BC.unpack s
    show (FAPP   (NonAC (s,_)) as) = BC.unpack s++"("++(intercalate "," (map show as))++")"
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

----------------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------------

-- | Convert a function symbol to its name.
showFunSymName :: FunSym -> String
showFunSymName (NonAC (bs, _)) = BC.unpack bs
showFunSymName (AC op)         = show op
showFunSymName List            = "List"

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

    ppACOp Mult  = "*"
    ppACOp Union = "#"
    ppACOp Xor   = "+"

    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts

    split (FAPP (NonAC ("pair",2)) [t1,t2]) = t1 : split t2
    split t                                 = [t]

    ppFun f ts =
        text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"

-- Derived instances
--------------------

$( derive makeNFData ''FunSym)
$( derive makeNFData ''ACSym)
$( derive makeNFData ''Term )

$( derive makeBinary ''FunSym)
$( derive makeBinary ''ACSym)
$( derive makeBinary ''Term )
