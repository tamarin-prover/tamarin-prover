{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveDataTypeable #-}
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
    , Term (..)

    , foldTerm
    , lits
    , prettyTerm
    
    -- ** Smart constructors
    , listToTerm

    -- ** Destrutors
    , destPair
    , destInv
    
    -- * Terms with constants and variables
    , Lit(..)
    , VTerm

    , varTerm
    , constTerm
    , varsVTerm
    , occursVTerm
    , constsVTerm
    , isVar

    , IsVar
    , IsConst

    -- * Equalities
    , Equal (..)
    , evalEqual

    -- * Matching Problems
    , Match(..)

    -- * Rewriting Rules
    , RRule(..)

    , module Term.Classes
    ) where

import Data.List
import qualified Data.DList as D
import Data.Monoid
import Data.Foldable (Foldable, foldMap)
import Data.Traversable 
import Data.Typeable
import Data.Generics
import Data.DeriveTH
import Data.Binary

import Control.DeepSeq
import Control.Basics

import Extension.Prelude

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



-- | These symbols are builtin and require special handling in the parser
--   or elsewhere.
pairSym, expSym, invSym, oneSym, zeroSym, emptySym :: NonACSym
pairSym  = ("pair",2)
expSym   = ("exp",2)
invSym   = ("inv",1)    -- ^ The inverse in the groups of exponents.
oneSym   = ("one", 0)   -- ^ The one in the group of exponents.
zeroSym  = ("zero",0)   -- ^ The zero for Xor.
emptySym = ("empty",0) -- ^ The empty multiset.

-- | Destruct a top-level function application.
{-# INLINE destFunApp #-}
destFunApp :: FunSym -> Term a -> Maybe [Term a]
destFunApp fsym (FApp fsym' args) | fsym == fsym' = Just args
destFunApp _    _                                 = Nothing

-- | Destruct a top-level pair.
destPair :: Term a -> Maybe (Term a, Term a)
destPair t = do [t1, t2] <- destFunApp (NonAC pairSym) t; return (t1, t2)

-- | Destruct a top-level inverse in the group of exponents.
destInv :: Term a -> Maybe (Term a)
destInv t = do [t1] <- destFunApp (NonAC invSym) t; return t1

----------------------------------------------------------------------
-- Terms
----------------------------------------------------------------------

-- | A term in T(Sigma,a).
data Term a = Lit a                 -- ^ atomic terms (constants, variables, ..)
            | FApp FunSym [Term a]  -- ^ function applications
  deriving (Eq, Ord, Typeable, Data )


-- Instances
------------

instance Functor Term where
    {-# INLINE fmap #-}
    fmap f = foldTerm (Lit . f) FApp

instance Foldable Term where
    {-# INLINE foldMap #-}
    foldMap f = foldTerm f (const mconcat)

instance Traversable Term where
    {-# INLINE traverse #-}
    traverse f (Lit x) = Lit <$> f x
    traverse f (FApp   fsym  as)  = FApp  fsym <$> traverse (traverse f) as

instance Applicative Term where
    {-# INLINE pure #-}
    pure = Lit
    {-# INLINE (<*>) #-}
    f <*> a = a >>= (\x -> fmap ($ x) f)

instance Monad Term where
    {-# INLINE return #-}
    return = Lit
    {-# INLINE (>>=) #-}
    m >>= f = foldTerm f FApp m

instance Show a => Show (Term a) where
    show (Lit l)                  = show l
    show (FApp   (NonAC (s,_)) []) = s
    show (FApp   (NonAC (s,_)) as) = s++"("++(intercalate "," (map show as))++")"
    show (FApp   List as)          = "LIST"++"("++(intercalate "," (map show as))++")"
    show (FApp   (AC o) as)        = show o++"("++(intercalate "," (map show as))++")"



-- | The fold function for @Term a@.
{-# INLINE foldTerm #-}
foldTerm :: (t -> b) -> (FunSym -> [b] -> b)
         -> Term t -> b
foldTerm fLit fApp t = go t
  where go (Lit a)        = fLit a
        go (FApp fsym a)   = fApp fsym $ map go a


instance Sized a => Sized (Term a) where
    size = foldTerm size (const $ \xs -> sum xs + 1)

-- | @lits t@ returns all literals that occur in term @t@. List can contain duplicates.
lits :: Ord a => Term a -> [a]
lits = foldMap return

-- | @listToTerm ts@ returns a term that represents @ts@.
listToTerm :: [Term a] -> Term a
listToTerm ts = FApp List ts

----------------------------------------------------------------------
-- Terms with constants and variables
----------------------------------------------------------------------


-- | A Lit is either a constant or a variable. (@Const@ is taken by Control.Applicative)
data Lit c v = Con c | Var v
  deriving (Eq, Ord, Data, Typeable)

-- | A VTerm is a term with constants and variables
type VTerm c v = Term (Lit c v)

-- | collect class constraints for variables
class (Ord v, Eq v, Show v) => IsVar v where

-- | collect class constraints for constants
class (Ord c, Eq c, Show c, Data c) => IsConst c where

-- | Functor instance in the variable.
instance Functor (Lit c) where
    fmap f (Var v)  = Var (f v)
    fmap _ (Con c) = Con c

-- | Foldable instance in the variable.
instance Foldable (Lit c) where
    foldMap f (Var v)  = f v
    foldMap _ (Con _) = mempty

-- | Traversable instance in the variable.
instance Traversable (Lit c) where
    sequenceA (Var v)  = Var <$> v
    sequenceA (Con n) = pure $ Con n

-- | Applicative instance in the variable.
instance Applicative (Lit c) where
    pure = Var
    (Var f)  <*> (Var x)  = Var (f x)
    (Var _)  <*> (Con n) = Con n
    (Con n) <*> _        = Con n

-- | Monad instance in the variable
instance Monad (Lit c) where
    return         = Var
    (Var x)  >>= f = f x
    (Con n)  >>= _ = Con n

instance Sized (Lit c v) where
    size _ = 1

instance (Show v, Show c) => Show (Lit c v) where
    show (Var x) = show x
    show (Con n) = show n

-- | @varTerm v@ is the 'VTerm' with the variable @v@.
varTerm :: v -> VTerm c v
varTerm = Lit . Var 

-- | @constTerm c@ is the 'VTerm' with the const @c@.
constTerm :: c -> VTerm c v
constTerm = Lit . Con

-- | @isVar t returns @True@ if @t@ is a variable.
isVar :: VTerm c v -> Bool
isVar (Lit (Var _)) = True
isVar _ = False

-- | @vars t@ returns a duplicate-free list of variables that occur in @t@.
varsVTerm :: (Eq v, Ord v) => VTerm c v -> [v]
varsVTerm = sortednub . D.toList . foldMap (foldMap return)

-- | @occurs v t@ returns @True@ if @v@ occurs in @t@
occursVTerm :: Eq v => v -> VTerm c v -> Bool
occursVTerm v = getAny . foldMap (foldMap (Any . (v==)))

-- | @constsVTerm t@ returns a duplicate-free list of constants that occur in @t@.
constsVTerm :: IsConst c => VTerm c v -> [c]
constsVTerm = sortednub . D.toList . foldMap fLit
  where fLit (Var _)  = mempty
        fLit (Con n) = return n

----------------------------------------------------------------------
-- Equalities, matching problems, and rewriting rules
----------------------------------------------------------------------

-- | An equality.
data Equal a = Equal { eqLHS :: a, eqRHS :: a }
    deriving (Eq, Show)

-- | True iff the two sides of the equality are equal with respect to their
-- 'Eq' instance.
evalEqual :: Eq a => Equal a -> Bool
evalEqual (Equal l r) = l == r

instance Functor Equal where
    fmap f (Equal lhs rhs) = Equal (f lhs) (f rhs) 

instance Monoid a => Monoid (Equal a) where
    mempty                                = Equal mempty mempty
    (Equal l1 r1) `mappend` (Equal l2 r2) = 
        Equal (l1 `mappend` l2) (r1 `mappend` r2)

instance Foldable Equal where
    foldMap f (Equal l r) = f l `mappend` f r

instance Traversable Equal where
    traverse f (Equal l r) = Equal <$> f l <*> f r

instance Applicative Equal where
    pure x                        = Equal x x
    (Equal fl fr) <*> (Equal l r) = Equal (fl l) (fr r)

-- | A matching problem.
data Match a = MatchWith { matchTerm :: a, matchPattern :: a }
    deriving (Eq, Show)

instance Functor Match where
    fmap f (MatchWith t p) = MatchWith (f t) (f p) 

instance Monoid a => Monoid (Match a) where
    mempty                                        =
        MatchWith mempty mempty
    (MatchWith t1 p1) `mappend` (MatchWith t2 p2) = 
        MatchWith (t1 `mappend` t2) (p1 `mappend` p2)

instance Foldable Match where
    foldMap f (MatchWith t p) = f t `mappend` f p

instance Traversable Match where
    traverse f (MatchWith t p) = MatchWith <$> f t <*> f p

instance Applicative Match where
    pure x                                = MatchWith x x
    (MatchWith ft fp) <*> (MatchWith t p) = MatchWith (ft t) (fp p)


-- |  A rewrite rule.
data RRule a = RRule a a
    deriving (Show, Ord, Eq)

instance Functor RRule where
    fmap f (RRule lhs rhs) = RRule (f lhs) (f rhs) 

instance Monoid a => Monoid (RRule a) where
    mempty                                = RRule mempty mempty
    (RRule l1 r1) `mappend` (RRule l2 r2) = 
        RRule (l1 `mappend` l2) (r1 `mappend` r2)

instance Foldable RRule where
    foldMap f (RRule l r) = f l `mappend` f r

instance Traversable RRule where
    traverse f (RRule l r) = RRule <$> f l <*> f r

instance Applicative RRule where
    pure x                        = RRule x x
    (RRule fl fr) <*> (RRule l r) = RRule (fl l) (fr r)

----------------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------------

-- | Pretty print a term.
prettyTerm :: Document d => (l -> d) -> Term l -> d
prettyTerm ppLit = ppTerm
  where
    ppTerm t = case t of
        Lit l                           -> ppLit l
        FApp (AC o)             ts      -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NonAC ("exp",2))  [t1,t2] -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NonAC ("pair",2)) _       -> ppTerms ", " 1 "<" ">" (split t)
        FApp (NonAC (f,_))      ts      -> ppFun f ts
        FApp List               ts      -> ppFun "LIST" ts

    ppACOp Mult = "*"
    ppACOp MUn  = "#"
    ppACOp Xor  = "+"

    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) . 
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts

    split (FApp (NonAC ("pair",2)) [t1,t2]) = t1 : split t2
    split t                                 = [t]

    ppFun f ts =
        text (f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"

-- Derived instances
--------------------

$( derive makeNFData ''FunSym)
$( derive makeNFData ''ACSym)
$( derive makeNFData ''Term )
$( derive makeNFData ''Lit)

$( derive makeBinary ''FunSym)
$( derive makeBinary ''ACSym)
$( derive makeBinary ''Term )
$( derive makeBinary ''Lit)


