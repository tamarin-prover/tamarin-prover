{-# LANGUAGE StandaloneDeriving
           , FlexibleContexts
           , TypeSynonymInstances
           , FlexibleInstances
           , DeriveDataTypeable
           , TupleSections
  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Copyright   : (c) 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Formulas that represent security properties.
module Theory.Atom(

  -- * Atoms
    Atom(..)
  , NAtom
  , LNAtom

  -- * LFormula
  , BLVar
  , BLAtom

  -- * Pretty-Printing
  , prettyNAtom
  )
where

import Term.Rewriting.NormAC
import Theory.Fact
import Theory.Pretty

import Data.Monoid   (mappend)
import Data.Foldable (Foldable, foldMap)
import Data.Traversable 
import Data.Generics

import Control.Basics

------------------------------------------------------------------------------
-- Atoms
------------------------------------------------------------------------------

-- | @Atom@'s are the atoms of trace formulas parametrized over arbitrary
-- terms. 
data Atom t = Action   t (Fact t)
            | EqE  t t
            | Less t t
            | Last t
            | DedBefore t t
            | EdgeA (t, Int) (t, Int)
            deriving( Eq, Ord, Show, Data, Typeable )

-- | @LAtom@ are the atoms we actually use in graph formulas input by the user.
type NAtom v = Atom (VTerm Name v)

-- | @LAtom@ are the atoms we actually use in graph formulas input by the user.
type LNAtom = Atom LNTerm

-- | 'LVar's combined with quantified variables. They occur only in 'LFormula's.
type BLVar = BVar LVar

-- | Terms built over names and 'LVar's combined with quantified variables.
type BLTerm = NTerm BLVar

-- | Atoms built over 'BLTerm's.
type BLAtom = Atom BLTerm


-- Instances
------------

instance Functor Atom where
    fmap f (Action   i fa) = Action    (f i) (fmap f fa)
    fmap f (EqE l r)       = EqE       (f l) (f r)
    fmap f (Less v u)      = Less      (f v) (f u)
    fmap f (Last i)        = Last      (f i)
    fmap f (DedBefore t i) = DedBefore (f t) (f i)
    fmap f (EdgeA x y)     = EdgeA     (first f x) (first f y)

instance Foldable Atom where
    foldMap f (Action i fa)   = 
        f i `mappend` (foldMap f fa)
    foldMap f (EqE l r)       = f l `mappend` f r
    foldMap f (Less i j)      = f i `mappend` f j
    foldMap f (Last i)        = f i
    foldMap f (DedBefore t i) = f t `mappend` f i
    foldMap f (EdgeA x y)     = f (fst x) `mappend` f (fst y)

instance Traversable Atom where
    traverse f (Action i fa)   = 
        Action <$> f i <*> traverse f fa
    traverse f (EqE l r)       = EqE <$> f l <*> f r
    traverse f (Less v u)      = Less <$> f v <*> f u
    traverse f (Last i)        = Last <$> f i
    traverse f (DedBefore t i) = DedBefore <$> f t <*> f i
    traverse f (EdgeA (x,i) (y,j)) = 
        EdgeA <$> ((,i) <$> f x) <*> ((,j) <$> f y)

instance HasFrees t => HasFrees (Atom t) where
    foldFrees f = foldMap (foldFrees f)
    mapFrees  f = traverse (mapFrees f)

instance Apply LNAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)
    apply subst (DedBefore t i)   = DedBefore (apply subst t) (apply subst i)
    apply subst (EdgeA x y)       = 
        EdgeA (first (apply subst) x) (first (apply subst) y)

instance Apply BLVar where
    apply _     x@(Bound _) = x
    apply subst x@(Free  v) = maybe x extractVar $ imageOf subst v
      where
        extractVar (Lit (Var v')) = Free v'
        extractVar t                     = 
          error $ "apply (BLVar): variable '" ++ show v ++ 
                  "' substituted with term '" ++ show t ++ "'"

instance Apply BLTerm where
    apply subst = normAC . (>>= applyBLLit)
      where
        applyBLLit :: Lit Name BLVar -> BLTerm
        applyBLLit l@(Var (Free v)) = 
            maybe (Lit l) (fmap (fmap Free)) (imageOf subst v)
        applyBLLit l                = Lit l

instance Apply BLAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)
    apply subst (DedBefore t i)   = DedBefore (apply subst t) (apply subst i)
    apply subst (EdgeA x y)       = 
        EdgeA (first (apply subst) x) (first (apply subst) y)


------------------------------------------------------------------------------
-- Pretty-Printing
------------------------------------------------------------------------------

prettyNAtom :: (Show v, HighlightDocument d) => NAtom v -> d
prettyNAtom (Action v fa) = 
    prettyFact prettyNTerm fa <-> opAction <-> text (show v) 
prettyNAtom (EqE l r) =
    sep [prettyNTerm l <-> opEqual, prettyNTerm r]
    -- sep [prettyNTerm l <-> text "≈", prettyNTerm r]
prettyNAtom (Less u v) = text (show u) <-> opLess <-> text (show v)
prettyNAtom (Last i)   = operator_ "Last" <> parens (text (show i))
prettyNAtom (DedBefore t i) = text (show t) <-> opDedBefore <-> text (show i)
prettyNAtom (EdgeA x y) = text (show x) <-> opEdge <-> text (show y)

