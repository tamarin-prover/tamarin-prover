{-# LANGUAGE DeriveDataTypeable   #-}
-- {-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
-- {-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
-- {-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
-- {-# OPTIONS_GHC -fno-warn-orphans #-}
-- {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2011, 2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Formulas that represent security properties.
module Theory.Model.Atom(

  -- * Atoms
    Atom(..)
  , NAtom
  , LNAtom

  , isActionAtom
  , isLastAtom
  , isLessAtom
  , isEqAtom

  -- * LFormula
  , BLAtom

  -- * Pretty-Printing
  , prettyNAtom
  )
where

-- import           Control.Basics
import           Control.DeepSeq

import           GHC.Generics (Generic)
import           Data.Binary
-- import           Data.Foldable      (Foldable, foldMap)
import           Data.Data
-- import           Data.Monoid        (mappend, mempty)
-- import           Data.Traversable

import           Term.LTerm
import           Term.Unification
import           Theory.Model.Fact
import           Theory.Text.Pretty


------------------------------------------------------------------------------
-- Atoms
------------------------------------------------------------------------------

-- | @Atom@'s are the atoms of trace formulas parametrized over arbitrary
-- terms.
data Atom t = Action   t (Fact t)
            | EqE  t t
            | Less t t
            | Last t
            deriving( Eq, Ord, Show, Data, Typeable, Generic, NFData, Binary )

-- | @LAtom@ are the atoms we actually use in graph formulas input by the user.
type NAtom v = Atom (VTerm Name v)

-- | @LAtom@ are the atoms we actually use in graph formulas input by the user.
type LNAtom = Atom LNTerm

-- | Atoms built over 'BLTerm's.
type BLAtom = Atom BLTerm


-- Instances
------------

instance Functor Atom where
    fmap f (Action   i fa) = Action    (f i) (fmap f fa)
    fmap f (EqE l r)       = EqE       (f l) (f r)
    fmap f (Less v u)      = Less      (f v) (f u)
    fmap f (Last i)        = Last      (f i)

instance Foldable Atom where
    foldMap f (Action i fa)   =
        f i `mappend` (foldMap f fa)
    foldMap f (EqE l r)       = f l `mappend` f r
    foldMap f (Less i j)      = f i `mappend` f j
    foldMap f (Last i)        = f i

instance Traversable Atom where
    traverse f (Action i fa)   =
        Action <$> f i <*> traverse f fa
    traverse f (EqE l r)       = EqE <$> f l <*> f r
    traverse f (Less v u)      = Less <$> f v <*> f u
    traverse f (Last i)        = Last <$> f i

instance HasFrees t => HasFrees (Atom t) where
    foldFrees f = foldMap (foldFrees f)
    foldFreesOcc _ _ = const mempty -- we ignore occurences in atoms for now
    mapFrees  f = traverse (mapFrees f)

instance Apply LNAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)

instance Apply BLAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)


-- Queries
----------

-- | True iff the atom is an action atom.
isActionAtom :: Atom t -> Bool
isActionAtom ato = case ato of Action _ _ -> True; _ -> False

-- | True iff the atom is a last atom.
isLastAtom :: Atom t -> Bool
isLastAtom ato = case ato of Last _ -> True; _ -> False

-- | True iff the atom is a temporal ordering atom.
isLessAtom :: Atom t -> Bool
isLessAtom ato = case ato of Less _ _ -> True; _ -> False

-- | True iff the atom is an equality atom.
isEqAtom :: Atom t -> Bool
isEqAtom ato = case ato of EqE _ _ -> True; _ -> False


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
prettyNAtom (Last i)   = operator_ "last" <> parens (text (show i))
