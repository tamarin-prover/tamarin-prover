{-# LANGUAGE TemplateHaskell, FlexibleInstances, DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Term Equalities, Matching Problems, and Subterm Rules.
module Term.Rewriting.Definitions (
    -- * Equalities
      Equal (..)
    , evalEqual

    -- * Matching Problems
    , Match(..)

    -- * Rewriting Rules
    , RRule(..)

    ) where

import Control.Applicative
import Data.Monoid
import Data.Foldable
import Data.Traversable

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
