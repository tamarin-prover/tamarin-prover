-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt, Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Term Equalities, Matching Problems, and Subterm Rules.
module Term.Rewriting.Definitions (
    -- * Equalities
      Equal (..)
    , evalEqual

    -- * Matching problems
    , Match(..)
    , flattenMatch
    , matchWith
    , matchOnlyIf

    -- * Rewriting rules
    , RRule(..)

    ) where

import Control.Arrow        ( (***) )
-- import Control.Applicative

import Extension.Data.Monoid
-- import Data.Foldable
-- import Data.Traversable

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

-- | Matching problems. Use the 'Monoid' instance to compose matching
-- problems.
data Match a =
      NoMatch
      -- ^ No matcher exists.
    | DelayedMatches [(a,a)]
      -- ^ A bunch of delayed (term,pattern) pairs.

instance Eq a => Eq (Match a) where
    x == y = flattenMatch x == flattenMatch y

instance Show a => Show (Match a) where
    show = show . flattenMatch


-- Smart constructors
---------------------

-- | Ensure that matching only succeeds if the condition holds.
matchOnlyIf :: Bool -> Match a
matchOnlyIf False = NoMatch
matchOnlyIf True  = mempty

-- | Match a term with a pattern.
matchWith :: a         -- ^ Term
          -> a         -- ^ Pattern
          -> Match a   -- ^ Matching problem.
matchWith t p = DelayedMatches [(t, p)]

-- Destructors
--------------

-- | Flatten a matching problem to a list of (term,pattern) pairs. If no
-- matcher exists, then 'Nothing' is returned.
flattenMatch :: Match a -> Maybe [(a, a)]
flattenMatch NoMatch             = Nothing
flattenMatch (DelayedMatches ms) = Just ms

-- Instances
------------

instance Functor Match where
    fmap _ NoMatch             = NoMatch
    fmap f (DelayedMatches ms) = DelayedMatches (fmap (f *** f) ms)

instance Monoid (Match a) where
    mempty = DelayedMatches []

    NoMatch            `mappend` _                  = NoMatch
    _                  `mappend` NoMatch            = NoMatch
    DelayedMatches ms1 `mappend` DelayedMatches ms2 =
        DelayedMatches (ms1 `mappend` ms2)


instance Foldable Match where
    foldMap _ NoMatch             = mempty
    foldMap f (DelayedMatches ms) = foldMap (\(t, p) -> f t <> f p) ms

instance Traversable Match where
    traverse _ NoMatch             = pure NoMatch
    traverse f (DelayedMatches ms) =
        DelayedMatches <$> traverse (\(t, p) -> (,) <$> f t <*> f p) ms

{-
instance Applicative Match where
    pure x                                = MatchWith x x
    (MatchWith ft fp) <*> (MatchWith t p) = MatchWith (ft t) (fp p)
-}


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
