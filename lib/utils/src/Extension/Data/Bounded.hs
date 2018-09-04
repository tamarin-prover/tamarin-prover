-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Monoids for bounded types.
module Extension.Data.Bounded (
    BoundedMax(..)
  , BoundedMin(..)
  ) where

-- import Data.Monoid
-- import Data.Semigroup

-- | A newtype wrapper for a monoid of the maximum of a bounded type.
newtype BoundedMax a = BoundedMax {getBoundedMax :: a}
    deriving( Eq, Ord, Show )

instance (Ord a, Bounded a) => Semigroup (BoundedMax a) where
    BoundedMax x <> BoundedMax y = BoundedMax (max x y)

instance (Ord a, Bounded a) => Monoid (BoundedMax a) where
    mempty                                  = BoundedMax minBound
    mappend = (<>)

-- | A newtype wrapper for a monoid of the minimum of a bounded type.
newtype BoundedMin a = BoundedMin {getBoundedMin :: a}
    deriving( Eq, Ord, Show )

instance (Ord a, Bounded a) => Semigroup (BoundedMin a) where
    BoundedMin x <> BoundedMin y = BoundedMin (min x y)

instance (Ord a, Bounded a) => Monoid (BoundedMin a) where
    mempty                                  = BoundedMin maxBound
