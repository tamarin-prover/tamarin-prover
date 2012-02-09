-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Monoids for bounded types.
module Extension.Data.Bounded (
    BoundedMax(..)
  ) where

import Data.Monoid

-- | A newtype wrapper for a monoid of the maximum of a bounded type.
newtype BoundedMax a = BoundedMax {getBoundedMax :: a}
    deriving( Eq, Ord, Show )
      
instance (Ord a, Bounded a) => Monoid (BoundedMax a) where
    mempty                                  = BoundedMax minBound
    (BoundedMax x) `mappend` (BoundedMax y) = BoundedMax (max x y)



-- TODO: Add BoundedMin
