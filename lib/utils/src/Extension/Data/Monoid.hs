{-# LANGUAGE CPP #-}
-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- A variant of "Data.Monoid" that also exports '(<>)' for 'mappend'.
module Extension.Data.Monoid (
    module Data.Monoid

#if __GLASGOW_HASKELL__ < 704
  , (<>)
#endif

  , MinMax(..)
  , minMaxSingleton
  ) where

import Data.Monoid

#if __GLASGOW_HASKELL__ < 704

infixr 6 <>

-- | An infix synonym for 'mappend'.
(<>) :: Monoid m => m -> m -> m
(<>) = mappend
{-# INLINE (<>) #-}

#endif

-- | A newtype wrapper around 'Maybe' that returns a tuple of the minimum and
-- maximum value encountered, if there was any.
newtype MinMax a = MinMax { getMinMax :: Maybe (a, a) }

-- | Construct a 'MinMax' value from a singleton value.
minMaxSingleton :: a -> MinMax a
minMaxSingleton x = MinMax (Just (x, x))

instance Ord a => Monoid (MinMax a) where
    mempty = MinMax Nothing

    MinMax Nothing             `mappend` y                          = y
    x                          `mappend` MinMax Nothing             = x
    MinMax (Just (xMin, xMax)) `mappend` MinMax (Just (yMin, yMax)) =
       MinMax (Just (min xMin yMin, max xMax yMax))
