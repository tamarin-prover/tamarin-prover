{-# LANGUAGE CPP #-}
-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- A variant of "Data.Monoid" that also exports '(<>)' for 'mappend'.
module Extension.Data.Monoid (
    (<>)
  , module Data.Monoid
  ) where

import Data.Monoid

#if __GLASGOW_HASKELL__ < 704

infixr 6 <>

-- | An infix synonym for 'mappend'.
(<>) :: Monoid m => m -> m -> m
(<>) = mappend
{-# INLINE (<>) #-}

#endif
