-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- | A type class for sized types.
module Term.Term.Classes where

class Sized a where
    size :: a -> Int

instance Sized a => Sized [a] where
    size = sum . map size