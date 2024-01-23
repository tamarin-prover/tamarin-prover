-- |
-- Copyright   : (c) 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
--
-- Module that can be imported to ignore calls to @trace@.
module Debug.Trace.Ignore (
    trace
  ) where

-- | @trace a b@ returns the second argument.
trace :: a -> b -> b
trace = flip const

