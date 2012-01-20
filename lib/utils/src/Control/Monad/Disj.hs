{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Computations that need perform case distinctions.
module Control.Monad.Disj (

  -- * MonadDisj class
    MonadDisj(..)

  , contradictory
  , contradictoryIf
  , contradiction
  , contradictionIf
  , disjunctions
  , disjunctionOfList

  -- * The DisjT monad transformer
  , DisjT(..)
  , disjT
  , runDisjT

  -- * Convencience exports
  , module Control.Monad
  , module Control.Monad.Fix
  , module Control.Monad.Trans

  ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans

import Control.Monad.Disj.Class
import Control.Monad.Trans.Disj

-- | @contradiction reason@ denotes the logical false, but also 
-- provides the @reason@ as meta-information.
contradiction :: MonadDisj m => String -> m a
contradiction = contradictoryBecause . Just

-- | @contradictionIf b reason@ is logically equivalent to @not b@, but also
-- provides the @reason@ as meta-information.
contradictionIf :: MonadDisj m => Bool -> String -> m ()
contradictionIf b reason | b         = contradiction reason
                         | otherwise = return ()

-- | @contradictory@ denotes the logical false.
contradictory :: MonadDisj m => m a
contradictory = contradictoryBecause Nothing

-- | @contradictoryIf b@ is logically equivalent to @not b@
contradictoryIf :: MonadDisj m => Bool -> m ()
contradictoryIf b | b         = contradictory
                  | otherwise = return ()

-- | @disjunctions ds@ builds the disjunction of all the @ds@ values.
disjunctions :: MonadDisj m => [m a] -> m a
disjunctions = foldr disjunction contradictory

-- | @disjunctionOfList xs@ build the disjunction of the values in list @xs@.
disjunctionOfList :: MonadDisj m => [a] -> m a
disjunctionOfList = disjunctions . map return


