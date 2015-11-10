{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : unknown
--
-- A monad transformer to enable other *commutative* monads to represent
-- logical disjunctions.
module Control.Monad.Trans.Disj (
  -- * The 'DisjT' monad transformer
    DisjT(..)
  , disjT
  , runDisjT
  ) where

-- import Control.Applicative
import Control.Monad.List
import Control.Monad.Reader
import Control.Monad.Disj.Class

------------------------------------------------------------------------------
-- The 'DisjT' monad transformer
------------------------------------------------------------------------------

-- | A disjunction of atoms of type a.
newtype DisjT m a = DisjT { unDisjT :: ListT m a }
  deriving (Functor, Applicative, MonadTrans )

-- | Construct a 'DisjT' action.
disjT :: m [a] -> DisjT m a
disjT = DisjT . ListT

-- | Run a 'DisjT' action.
runDisjT :: DisjT m a -> m [a]
runDisjT = runListT . unDisjT




-- Instances
------------

instance Monad m => Monad (DisjT m) where
    -- Ensure that contradictions are not reported via fail!
    fail    = error
    {-# INLINE return #-}
    return  = DisjT . return
    {-# INLINE (>>=) #-}
    m >>= f = DisjT $ (unDisjT . f) =<< unDisjT m

instance Monad m => MonadDisj (DisjT m) where
    contradictoryBecause _ = DisjT mzero
    disjunction m1 m2      = DisjT $ unDisjT m1 `mplus` unDisjT m2


instance MonadReader r m => MonadReader r (DisjT m) where
    ask       = lift ask
    local f m = DisjT $ local f $ unDisjT m

