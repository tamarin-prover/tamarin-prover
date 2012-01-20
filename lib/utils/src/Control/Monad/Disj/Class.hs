{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : unknown
--
-- A monad to represent logical disjunctions.
module Control.Monad.Disj.Class (
  -- * The @MonadDisj@ class
    MonadDisj(..)
  ) where

import Control.Monad.Trans
import qualified Control.Monad.State.Lazy   as L
import qualified Control.Monad.State.Strict as S
import Control.Monad.Reader
import Control.Monad.Fresh


------------------------------------------------------------------------------
-- The MonadDisj class
------------------------------------------------------------------------------


class Monad m => MonadDisj m where
    -- | Mark a contradiction.
    contradictoryBecause :: Maybe String -> m a
    -- | Disjoin two computations.
    disjunction          :: m a -> m a -> m a


------------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------------

instance MonadDisj m => MonadDisj (L.StateT s m) where
    contradictoryBecause = lift . contradictoryBecause
    disjunction m1 m2 = L.StateT $ \s -> L.runStateT m1 s `disjunction` L.runStateT m2 s

instance MonadDisj m => MonadDisj (S.StateT s m) where
    contradictoryBecause = lift . contradictoryBecause
    disjunction m1 m2 = S.StateT $ \s -> S.runStateT m1 s `disjunction` S.runStateT m2 s

instance MonadDisj m => MonadDisj (FreshT m) where
    contradictoryBecause = lift . contradictoryBecause
    disjunction m1 m2 = FreshT $ unFreshT m1 `disjunction` unFreshT m2

instance MonadDisj m => MonadDisj (ReaderT r m) where
    contradictoryBecause = lift . contradictoryBecause
    disjunction m1 m2 = ReaderT $ \r -> runReaderT m1 r `disjunction` runReaderT m2 r



