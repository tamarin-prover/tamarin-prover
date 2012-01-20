-- |
-- Copyright   : (c) 2010 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Type-class abstracting computations that need a fresh name supply.
module Control.Monad.Fresh.Class (
  MonadFresh(..)
) where

import Control.Basics

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer

import qualified Control.Monad.Trans.Fresh as Fresh (FreshT, freshIdent)

-- Added 'Applicative' until base states this hierarchy
class (Applicative m, Monad m) => MonadFresh m where
    freshIdent :: String -- ^ Desired name.
               -> m Int  -- ^ Fresh identifier.


instance (Functor m, Monad m) => MonadFresh (Fresh.FreshT m) where
    freshIdent = Fresh.freshIdent


----------------------------------------------------------------------------
-- instances for other mtl transformers
--
-- TODO: Add remaining ones

instance MonadFresh m => MonadFresh (MaybeT m) where
    freshIdent = lift . freshIdent

instance MonadFresh m => MonadFresh (StateT s m) where
    freshIdent = lift . freshIdent

instance MonadFresh m => MonadFresh (ReaderT r m) where
    freshIdent = lift . freshIdent

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
    freshIdent = lift . freshIdent
