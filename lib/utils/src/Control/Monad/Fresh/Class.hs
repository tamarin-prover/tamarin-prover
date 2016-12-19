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

-- import Control.Basics

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer

import qualified Control.Monad.Trans.FastFresh    as Fast
import qualified Control.Monad.Trans.PreciseFresh as Precise

-- Added 'Applicative' until base states this hierarchy
class (Applicative m, Monad m) => MonadFresh m where
    -- | Get the integer of the next fresh identifier of this name.
    freshIdent  :: String   -- ^ Desired name
                -> m Integer

    -- | Get a number of fresh identifiers. This reserves the required number
    -- of identifiers on all names.
    freshIdents :: Integer    -- ^ Number of desired fresh identifiers.
                -> m Integer  -- ^ The first Fresh identifier.

    -- | Scope the 'freshIdent' and 'freshIdents' requests such that these
    -- variables are not marked as used once the scope is left.
    scopeFreshness :: m a -> m a

instance Monad m => MonadFresh (Fast.FreshT m) where
    freshIdent _name = Fast.freshIdents 1
    freshIdents      = Fast.freshIdents
    scopeFreshness   = Fast.scopeFreshness

instance Monad m => MonadFresh (Precise.FreshT m) where
    freshIdent     = Precise.freshIdent
    freshIdents    = Precise.freshIdents
    scopeFreshness = Precise.scopeFreshness


----------------------------------------------------------------------------
-- instances for other mtl transformers
--
-- TODO: Add remaining ones

instance MonadFresh m => MonadFresh (MaybeT m) where
    freshIdent       = lift . freshIdent
    freshIdents      = lift . freshIdents
    scopeFreshness m = MaybeT $ scopeFreshness (runMaybeT m)

instance MonadFresh m => MonadFresh (StateT s m) where
    freshIdent  = lift . freshIdent
    freshIdents = lift . freshIdents
    scopeFreshness m = StateT $ \s -> scopeFreshness (runStateT m s)

instance MonadFresh m => MonadFresh (ReaderT r m) where
    freshIdent       = lift . freshIdent
    freshIdents      = lift . freshIdents
    scopeFreshness m = ReaderT $ \r -> scopeFreshness (runReaderT m r)

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
    freshIdent       = lift . freshIdent
    freshIdents      = lift . freshIdents
    scopeFreshness m = WriterT $ scopeFreshness (runWriterT m)
