{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Shallow monad transformer for dealing with bindings.
--
module Control.Monad.Bind (

  -- * Bindings
    Bindings
  , noBindings

  -- * MonadBind class
  , MonadBind

  -- * Bind monad
  , Bind 
  , runBind
  , evalBind
  , execBind

  -- * BindT monad transformer
  , BindT 
  , runBindT
  , evalBindT
  , execBindT

  -- * Binding operations

  , lookupBinding
  , insertBinding
  , importBinding

  , module Control.Monad.Fresh
  
  ) where

import qualified Data.Map as M

import Control.Basics
import Control.Monad.State
import Control.Monad.Fresh

import qualified Control.Monad.Trans.PreciseFresh as Precise

------------------------------------------------------------------------------
-- Bindings
------------------------------------------------------------------------------

-- | Type constructor for the state of the binding store.
type Bindings = M.Map

-- | The empty binding store.
noBindings :: Bindings v k
noBindings = M.empty

------------------------------------------------------------------------------
-- Type synonym for the StateT monad transformer
------------------------------------------------------------------------------

class MonadState (Bindings k v) m => MonadBind k v m where

instance Monad m => MonadBind k v (StateT (Bindings k v) m) where

instance MonadBind k v m => MonadBind k v (FreshT m) where
instance MonadBind k v m => MonadBind k v (Precise.FreshT m) where

------------------------------------------------------------------------------
-- Type synonym for the StateT monad transformer
------------------------------------------------------------------------------

-- | Managing bindings on top of another monad.
type BindT k v = StateT (Bindings k v)

-- | Run a computation with bindings.
runBindT :: BindT k v m a -> Bindings k v -> m (a, Bindings k v)
runBindT = runStateT

-- | Evaluate a binding context computation.
evalBindT :: Monad m => BindT k v m a -> Bindings k v -> m a
evalBindT = evalStateT

-- | Execute a binding context computation.
execBindT :: Monad m => BindT k v m a -> Bindings k v -> m (Bindings k v)
execBindT = execStateT

------------------------------------------------------------------------------
-- Type synonym for the State monad
------------------------------------------------------------------------------

-- | Managing just bindings.
type Bind k v = State (Bindings k v)

-- | Run a computation with bindings.
runBind :: Bind k v a -> Bindings k v -> (a, Bindings k v)
runBind = runState

-- | Evaluate a binding context computation.
evalBind :: Bind k v a -> Bindings k v -> a
evalBind = evalState

-- | Execute a binding context computation.
execBind :: Bind k v a -> Bindings k v -> Bindings k v
execBind = execState


------------------------------------------------------------------------------
-- Binding operations
------------------------------------------------------------------------------

-- | Lookup a stored binding.
lookupBinding :: (MonadBind k v m, Ord k) 
              => k -> m (Maybe v)
lookupBinding = gets . M.lookup

-- | @insertBinding k v@ inserts the binding of @k@ to @v@, possibly
-- overwriting the existing binding of @k@.
insertBinding :: (MonadBind k v m, Ord k) 
              => k -> v -> m ()
insertBinding k = modify . M.insert k

-- | @importBinding mkR d n@ checks if there is already a binding registered
-- for the value @d@ and if not it generates a fresh identifier using the name
-- @n@ as a hint and converting name and identifier to a value using $mkR$.
{-# INLINE importBinding #-}
importBinding :: (MonadBind k v m, MonadFresh m, Ord k) 
               => (String -> Integer -> v) 
               -> k 
               -> String -> m v
importBinding mkR k n = do
    rOpt <- lookupBinding k
    case rOpt of
      Nothing -> do v <- mkR n <$> freshIdent n
                    modify $ M.insert k v 
                    return v
      Just v -> return v
