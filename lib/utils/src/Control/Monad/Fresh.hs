{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Computations that need a fresh name supply.
module Control.Monad.Fresh (

  -- * MonadFresh class
    MonadFresh(..)

  -- * The Fresh monad
  , Fresh
  , runFresh
  , evalFresh
  , execFresh

  -- * The fast FreshT monad transformer
  , FreshT(..)
  , freshT
  , runFreshT
  , evalFreshT
  , execFreshT

  -- * Fresh name generation
  , FreshState
  , nothingUsed

  , module Control.Monad
  , module Control.Monad.Fix
  , module Control.Monad.Trans

  ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans

import Control.Monad.Fresh.Class
import Control.Monad.Trans.FastFresh hiding (freshIdents)

