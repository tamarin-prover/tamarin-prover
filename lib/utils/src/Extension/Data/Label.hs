{-# LANGUAGE TypeOperators #-}
-- |
-- Copyright   : (c) 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Extensions to the first-class labels (fclabels) package.
module Extension.Data.Label (
    nthL
  , fstL
  , sndL
  , module Data.Label

  -- * Labels and applicative functors
  , modA

  -- * Labels and Monads
  , askM
  , setM
  , getM
  , modM
  , (=:)
  ) where

import Data.Label
import Data.Label.Monadic ( (=:) )
import qualified Data.Label.Monadic as LM

import Control.Arrow (first, second)
-- import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Control.Monad.State (MonadState)
import Control.Monad.Reader (MonadReader)

-- | Lens for the first element of a tuple.
fstL :: ((a, b) :-> a)
fstL = lens fst first

-- | Lens for the second element of a tuple.
sndL :: ((a, b) :-> b)
sndL = lens snd second

-- | Lens for the nth element of the list.
nthL :: Int -> ([a] :-> a)
nthL i = lens (!! i) updateAt
  where
    updateAt f xs
      | 0 <= i && i < length xs = case splitAt i xs of
          (prefix, x:suffix) -> prefix ++ (f x:suffix)
          _                  -> error "nthL: impossible"
      | otherwise = error $ "nthL: index " ++ show i ++ " out of range"

-- | Effectful modification of a labeled value.
modA :: Applicative f => (a :-> b) -> (b -> f b) -> a -> f a
modA l f a = set l <$> f (get l a) <*> pure a

-- | Get part of the state from a reader.
askM :: MonadReader r m => (r :-> a) -> m a
askM = LM.asks

-- | Set some part of the state.
setM :: MonadState s m => (s :-> a) -> a -> m ()
setM = LM.puts

-- | Get some part of the state.
getM :: MonadState s m => (s :-> a) -> m a
getM = LM.gets

-- | Modify some part of the state.
modM :: MonadState s m => (s :-> a) -> (a -> a) -> m ()
modM = LM.modify
