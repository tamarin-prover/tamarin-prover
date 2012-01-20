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
  , imageL
  , fstL
  , sndL
  , module Data.Label

  -- * Labels and applicative functors
  , liftLA
  , modA

  -- * Labels and Monads
  , askM
  , setM
  , getM
  , modM
  , (=:)
  ) where

import Data.Maybe (fromMaybe)
import qualified Data.Map as M

import Data.Label
import Data.Label.PureM ( (=:) )
import qualified Data.Label.PureM as LM

import Control.Arrow (first, second)
import Control.Applicative (Applicative, (<$>), (<*>), pure, liftA2)
import Control.Monad.State (MonadState)
import Control.Monad.Reader (MonadReader)

-- | Lens for the first element of a tuple.
fstL :: ((a, b) :-> a)
fstL = lens fst (first . const)

-- | Lens for the second element of a tuple.
sndL :: ((a, b) :-> b)
sndL = lens snd (second . const)

-- | Lens for the nth element of the list.
nthL :: Int -> ([a] :-> a)
nthL i = lens (!! i) updateAt
  where
    updateAt x xs
      | 0 <= i && i < length xs = case splitAt i xs of
          (prefix, _:suffix) -> prefix ++ (x:suffix)
          _                  -> error "nthL: impossible"
      | otherwise = error $ "nthL: index " ++ show i ++ " out of range"

-- | Lens for the element at a given position of a map.
imageL :: Ord k => k -> (M.Map k v :-> v)
imageL k = 
    lens (fromMaybe (error "imageL: element not found") . M.lookup k) 
         (M.insert k)

-- | Lift a label into an applicative functor.
liftLA :: Applicative f => (a :-> b) -> (f a :-> f b)
liftLA l = lens (get l <$>) (liftA2 (set l))

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
