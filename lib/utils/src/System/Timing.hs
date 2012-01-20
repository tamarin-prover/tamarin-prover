-- | A simple module for timing IO action.
module System.Timing (
    timed
  , timed_
) where

import Control.Monad
import Data.Time.Clock

-- | Execute an IO action and return its result plus the time it took to execute it.
timed :: IO a -> IO (a, NominalDiffTime)
timed io = do
  t0 <- getCurrentTime
  x <- io
  t1 <- getCurrentTime
  return (x, diffUTCTime t1 t0)

-- | Execute an IO action and return the time it took to execute it.
timed_ :: IO a -> IO NominalDiffTime
timed_ = (snd `liftM`) . timed
