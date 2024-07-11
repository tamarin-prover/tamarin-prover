-- |
-- Copyright   : (c) 2011 Simon Meier, 2022 Kevin Morio
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- A simple module for timing IO actions and evaluation of values.
module System.Timing (
    timedIO
  , timed
) where

import Data.Time.Clock ( diffUTCTime, getCurrentTime, NominalDiffTime )
import GHC.IO (unsafePerformIO)
import Control.DeepSeq ( NFData, deepseq )

-- | Fully evaluate an IO action and measure its execution time.
timedIO :: NFData a => IO a -> IO (a, NominalDiffTime)
timedIO mx = do
    t0 <- getCurrentTime
    val <- mx
    t1 <- val `deepseq` getCurrentTime
    let measure = t1 `diffUTCTime` t0
    return (val, measure)

-- | Fully evaluate a value and measure its execution time.
timed :: NFData a => a -> (a, NominalDiffTime)
timed x =
    let measure = unsafePerformIO $ do
                    t0 <- getCurrentTime
                    t1 <- x `deepseq` getCurrentTime
                    return (t1 `diffUTCTime` t0)
    in (x, measure)