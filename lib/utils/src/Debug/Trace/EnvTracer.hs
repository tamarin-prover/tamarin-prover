-- |
-- Copyright   : (c) 2024 Adrian Dapprich
-- License     : GPL v3 (see LICENSE)
-- 
--
-- Module for helper functions to generate debug traces.
-- Usage: DEBUG_TRACE=foo,bar tamarin-prover interactive <thy>
-- This will enable all debug traces with keys "foo" or "bar"
module Debug.Trace.EnvTracer (
    etraceSectionLn
  , etraceSectionLnM
  , etraceLn
  , etraceLnM
  ) where

import           Data.List.Split (splitOn)
import           System.IO.Unsafe (unsafePerformIO)
import           System.Environment (lookupEnv)
import qualified Debug.Trace as T

-- | Environment variable.
traceSettings :: String
traceSettings = "DEBUG_TRACE"

-- | Look up the `traceKey` in the `traceSettings` environment variable to check if a trace should be output.
shouldTrace :: String -> Bool
shouldTrace traceKey =
  -- justification for unsafePerformIO: The normal Debug.trace functions also use this so that they can be used from a pure context.
  let e = unsafePerformIO (lookupEnv traceSettings) in
  case e of
    Nothing -> False
    Just setting -> traceKey `elem` splitOn "," setting

-- | Output a trace title to separate different traces.
etraceSectionLn :: String -- ^ Key that assigns this trace to a "category" and will be checked against the global trace settings.
                -> String -- ^ Title of the trace section.
                -> b      -- ^ Normal arguments to trace.
                -> b    
etraceSectionLn traceKey title = 
  let fmt = "=== " ++ title ++ " " ++ replicate (80 - 5 - length title) '=' ++ "\n" in
  if shouldTrace traceKey
  then T.trace fmt
  else id

-- | Output a trace title to separate different traces inside an Applicative/Monad f.
etraceSectionLnM :: Applicative f 
                 => String        -- ^ Key that assigns this trace to a "category" and will be checked against the global trace settings.
                 -> String        -- ^ Title of the trace section.
                 -> f ()
etraceSectionLnM traceKey title = etraceSectionLn traceKey title $ pure ()

-- | Do a conditional debug trace.
etraceLn :: String -- ^ Key that assigns this trace to a "category" and will be checked against the global trace settings.
         -> String -- ^ Label for the trace output.
         -> String -- ^ The string to be traced.
         -> b      -- ^ Normal arguments to trace.
         -> b    
etraceLn traceKey label s =
  let fmt = label ++ ": " ++ s ++ "\n" in
  if shouldTrace traceKey
  then T.trace fmt
  else id

-- | Do a conditional debug trace inside an Applicative/Monad f.
etraceLnM :: Applicative f
          => String        -- ^ Key that assigns this trace to a "category" and will be checked against the global trace settings.
          -> String        -- ^ Label for the trace output.
          -> String        -- ^ The string to be traced.
          -> f ()
etraceLnM traceKey label s = etraceLn traceKey label s $ pure ()
  