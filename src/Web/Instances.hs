{- |
Module      :  Web.Instances
Description :  Binary instances for making the server state persistent.
Copyright   :  (c) 2011, 2012 Benedikt Schmidt & Simon Meier
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}

{-# LANGUAGE TemplateHaskell, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Web.Instances where

import           Data.Binary
import           Data.DeriveTH

import           Control.DeepSeq
import           Data.Fixed
import           Data.Time.Calendar
import           Data.Time.LocalTime
import           Web.Types
-- import           Theory

-- $( derive makeBinary ''DiffTheory)
-- $( derive makeBinary ''ClosedDiffTheory)
-- $( derive makeBinary ''ClosedDiffTheory)
$( derive makeBinary ''TheoryOrigin)
$( derive makeBinary ''TheoryInfo)
$( derive makeBinary ''DiffTheoryInfo)
$( derive makeBinary ''EitherTheoryInfo)

$( derive makeBinary ''TimeZone)
$( derive makeBinary ''Day)
$( derive makeBinary ''TimeOfDay)

instance HasResolution a => Binary (Fixed a) where
  put f = put (showFixed True f)
  -- Fixed constructor is private
  get = do
    s <- get
    -- round to seconds for now
    return . fromInteger . read $ takeWhile (/='.') s

$( derive makeBinary ''LocalTime)
$( derive makeBinary ''ZonedTime)

$( derive makeNFData ''TheoryOrigin)
