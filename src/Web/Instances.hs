{- |
Module      :  Web.Instances
Description :  Binary instances for making the server state persistent.
Copyright   :  (c) 2011 Benedikt Schmidt
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}

{-# LANGUAGE TemplateHaskell, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Web.Instances where

import Data.DeriveTH
import Data.Binary

import Web.Types
import Data.Time.Calendar
import Data.Time.LocalTime
import Data.Fixed
import Data.Set ()
import Data.Map ()
import Control.DeepSeq

$( derive makeBinary ''TheoryOrigin)
$( derive makeBinary ''TheoryInfo)

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
