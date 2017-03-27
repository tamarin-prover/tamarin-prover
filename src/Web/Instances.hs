{- |
Module      :  Web.Instances
Description :  Binary instances for making the server state persistent.
Copyright   :  (c) 2011, 2012 Benedikt Schmidt & Simon Meier
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}

{-# LANGUAGE TemplateHaskell, GADTs, CPP, DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Web.Instances where

-- | Needed for GHC < 8.0
#if __GLASGOW_HASKELL__ < 800
import           Data.Binary
import           Data.Fixed

instance HasResolution a => Binary (Fixed a) where
  put f = put (showFixed True f)
  -- Fixed constructor is private
  get = do
    s <- get
    -- round to seconds for now
    return . fromInteger . read $ takeWhile (/='.') s
#endif
