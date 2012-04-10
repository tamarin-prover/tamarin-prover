{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Copyright   : (c) 2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Provide NFData instance for ByteString
module Extension.Data.ByteString (
  ) where

import qualified Data.ByteString as B
import Control.DeepSeq

instance NFData B.ByteString