{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Items.ExportInfo (
    module Items.ExportInfo
) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Label as L ( mkLabels )

data ExportInfo = ExportInfo
        { _eTag            :: String
        , _eText           :: String
         }
         deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''ExportInfo])
