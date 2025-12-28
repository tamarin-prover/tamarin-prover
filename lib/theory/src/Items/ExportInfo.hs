{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Items.ExportInfo (
    module Items.ExportInfo
) where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Optics.TH (makeFieldLabelsNoPrefix)

data ExportInfo = ExportInfo
        { tag            :: String
        , text           :: String
         }
         deriving( Eq, Ord, Show, Generic, NFData, Binary )

makeFieldLabelsNoPrefix ''ExportInfo
