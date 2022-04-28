{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
module Items.ProcessItem (
    module Items.ProcessItem
) where

import Theory.Sapic
import GHC.Generics
import Data.Binary (Binary)
import Data.Label as L
import           Control.DeepSeq

import           Prelude                             hiding (id, (.))

------------------------------------------------------------------------------
-- Processes
------------------------------------------------------------------------------

data ProcessDef = ProcessDef
        { _pName            :: String
        , _pBody            :: Process
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''ProcessDef])

-- generate accessors for ProcessDef data structure records