{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
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
        , _pBody            :: PlainProcess
        , _pVars            :: Maybe [SapicLVar]
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''ProcessDef])

-- generate accessors for ProcessDef data structure records