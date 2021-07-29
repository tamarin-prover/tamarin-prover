{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveAnyClass        #-}
module Theory.Module (
      ModuleType (..)
    , description
)
where

import GHC.Generics (Generic)
import Control.DeepSeq ( NFData )
import Data.Binary ( Binary )
import Data.Data ( Data )

data ModuleType = ModuleSpthy | ModuleSpthyTyped | ModuleMsr | ModuleProVerif | ModuleDeepSec
  deriving (Eq, Ord, Enum, Bounded, Generic, Data, NFData, Binary)
instance Show ModuleType where
    show ModuleSpthy = "spthy"
    show ModuleSpthyTyped ="spthytyped"
    show ModuleMsr ="msr"
    show ModuleProVerif ="proverif"
    show ModuleDeepSec ="deepsec"

description :: ModuleType -> String
description ModuleSpthy = "spthy (including Sapic Processes)"
description ModuleSpthyTyped ="spthy with explicit types inferred"
description ModuleMsr ="pure msrs (with Sapic translation)"
description ModuleProVerif ="ProVerif"
description ModuleDeepSec ="DeepSec"
