{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Items.ProcessItem (
    module Items.ProcessItem
) where

import Theory.Sapic
import GHC.Generics
import Data.Binary (Binary)
import           Control.DeepSeq
import Optics.TH (makeFieldLabelsNoPrefix)

------------------------------------------------------------------------------
-- Processes
------------------------------------------------------------------------------

data ProcessDef = ProcessDef
        { name            :: String
        , body            :: PlainProcess
        , vars            :: Maybe [SapicLVar]
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )

makeFieldLabelsNoPrefix ''ProcessDef

-- generate accessors for ProcessDef data structure records
