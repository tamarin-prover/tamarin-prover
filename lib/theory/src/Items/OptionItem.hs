{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Items.OptionItem (
    Option(..)
    ,module Items.OptionItem
) where
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Label as L
import qualified Data.Set as S
import Theory.Model.Fact
import qualified Data.Map as Map

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------
-- | Options for translation and, maybe in the future, also msrs itself.
-- | Note: setOption below assumes all values to be boolean
data Option = Option
        {
          _transAllowPatternMatchinginLookup   :: Bool
        , _transProgress            :: Bool
        , _transReliable            :: Bool
        , _transReport            :: Bool
        , _stateChannelOpt            :: Bool
        , _asynchronousChannels       :: Bool
        , _compressEvents       :: Bool
        , _forcedInjectiveFacts :: S.Set FactTag
        , _thyParams               :: Map.Map String [String]  -- (Key,Value)
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''Option])
-- generate accessors for Option data structure records


-- | Options for diffTheory
data DiffOption = DiffOption
        {
          _diffThyParams          :: Map.Map String [String]  -- (Key,Value)
        , _diffFutureOptions      :: Bool --Temporary useless option 
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''DiffOption])
-- generate accessors for Option data structure records