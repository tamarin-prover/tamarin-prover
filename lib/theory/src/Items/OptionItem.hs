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
        , _lemmasToProve        :: [String]
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''Option])
-- generate accessors for Option data structure records