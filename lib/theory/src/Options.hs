
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Options (
    Option(..)
  ,  transAllowPatternMatchinginLookup   
  , transProgress            
  , transReliable            
  , transReport  
) where
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Label as L

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
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''Option])
-- generate accessors for Option data structure records