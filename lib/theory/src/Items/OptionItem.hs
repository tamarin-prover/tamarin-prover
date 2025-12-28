{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Items.OptionItem (
    Option(..)
    ,module Items.OptionItem
) where
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import qualified Data.Set as S
import Optics.TH (makeFieldLabelsNoPrefix)
import Theory.Model.Fact

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------
-- | Options for translation and, maybe in the future, also msrs itself.
-- | Note: setOption below assumes all values to be boolean
data Option = Option
        {
          verboseOption                     :: Bool
        , precomputationOnlyOption          :: Bool
        , transAllowPatternMatchinginLookup :: Bool
        , transProgress                     :: Bool
        , transReliable                     :: Bool
        , transReport                       :: Bool
        , stateChannelOpt                   :: Bool
        , asynchronousChannels              :: Bool
        , compressEvents                    :: Bool
        , deductionChainCheck               :: Bool
        , forcedInjectiveFacts              :: S.Set FactTag
        , lemmasToProve                     :: [String]
        , openChainsLimit                   :: Integer
        , saturationLimit                   :: Integer
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
makeFieldLabelsNoPrefix ''Option
-- generate accessors for Option data structure records
