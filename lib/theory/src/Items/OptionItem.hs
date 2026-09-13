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
import Data.Label.Mono (Lens)
import Data.Label.Total (Total)
import qualified Data.Set as S
import Theory.Model.Fact

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------
-- | Options for translation and, maybe in the future, also msrs itself.
-- | Note: setOption below assumes all values to be boolean
data Option = Option
        {
          _verboseOption                     :: Bool
        , _precomputationOnlyOption          :: Bool
        , _transAllowPatternMatchinginLookup :: Bool
        , _transProgress                     :: Bool
        , _transReliable                     :: Bool
        , _transReport                       :: Bool
        , _stateChannelOpt                   :: Bool
        , _asynchronousChannels              :: Bool
        , _compressEvents                    :: Bool
        , _deductionChainCheck               :: Bool
        , _forcedInjectiveFacts              :: S.Set FactTag
        , _lemmasToProve                     :: [String]
        , _openChainsLimit                   :: Integer
        , _saturationLimit                   :: Integer
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )
$(mkLabels [''Option])
-- generate accessors for Option data structure records

-- | The options a theory file can set with the "options:" keyword, together
-- with the name they are written under. Read by both the parser and the
-- pretty-printer, so that every option that can be declared is also printed.
declarableOptions :: [(String, Lens Total Option Bool)]
declarableOptions =
    [ ("translation-progress", transProgress)
    , ("translation-allow-pattern-lookups", transAllowPatternMatchinginLookup)
    , ("translation-state-optimisation", stateChannelOpt)
    , ("translation-asynchronous-channels", asynchronousChannels)
    , ("translation-compress-events", compressEvents)
    ]
