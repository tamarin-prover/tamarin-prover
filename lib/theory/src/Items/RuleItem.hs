{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Items.RuleItem (
    module Items.RuleItem
) where

import GHC.Generics
import Control.DeepSeq
import Data.Binary

import           Prelude                             hiding (id, (.))


import qualified Data.Set                            as S

import           Control.Category
import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L

import           Theory.Model
import           Theory.Proof

------------------------------------------------------------------------------
-- Commented sets of rewriting rules
------------------------------------------------------------------------------

-- | A protocol rewriting rule modulo E together with its possible assertion
-- soundness proof.
-- Optionally, the variant(s) modulo AC can be present if they were loaded
-- or contain additional actions.
data OpenProtoRule = OpenProtoRule
       { _oprRuleE  :: ProtoRuleE             -- original rule modulo E
       , _oprRuleAC :: [ProtoRuleAC]          -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A diff protocol rewriting rule modulo E
-- Optionally, the left and right rules can be present if they were loaded
-- or contain additional actions.
data DiffProtoRule = DiffProtoRule
       { _dprRule       :: ProtoRuleE         -- original rule with diff
       , _dprLeftRight  :: Maybe (OpenProtoRule, OpenProtoRule)
                                              -- left and right instances
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A closed proto rule lists its original rule modulo E, the corresponding
-- variant(s) modulo AC, and if required the assertion soundness proof.
-- When using auto-sources, all non-trivial variants of a ClosedProtoRule are
-- split up into multiple ClosedProtoRules. Auto-sources also only adds
-- actions only to closed rules. Opening such rules keeps the AC rules s.t.
-- they can be exported.
data ClosedProtoRule = ClosedProtoRule
       { _cprRuleE         :: ProtoRuleE      -- original rule modulo E
       , _cprRuleAC        :: ProtoRuleAC     -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

type OpenRuleCache = [IntrRuleAC]

data ClosedRuleCache = ClosedRuleCache
       { _crcRules               :: ClassifiedRules
       , _crcRawSources          :: [Source]
       , _crcRefinedSources      :: [Source]
       , _crcInjectiveFactInsts  :: S.Set FactTag
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''OpenProtoRule, ''DiffProtoRule, ''ClosedProtoRule, ''ClosedRuleCache])

instance HasRuleName OpenProtoRule where
    ruleName = ruleName . L.get oprRuleE

instance HasRuleName DiffProtoRule where
    ruleName = ruleName . L.get dprRule

instance HasRuleName ClosedProtoRule where
    ruleName = ruleName . L.get cprRuleAC