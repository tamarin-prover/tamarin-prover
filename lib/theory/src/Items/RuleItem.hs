{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Items.RuleItem (
    module Items.RuleItem
                      , ClosedRuleCache(..)
) where

import GHC.Generics
import Control.DeepSeq
import Data.Binary

import qualified Data.Set                            as S

import           Optics.TH (makeFieldLabelsNoPrefix)

import           Theory.Model
import           Theory.Proof
import           Theory.Tools.InjectiveFactInstances

------------------------------------------------------------------------------
-- Commented sets of rewriting rules
------------------------------------------------------------------------------

-- | A protocol rewriting rule modulo E together with its possible assertion
-- soundness proof.
-- Optionally, the variant(s) modulo AC can be present if they were loaded
-- or contain additional actions.
data OpenProtoRule = OpenProtoRule
       { ruleE  :: ProtoRuleE             -- original rule modulo E
       , ruleAC :: [ProtoRuleAC]          -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A diff protocol rewriting rule modulo E
-- Optionally, the left and right rules can be present if they were loaded
-- or contain additional actions.
data DiffProtoRule = DiffProtoRule
       { rule       :: ProtoRuleE         -- original rule with diff
       , leftRight  :: Maybe (OpenProtoRule, OpenProtoRule)
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
       { ruleE         :: ProtoRuleE      -- original rule modulo E
       , ruleAC        :: ProtoRuleAC     -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

type OpenRuleCache = [IntrRuleAC]

data ClosedRuleCache = ClosedRuleCache
       { rules               :: ClassifiedRules
       , rawSources          :: [Source]
       , refinedSources      :: [Source]
       , injectiveFactInsts  :: S.Set (FactTag, [[MonotonicBehaviour]])
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

makeFieldLabelsNoPrefix ''OpenProtoRule
makeFieldLabelsNoPrefix ''DiffProtoRule
makeFieldLabelsNoPrefix ''ClosedProtoRule
makeFieldLabelsNoPrefix ''ClosedRuleCache

instance HasRuleName OpenProtoRule where
    ruleName = ruleName . (.ruleE)

instance HasRuleName DiffProtoRule where
    ruleName = ruleName . (.rule)

instance HasRuleName ClosedProtoRule where
    ruleName = ruleName . (.ruleAC)
