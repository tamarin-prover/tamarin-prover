{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Common types for our constraint solver. They must be declared jointly
-- because there is a recursive dependency between goals, proof contexts, and
-- case distinctions.
module Theory.Constraint.Solver.Types (

  -- * Proof context
    ProofContext(..)
  , DiffProofContext(..)
  , InductionHint(..)

  , pcSignature
  , pcRules
  , pcInjectiveFactInsts
  , pcCaseDists
  , pcCaseDistKind
  , pcUseInduction
  , pcTraceQuantifier
  , pcMaudeHandle
  , dpcProtoRules
  , dpcDestrRules
  , dpcConstrRules

  -- ** Classified rules
  , ClassifiedRules(..)
  , emptyClassifiedRules
  , crConstruct
  , crDestruct
  , crProtocol
  , joinAllRules
  , nonSilentRules

  -- * Precomputed case distinctions.
  , CaseDistinction(..)

  , cdGoal
  , cdCases

  , Side(..)
  
  , prettyCaseDistinction

  ) where

import           Prelude                  hiding (id, (.))

import           Data.Binary
import           Data.DeriveTH
import           Data.Label               hiding (get)
import qualified Data.Label               as L
import           Data.Monoid              (Monoid(..))
import qualified Data.Set                 as S

import           Control.Basics
import           Control.Category
import           Control.DeepSeq

import           Logic.Connectives
import           Theory.Constraint.System
import           Theory.Text.Pretty
import           Theory.Model


----------------------------------------------------------------------
-- ClassifiedRules
----------------------------------------------------------------------

data ClassifiedRules = ClassifiedRules
     { _crProtocol      :: [RuleAC] -- all protocol rules
     , _crDestruct      :: [RuleAC] -- destruction rules
     , _crConstruct     :: [RuleAC] -- construction rules
     }
     deriving( Eq, Ord, Show )

$(mkLabels [''ClassifiedRules])

-- | The empty proof rule set.
emptyClassifiedRules :: ClassifiedRules
emptyClassifiedRules = ClassifiedRules [] [] []

-- | @joinAllRules rules@ computes the union of all rules classified in
-- @rules@.
joinAllRules :: ClassifiedRules -> [RuleAC]
joinAllRules (ClassifiedRules a b c) = a ++ b ++ c

-- | Extract all non-silent rules.
nonSilentRules :: ClassifiedRules -> [RuleAC]
nonSilentRules = filter (not . null . L.get rActs) . joinAllRules


------------------------------------------------------------------------------
-- Proof Context
------------------------------------------------------------------------------

-- | In the diff type, we have either the Left Hand Side or the Right Hand Side
data Side = LHS | RHS deriving(Show, Eq, Ord, Read)


-- | A big-step case distinction.
data CaseDistinction = CaseDistinction
     { _cdGoal     :: Goal   -- start goal of case distinction
       -- disjunction of named sequents with premise being solved; each name
       -- being the path of proof steps required to arrive at these cases
     , _cdCases    :: Disj ([String], System)
     }
     deriving( Eq, Ord, Show )

data InductionHint = UseInduction | AvoidInduction
       deriving( Eq, Ord, Show )

-- | A proof context contains the globally fresh facts, classified rewrite
-- rules and the corresponding precomputed premise case distinction theorems.
data ProofContext = ProofContext
       { _pcSignature          :: SignatureWithMaude
       , _pcRules              :: ClassifiedRules
       , _pcInjectiveFactInsts :: S.Set FactTag
       , _pcCaseDistKind       :: CaseDistKind
       , _pcCaseDists          :: [CaseDistinction]
       , _pcUseInduction       :: InductionHint
       , _pcTraceQuantifier    :: SystemTraceQuantifier
       }
       deriving( Eq, Ord, Show )

-- | A diff proof context contains the two proof contexts for either side
-- and all rules.
data DiffProofContext = DiffProofContext
       {
--          _dpcPCLeft            :: ProofContext
--        , _dpcPCRight           :: ProofContext
         _dpcProtoRules           :: [ProtoRuleE]
       , _dpcConstrRules          :: [RuleAC]
       , _dpcDestrRules           :: [RuleAC]
       }
       deriving( Eq, Ord, Show )

       
$(mkLabels [''ProofContext, ''DiffProofContext, ''CaseDistinction])


-- | The 'MaudeHandle' of a proof-context.
pcMaudeHandle :: ProofContext :-> MaudeHandle
pcMaudeHandle = sigmMaudeHandle . pcSignature

-- Instances
------------

instance HasFrees CaseDistinction where
    foldFrees f th =
        foldFrees f (L.get cdGoal th)   `mappend`
        foldFrees f (L.get cdCases th)

    foldFreesOcc  _ _ = const mempty

    mapFrees f th = CaseDistinction <$> mapFrees f (L.get cdGoal th)
                                    <*> mapFrees f (L.get cdCases th)

-- Pretty printing
------------------

-- | Pretty print a case distinction
prettyCaseDistinction :: HighlightDocument d => CaseDistinction -> d
prettyCaseDistinction th = vcat $
   [ prettyGoal $ L.get cdGoal th ]
   ++ map combine (zip [(1::Int)..] $ map snd . getDisj $ (L.get cdCases th))
  where
    combine (i, sys) = fsep [keyword_ ("Case " ++ show i) <> colon, nest 2 (prettySystem sys)]


-- NFData
---------

$( derive makeBinary ''Side)
$( derive makeBinary ''CaseDistinction)
$( derive makeBinary ''ClassifiedRules)
$( derive makeBinary ''InductionHint)

$( derive makeNFData ''Side)
$( derive makeNFData ''CaseDistinction)
$( derive makeNFData ''ClassifiedRules)
$( derive makeNFData ''InductionHint)
