{-# LANGUAGE TypeOperators, StandaloneDeriving, DeriveDataTypeable, TemplateHaskell #-}
{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
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
  , InductionHint(..)

  , pcSignature
  , pcRules
  , pcCaseDists
  , pcCaseDistKind
  , pcUseInduction
  , pcTraceQuantifier
  , pcMaudeHandle

  -- ** Classified rules
  , ClassifiedRules(..)
  , emptyClassifiedRules
  , crConstruct
  , crDestruct
  , crProtocol
  , joinAllRules
  , nonSilentRules

  -- * Goals
  , Goal(..)
  , isActionGoal
  , isStandardActionGoal
  , isPremiseGoal
  , isPremDnKGoal
  , isChainGoal
  , isSplitGoal
  , isDisjGoal

  , prettyGoal

  -- * Precomputed case distinctions.
  , CaseDistinction(..)

  , cdGoal
  , cdCases

  ) where

import           Prelude                          hiding ( (.), id )

import           Data.Binary
import           Data.DeriveTH
import           Data.Label                       hiding (get)
import qualified Data.Label                       as L
import           Data.Monoid                      (Monoid(..))

import           Control.Basics
import           Control.Category
import           Control.DeepSeq

import           Text.PrettyPrint.Class

import           Logic.Connectives

import           Theory.Constraint.System
import           Theory.Model
import           Theory.Text.Pretty


------------------------------------------------------------------------------
-- Goals
------------------------------------------------------------------------------

-- | A 'Goal' denotes that a constraint reduction rule is applicable, which
-- might result in case splits. We either use a heuristic to decide what goal
-- to solve next or leave the choice to user (in case of the interactive UI).
data Goal =
       ActionG LVar LNFact
       -- ^ An action that must exist in the trace.
     | PremiseG NodePrem LNFact Bool
       -- ^ A premise that must have an incoming direct edge. The 'Bool'
       -- argument is 'True' if this premise is marked as a loop-breaker;
       -- i.e., if care must be taken to avoid solving such a premise too
       -- often.
     | PremDnKG NodePrem
       -- ^ A KD goal that must be solved using a destruction chain.
     | ChainG Chain
       -- A destruction chain that does not start from a message variable.
     | SplitG SplitId
       -- ^ A case split over equalities.
     | DisjG (Disj LNGuarded)
       -- ^ A case split over a disjunction.
     | ImplG LNGuarded
       -- ^ The consequent of a universally quantified clause that could be
       -- added to the sequent. For debugging mode only; currently commented
       -- out.
     deriving( Eq, Ord, Show )

-- | Pretty print a goal.
prettyGoal :: HighlightDocument d => Goal -> d
prettyGoal (ActionG i fa)          = prettyNAtom (Action (varTerm i) fa)
prettyGoal (ChainG ch)             = prettyChain ch
prettyGoal (PremiseG p fa mayLoop) =
    prettyNodePrem p <> brackets (prettyLNFact fa) <->
    (if mayLoop then comment_ "/* may loop */" else emptyDoc)
prettyGoal (PremDnKG p)            = text "KD" <> parens (prettyNodePrem p)
prettyGoal (ImplG gf)              =
    (text "Consequent" <>) $ nest 1 $ parens $ prettyGuarded gf
prettyGoal (DisjG (Disj gfs)) = (text "Disj" <>) $ fsep $
    punctuate (operator_ " |") (map (nest 1 . parens . prettyGuarded) gfs)
prettyGoal (SplitG x) =
    text "splitEqs" <> parens (text $ show (succ x))

-- Indicators
-------------

isActionGoal :: Goal -> Bool
isActionGoal (ActionG _ _) = True
isActionGoal _             = False

isStandardActionGoal :: Goal -> Bool
isStandardActionGoal (ActionG _ fa) = not (isKUFact fa)
isStandardActionGoal _              = False

isPremiseGoal :: Goal -> Bool
isPremiseGoal (PremiseG _ _ _) = True
isPremiseGoal _                = False

isPremDnKGoal :: Goal -> Bool
isPremDnKGoal (PremDnKG _) = True
isPremDnKGoal _            = False

isChainGoal :: Goal -> Bool
isChainGoal (ChainG _) = True
isChainGoal _          = False

isSplitGoal :: Goal -> Bool
isSplitGoal (SplitG _) = True
isSplitGoal _          = False

isDisjGoal :: Goal -> Bool
isDisjGoal (DisjG _) = True
isDisjGoal _         = False



-- Instances
------------

instance HasFrees Goal where
    foldFrees f goal = case goal of
        ActionG i fa          -> foldFrees f i `mappend` foldFrees f fa
        PremiseG p fa mayLoop -> foldFrees f p `mappend` foldFrees f fa `mappend` foldFrees f mayLoop
        PremDnKG p            -> foldFrees f p
        ChainG ch             -> foldFrees f ch
        SplitG i              -> foldFrees f i
        DisjG x               -> foldFrees f x
        ImplG x               -> foldFrees f x

    mapFrees f goal = case goal of
        ActionG i fa          -> ActionG  <$> mapFrees f i <*> mapFrees f fa
        PremiseG p fa mayLoop -> PremiseG <$> mapFrees f p <*> mapFrees f fa <*> mapFrees f mayLoop
        PremDnKG p            -> PremDnKG <$> mapFrees f p
        ChainG ch             -> ChainG   <$> mapFrees f ch
        SplitG i              -> SplitG   <$> mapFrees f i
        DisjG x               -> DisjG    <$> mapFrees f x
        ImplG x               -> ImplG    <$> mapFrees f x

instance Apply Goal where
    apply subst goal = case goal of
        ActionG i fa          -> ActionG  (apply subst i)     (apply subst fa)
        PremiseG p fa mayLoop -> PremiseG (apply subst p)     (apply subst fa) (apply subst mayLoop)
        PremDnKG p            -> PremDnKG (apply subst p)
        ChainG ch             -> ChainG   (apply subst ch)
        SplitG i              -> SplitG   (apply subst i)
        DisjG x               -> DisjG    (apply subst x)
        ImplG x               -> ImplG    (apply subst x)



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
       { _pcSignature       :: SignatureWithMaude
       , _pcRules           :: ClassifiedRules
       , _pcCaseDistKind    :: CaseDistKind
       , _pcCaseDists       :: [CaseDistinction]
       , _pcUseInduction    :: InductionHint
       , _pcTraceQuantifier :: SystemTraceQuantifier
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''ProofContext, ''CaseDistinction])


-- | The 'MaudeHandle' of a proof-context.
pcMaudeHandle :: ProofContext :-> MaudeHandle
pcMaudeHandle = sigmMaudeHandle . pcSignature

-- Instances
------------

instance HasFrees CaseDistinction where
    foldFrees f th =
        foldFrees f (L.get cdGoal th)   `mappend`
        foldFrees f (L.get cdCases th)

    mapFrees f th = CaseDistinction <$> mapFrees f (L.get cdGoal th)
                                    <*> mapFrees f (L.get cdCases th)


-- NFData
---------

$( derive makeBinary ''Goal)
$( derive makeBinary ''CaseDistinction)
$( derive makeBinary ''ClassifiedRules)
$( derive makeBinary ''InductionHint)

$( derive makeNFData ''Goal)
$( derive makeNFData ''CaseDistinction)
$( derive makeNFData ''ClassifiedRules)
$( derive makeNFData ''InductionHint)
