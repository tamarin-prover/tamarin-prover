{- |
Module      :  Web.Instances
Description :  Binary instances for making the server state persistent.
Copyright   :  (c) 2011 Benedikt Schmidt
License     :  GPL-3

Stability   :  experimental
Portability :  non-portable
-}

{-# LANGUAGE TemplateHaskell, GADTs #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Web.Instances where

import Data.DeriveTH
import Data.Binary
import Control.Applicative

import Theory.Proof.Types
import Theory
import Web.Types
import Data.Time.Calendar
import Data.Time.LocalTime
import Data.Fixed
import Data.Set ()
import Data.Map ()
import Control.DeepSeq

$( derive makeBinary ''Term )
$( derive makeBinary ''Lit)
$( derive makeBinary ''ACSym)
$( derive makeBinary ''FunSym)
$( derive makeBinary ''LSort)
$( derive makeBinary ''LVar)
$( derive makeBinary ''BVar)

instance (Binary c, Binary v, Ord v) => Binary (Subst c v) where
  put (Subst m) = put m
  get = Subst <$> get

instance (Binary c, Binary v, Ord v) => Binary (SubstVFresh c v) where
  put (SubstVFresh m) = put m
  get = SubstVFresh <$> get

$( derive makeBinary ''Fact)
$( derive makeBinary ''Name)
$( derive makeBinary ''NameTag)
$( derive makeBinary ''NameId)
$( derive makeBinary ''Rule)
$( derive makeBinary ''Goal)
$( derive makeBinary ''Conj)
$( derive makeBinary ''Disj)
$( derive makeBinary ''Chain)
$( derive makeBinary ''MsgEdge)
$( derive makeBinary ''Edge)
$( derive makeBinary ''NodePrem)
$( derive makeBinary ''NodeConc)
$( derive makeBinary ''RuleInfo)
$( derive makeBinary ''IntrRuleACInfo)
$( derive makeBinary ''ProtoRuleName)
$( derive makeBinary ''Atom)
$( derive makeBinary ''Guarded)
$( derive makeBinary ''EqStore)
$( derive makeBinary ''CaseDistKind)
$( derive makeBinary ''Sequent)
$( derive makeBinary ''TheoryItem)
$( derive makeBinary ''Formula)
$( derive makeBinary ''Connective)
$( derive makeBinary ''Quantifier)
$( derive makeBinary ''LemmaAttribute)
$( derive makeBinary ''Lemma)
$( derive makeBinary ''ClosedRuleCache)
$( derive makeBinary ''Theory)
$( derive makeBinary ''ProofMethod)
$( derive makeBinary ''Contradiction)
$( derive makeBinary ''ProofStep)

instance (Ord l, Binary l, Binary a) => Binary (LTree l a) where
  put (LNode r m) = put r >> put m
  get = LNode <$> get <*> get

$( derive makeBinary ''CaseDistinction)
$( derive makeBinary ''ClassifiedRules)
$( derive makeBinary ''TheoryOrigin)
$( derive makeBinary ''ClosedProtoRule)
$( derive makeBinary ''BigStepGoal)
$( derive makeBinary ''ProtoRuleACInfo)
$( derive makeBinary ''TheoryInfo)

$( derive makeBinary ''TimeZone)
$( derive makeBinary ''Day)
$( derive makeBinary ''TimeOfDay)

instance HasResolution a => Binary (Fixed a) where
  put f = put (showFixed True f)
  -- Fixed constructor is private
  get = do
    s <- get
    -- round to seconds for now
    return . fromInteger . read $ takeWhile (/='.') s

$( derive makeBinary ''LocalTime)
$( derive makeBinary ''ZonedTime)

$( derive makeNFData ''Term )
$( derive makeNFData ''Lit)
$( derive makeNFData ''FunSym)
$( derive makeNFData ''ACSym)
$( derive makeNFData ''LSort)
$( derive makeNFData ''LVar)
$( derive makeNFData ''BVar)

instance (NFData c, NFData v, Ord v) => NFData (Subst c v) where
  rnf (Subst m) = rnf m

instance (NFData c, NFData v, Ord v) => NFData (SubstVFresh c v) where
  rnf (SubstVFresh m) = rnf m

$( derive makeNFData ''Fact)
$( derive makeNFData ''Name)
$( derive makeNFData ''NameTag)
$( derive makeNFData ''NameId)
$( derive makeNFData ''Rule)
$( derive makeNFData ''Goal)
$( derive makeNFData ''Conj)
$( derive makeNFData ''Disj)
$( derive makeNFData ''Chain)
$( derive makeNFData ''MsgEdge)
$( derive makeNFData ''Edge)
$( derive makeNFData ''NodePrem)
$( derive makeNFData ''NodeConc)
$( derive makeNFData ''RuleInfo)
$( derive makeNFData ''IntrRuleACInfo)
$( derive makeNFData ''ProtoRuleName)
$( derive makeNFData ''Atom)
$( derive makeNFData ''Guarded)
$( derive makeNFData ''EqStore)
$( derive makeNFData ''CaseDistKind)
$( derive makeNFData ''Sequent)
$( derive makeNFData ''TheoryItem)
$( derive makeNFData ''Formula)
$( derive makeNFData ''Connective)
$( derive makeNFData ''Quantifier)
$( derive makeNFData ''LemmaAttribute)
$( derive makeNFData ''Lemma)
$( derive makeNFData ''ClosedRuleCache)
$( derive makeNFData ''Theory)
$( derive makeNFData ''ProofMethod)
$( derive makeNFData ''Contradiction)
$( derive makeNFData ''ProofStep)

instance (Ord l, NFData l, NFData a) => NFData (LTree l a) where
  rnf (LNode r m) = rnf r `seq` rnf  m

$( derive makeNFData ''CaseDistinction)
$( derive makeNFData ''ClassifiedRules)
$( derive makeNFData ''TheoryOrigin)
$( derive makeNFData ''ClosedProtoRule)
$( derive makeNFData ''BigStepGoal)
$( derive makeNFData ''ProtoRuleACInfo)
