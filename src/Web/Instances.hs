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

$( derive makeNFData ''TheoryOrigin)
