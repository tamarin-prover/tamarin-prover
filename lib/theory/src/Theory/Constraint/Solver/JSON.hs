-- these are all orphan instances on purpose -- we're serializing types we
-- don't own, hence -Wno-orphans.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- ToJSON instances for everything reachable from a System. This is the
-- rendering side of the proof-state store. The store itself is binary; JSON
-- is only an exported view and is never parsed back.
module Theory.Constraint.Solver.JSON () where

import           Data.Aeson       (ToJSON(..), ToJSONKey, object, (.=))
import qualified Data.ByteString as BS

import           Theory.Constraint.Solver
import           Theory.Model

instance ToJSON   ProofMethod
instance ToJSON   Result
instance ToJSON   Contradiction
instance ToJSON   System
instance ToJSON   (Guarded (String, LSort) Name LVar)
instance ToJSON   LVar
instance ToJSON   Goal
instance ToJSON   LSort
instance ToJSON   (Term (Lit Name LVar))
instance ToJSON   (Fact LNTerm)
instance ToJSON   (Lit Name LVar)
instance ToJSON   Name
instance ToJSON   FunSym
instance ToJSON   FactTag
instance ToJSON   FactAnnotation
instance ToJSON   NameTag
instance ToJSON   Multiplicity
instance ToJSON   CSym
instance ToJSON   NameId
instance ToJSON   ACSym
instance ToJSON   Constructability
instance ToJSON   Privacy
instance ToJSON   NDCstate
instance ToJSON   (ProtoAtom Unit2 (VTerm Name (BVar LVar)))
instance ToJSON   (BVar LVar)
instance ToJSON   (Term (Lit Name (BVar LVar)))
instance ToJSON   (Lit Name (BVar LVar))
instance ToJSON   (Unit2 (VTerm Name (BVar LVar)))
instance ToJSON   (Rule (RuleInfo ProtoRuleACInstInfo IntrRuleACInfo))
instance ToJSON   (RuleInfo ProtoRuleACInstInfo IntrRuleACInfo)
instance ToJSON   ProtoRuleACInstInfo
instance ToJSON   IntrRuleACInfo
instance ToJSON   ProtoRuleName
instance ToJSON   Edge
instance ToJSON   GoalStatus
instance ToJSON   SourceKind
instance ToJSON   EqStore
instance ToJSON   LessAtom
instance ToJSON   SubtermStore
instance ToJSON   (Fact (Term (Lit Name (BVar LVar))))
instance ToJSON   Quantifier
instance ToJSON   Reason
instance ToJSONKey   LVar
instance ToJSONKey   Goal

instance ToJSON   a => ToJSON   (Disj a) where toJSON = toJSON . getDisj
instance ToJSON   a => ToJSON   (Conj a) where toJSON = toJSON . getConj
instance ToJSON   ConcIdx where toJSON = toJSON . getConcIdx
instance ToJSON   PremIdx where toJSON = toJSON . getPremIdx
instance ToJSON   SplitId where toJSON = toJSON . unSplitId
instance {-# OVERLAPPING #-} ToJSON   BS.ByteString where toJSON = toJSON . BS.unpack
instance ToJSON   (Subst Name LVar) where toJSON = toJSON . sMap
instance ToJSON   (SubstVFresh Name LVar) where toJSON = toJSON . svMap
instance ToJSON RuleAttributes where
  toJSON (RuleAttributes _ _ idc sap rl) = object ["ignoreDerivChecks" .= idc, "isSAPiCRule" .= sap, "role" .= rl]
