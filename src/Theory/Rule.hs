{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, TupleSections, TypeOperators, FlexibleInstances, FlexibleContexts, TypeSynonymInstances #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Rewriting rules representing protocol execution and intruder deduction. Once
-- modulo the full Diffie-Hellman equational theory and once modulo AC.
module Theory.Rule (
  -- * General Rules
    Rule(..)

  -- ** Accessors
  , rInfo
  , rPrems
  , rConcs
  , rActs
  , rPrem
  , rConc
  , rAct
  , lookupPrem
  , lookupConc

  -- ** Genereal protocol and intruder rules
  , RuleInfo(..)
  , ruleInfo

  -- * Protocol Rule Information
  , ProtoRuleName(..)
  , ProtoRuleACInfo(..)
  , RuleACConstrs

  -- * Intruder Rule Information
  , IntrRuleACInfo(..)
  
  -- * Concrete Rules
  , ProtoRuleE
  , ProtoRuleAC
  , IntrRuleAC
  , RuleAC
  , RuleACInst

  -- ** Queries
  , HasRuleName(..)
  , isDestrRule
  , isConstrRule
  , isFreshRule
  , isIRecvRule
  , isISendRule
  , isCoerceRule
  , nfRule
  , isTrivialProtoRuleAC

  -- ** Conversion
  , ruleACToIntrRuleAC
  , ruleACIntrToRuleAC

  -- ** Construction
  , someRuleACInst

  -- ** Unification
  , unifyRuleACInstEqs

  -- * Pretty-Printing
  , showRuleCaseName
  , prettyProtoRuleName
  , prettyRuleName
  , prettyProtoRuleE
  , prettyProtoRuleAC
  , prettyIntrRuleAC
  , prettyIntrRuleACInfo
  , prettyRuleAC
  , prettyRuleACInst

  -- * Convenience exports
  , module Theory.Fact

  )  where

import           Prelude hiding ( (.), id )

import           Safe
import           Data.List
import           Data.Monoid
import           Data.Foldable (foldMap)
import           Data.Generics 
import           Data.DeriveTH
import           Data.Binary

import           Control.DeepSeq
import           Control.Category
import           Control.Basics
import           Control.Monad.Bind
import           Control.Monad.Reader

import           Extension.Data.Label hiding (get)
import qualified Extension.Data.Label as L
import           Logic.Connectives

import           Theory.Fact
import           Theory.Pretty
import           Term.Rewriting.Norm

------------------------------------------------------------------------------
-- General Rule
------------------------------------------------------------------------------

-- | Rewriting rules with arbitrary additional information and facts with names
-- and logical variables.
data Rule i = Rule {
         _rInfo  :: i
       , _rPrems :: [LNFact]
       , _rConcs :: [LNFact]
       , _rActs  :: [LNFact]
       }
       deriving( Eq, Ord, Show, Data, Typeable )

$(mkLabels [''Rule])

-- | @lookupPrem i ru@ returns the @i@-th premise of rule @ru@, if possible.
lookupPrem :: Int -> Rule i -> Maybe LNFact
lookupPrem i = (`atMay` i) . L.get rPrems

-- | @lookupConc i ru@ returns the @i@-th conclusion of rule @ru@, if possible.
lookupConc :: Int -> Rule i -> Maybe LNFact
lookupConc i = (`atMay` i) . L.get rConcs

-- | @rPrem i@ is a lens for the @i@-th premise of a rule.
rPrem :: Int -> (Rule i :-> LNFact)
rPrem i = nthL i . rPrems

-- | @rConc i@ is a lens for the @i@-th conclusion of a rule.
rConc :: Int -> (Rule i :-> LNFact)
rConc i = nthL i . rConcs

-- | @rAct i@ is a lens for the @i@-th action of a rule.
rAct :: Int -> (Rule i :-> LNFact)
rAct i = nthL i . rActs

-- Instances
------------

instance Functor Rule where
    fmap f (Rule i ps cs as) = Rule (f i) ps cs as

instance HasFrees i => HasFrees (Rule i) where
    foldFrees f (Rule i ps cs as) = 
        (foldFrees f i  `mappend`) $ 
        (foldFrees f ps `mappend`) $
        (foldFrees f cs `mappend`) $
        (foldFrees f as)

    mapFrees f (Rule i ps cs as) =
        Rule <$> mapFrees f i 
             <*> mapFrees f ps <*> mapFrees f cs <*> mapFrees f as

instance Apply i => Apply (Rule i) where
    apply subst (Rule i ps cs as) = 
        Rule (apply subst i) (apply subst ps) (apply subst cs) (apply subst as)

instance Sized (Rule i) where
  size (Rule _ ps cs as) = size ps + size cs + size as

------------------------------------------------------------------------------
-- Rule information split into intruder rule and protocol rules
------------------------------------------------------------------------------

-- | Rule information for protocol and intruder rules.
data RuleInfo p i = 
         ProtoInfo p
       | IntrInfo i 
       deriving( Eq, Ord, Show )

-- | @ruleInfo proto intr@ maps the protocol information with @proto@ and the
-- intruder information with @intr@.
ruleInfo :: (p -> c) -> (i -> c) -> RuleInfo p i -> c
ruleInfo proto _    (ProtoInfo x) = proto x
ruleInfo _     intr (IntrInfo  x) = intr x


-- Instances
------------

instance (HasFrees p, HasFrees i) => HasFrees (RuleInfo p i) where
    foldFrees  f = ruleInfo (foldFrees f) (foldFrees f)

    mapFrees   f = ruleInfo (fmap ProtoInfo . mapFrees   f) 
                            (fmap IntrInfo . mapFrees   f)

instance (Apply p, Apply i) => Apply (RuleInfo p i) where
    apply subst = ruleInfo (ProtoInfo . apply subst) (IntrInfo . apply subst)


------------------------------------------------------------------------------
-- Protocol Rule Information
------------------------------------------------------------------------------

-- | A name of a protocol rule is either one of the special reserved rules or
-- some standard rule.
data ProtoRuleName = 
       -- FIXME: Consider also moving them to intruder/model rules.
         FreshRule
       | IRecvRule
       | ISendRule
       | StandRule String -- ^ Some standard protocol rule
       deriving( Eq, Ord, Show, Data, Typeable )


-- | Information for protocol rules modulo AC. The variants list the possible
-- instantiations of the free variables of the rule. The typing is interpreted
-- modulo AC; i.e., its variants were also built.
data ProtoRuleACInfo = ProtoRuleACInfo
       { pracName     :: ProtoRuleName
       , pracVariants :: Disj (LNSubstVFresh)
       }
       deriving( Eq, Ord, Show )


-- Instances
------------

instance Apply ProtoRuleName where
    apply _ = id

instance HasFrees ProtoRuleName where
    foldFrees  _ = const mempty
    mapFrees   _ = pure


instance HasFrees ProtoRuleACInfo where
    foldFrees f (ProtoRuleACInfo na vari) =
        foldFrees f na `mappend` foldFrees f vari
    
    mapFrees f (ProtoRuleACInfo na vari) = 
        ProtoRuleACInfo na <$> mapFrees f vari


------------------------------------------------------------------------------
-- Intruder Rule Information
------------------------------------------------------------------------------

-- | An intruder rule modulo AC is described by its name.
data IntrRuleACInfo = IntrApp String | CoerceRule
  deriving( Ord, Eq, Show, Data, Typeable )

-- | An intruder rule modulo AC.
type IntrRuleAC = Rule IntrRuleACInfo

-- | Converts between these two types of rules, if possible.
ruleACToIntrRuleAC :: RuleAC -> Maybe IntrRuleAC
ruleACToIntrRuleAC (Rule (IntrInfo i) ps cs as) = Just (Rule i ps cs as)
ruleACToIntrRuleAC _                            = Nothing

-- | Converts between these two types of rules.
ruleACIntrToRuleAC :: IntrRuleAC -> RuleAC
ruleACIntrToRuleAC (Rule ri ps cs as) = Rule (IntrInfo ri) ps cs as

-- Instances
------------

instance Apply IntrRuleACInfo where
    apply _ = id

instance HasFrees IntrRuleACInfo where
    foldFrees _ = const mempty
    mapFrees _  = pure


------------------------------------------------------------------------------
-- Concrete rules
------------------------------------------------------------------------------

-- | A rule modulo E is always a protocol rule. Intruder rules are specified
-- abstractly by their operations generating them and are only available once
-- their variants are built.
type ProtoRuleE  = Rule ProtoRuleName

-- | A protocol rule modulo AC.
type ProtoRuleAC = Rule ProtoRuleACInfo

-- | A rule modulo AC is either a protocol rule or an intruder rule
type RuleAC      = Rule (RuleInfo ProtoRuleACInfo IntrRuleACInfo)

-- | A rule instance module AC is either a protocol rule or an intruder rule.
-- The info identifies the corresponding rule modulo AC that the instance was
-- derived from.
type RuleACInst  = Rule (RuleInfo ProtoRuleName IntrRuleACInfo)

-- Accessing the rule name
--------------------------

-- | Types that have an associated name.
class HasRuleName t where
  ruleName :: t -> RuleInfo ProtoRuleName IntrRuleACInfo

instance HasRuleName ProtoRuleE where
  ruleName = ProtoInfo . L.get rInfo

instance HasRuleName RuleAC where
  ruleName = ruleInfo (ProtoInfo . pracName) IntrInfo . L.get rInfo

instance HasRuleName ProtoRuleAC where
  ruleName = ProtoInfo . pracName . L.get rInfo

instance HasRuleName IntrRuleAC where
  ruleName = IntrInfo . L.get rInfo

instance HasRuleName RuleACInst where
  ruleName = L.get rInfo


-- Queries
----------

-- | True iff the rule is a destruction rule.
isDestrRule :: Rule r -> Bool
isDestrRule ru = case kFactView <$> L.get rConcs ru of
    [Just (DnK, _, _)] -> True
    _                  -> False

-- | True iff the rule is a construction rule.
isConstrRule :: Rule r -> Bool
isConstrRule ru = case kFactView <$> L.get rConcs ru of
    [Just (UpK, _, _)] -> True
    _                  -> False

-- | True iff the rule is the special fresh rule.
isFreshRule :: HasRuleName r => r -> Bool
isFreshRule = (ProtoInfo FreshRule ==) . ruleName

-- | True iff the rule is the special learn rule.
isIRecvRule :: HasRuleName r => r -> Bool
isIRecvRule = (ProtoInfo IRecvRule ==) . ruleName

-- | True iff the rule is the special knows rule.
isISendRule :: HasRuleName r => r -> Bool
isISendRule = (ProtoInfo ISendRule ==) . ruleName

-- | True iff the rule is the special coerce rule.
isCoerceRule :: HasRuleName r => r -> Bool
isCoerceRule = (IntrInfo CoerceRule ==) . ruleName

-- | True if the messages in premises and conclusions are in normal form
nfRule :: Rule i -> WithMaude Bool
nfRule (Rule _ ps cs as) = reader $ \hnd ->
    all (nfFactList hnd) [ps, cs, as]
  where
    nfFactList hnd xs = 
        getAll $ foldMap (foldMap (All . (\t -> nf' t `runReader` hnd))) xs

-- | True if the protocol rule has no variants.
isTrivialProtoRuleAC :: ProtoRuleAC -> Bool
isTrivialProtoRuleAC (Rule info _ _ _) =
    pracVariants info == Disj [emptySubstVFresh]


-- Construction
---------------

type RuleACConstrs = Disj (LNSubstVFresh)

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given typing and variants also need to handled.
someRuleACInst :: MonadFresh m 
               => RuleAC 
               -> m (RuleACInst, Maybe RuleACConstrs)
someRuleACInst = 
    (`evalBindT` noBindings) . fmap extractInsts . someInst
  where
    extractInsts (Rule (ProtoInfo i) ps cs as) = 
      ( Rule (ProtoInfo (pracName i)) ps cs as
      , Just (pracVariants i)
      )
    extractInsts (Rule (IntrInfo i) ps cs as) = 
      ( Rule (IntrInfo i) ps cs as, Nothing )


-- Unification
--------------

-- | Unify a list of @RuleACInst@ equalities.
unifyRuleACInstEqs :: [Equal RuleACInst] -> WithMaude [LNSubstVFresh]
unifyRuleACInstEqs eqs 
  | all unifiable eqs = unifyLNFactEqs $ concatMap ruleEqs eqs
  | otherwise         = return []
  where
    unifiable (Equal ru1 ru2) = 
         L.get rInfo ru1            == L.get rInfo ru2
      && length (L.get rPrems ru1) == length (L.get rPrems ru2)
      && length (L.get rConcs ru1) == length (L.get rConcs ru2)

    ruleEqs (Equal ru1 ru2) = 
        zipWith Equal (L.get rPrems ru1) (L.get rPrems ru2) ++ 
        zipWith Equal (L.get rConcs ru1) (L.get rConcs ru2)



------------------------------------------------------------------------------
-- Fact analysis
------------------------------------------------------------------------------

-- | Globally unique facts.
--
-- A rule instance removes a fact fa if fa is in the rule's premise but not
-- in the rule's conclusion.
--
-- A fact symbol fa is globally fresh with respect to a dependency graph if
-- there are no two rule instances that remove the same fact built from fa.
--
-- We are looking for sufficient criterion to prove that a fact symbol is
-- globally fresh.
--
-- The Fr symbol is globally fresh by construction.
--
-- We have to track every creation of a globally fresh fact to a Fr fact.
--
-- (And show that the equality of of the created fact implies the equality of
-- the corresponding fresh facts. Ignore this for now by assuming that no
-- duplication happens.)
--
-- (fa(x1), fr(y1)), (fa(x2), fr(y2)) : x2 = x1 ==> y1 == y2
--
-- And ensure that every duplication is non-unifiable.
--
-- A Fr fact is described 
--
-- We track which symbols are not globally fresh.
--
-- All persistent facts are not globally fresh.
--
-- Adding a rule ru.
--   All fact symbols that occur twice in the conclusion
--
-- For simplicity: globally fresh fact symbols occur at most once in premise
--   and conclusion of a rule.
-- 
-- A fact is removed by a rule if it occurs in the rules premise
--   1. but doesn't occur in the rule's conclusion
--   2. or does occur but non-unifiable.
--
-- We want a sufficient criterion to prove that a fact is globally unique.
--
--

------------------------------------------------------------------------------
-- Pretty-Printing
------------------------------------------------------------------------------

prettyProtoRuleName :: Document d => ProtoRuleName -> d
prettyProtoRuleName rn = text $ case rn of
    FreshRule  -> "Fresh"
    IRecvRule  -> "IRecv"
    ISendRule  -> "ISend"
    StandRule n 
      | n `elem` ["Fresh", "IRecv", "ISend"] -> "_" ++ n
      | "_" `isPrefixOf` n                   -> "_" ++ n
      | otherwise                            ->        n

prettyRuleName :: (HighlightDocument d, HasRuleName (Rule i)) => Rule i -> d
prettyRuleName = ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName

-- | Pretty print the rule name such that it can be used as a case name
showRuleCaseName :: HasRuleName (Rule i) => Rule i -> String
showRuleCaseName = 
    render . ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName

prettyIntrRuleACInfo :: Document d => IntrRuleACInfo -> d
prettyIntrRuleACInfo (IntrApp name) = text $ name
prettyIntrRuleACInfo CoerceRule     = text "coerce"

prettyNamedRule :: (HighlightDocument d, HasRuleName (Rule i))
                => d           -- ^ Prefix.
                -> (i -> d)    -- ^ Rule info pretty printing.
                -> Rule i -> d
prettyNamedRule prefix ppInfo ru =
    prefix <-> prettyRuleName ru <> colon $-$
    nest 2 (sep [ nest 1 $ ppFactsList rPrems
                , if null (L.get rActs ru) 
                    then operator_ "-->"
                    else fsep [operator_ "--[", ppFacts rActs, operator_ "]->"]
                , nest 1 $ ppFactsList rConcs]) $--$
    nest 2 (ppInfo $ L.get rInfo ru)
  where
    ppList pp        = fsep . punctuate comma . map pp
    ppFacts proj     = ppList prettyLNFact $ L.get proj ru
    ppFactsList proj = fsep [operator_ "[", ppFacts proj, operator_ "]"]

prettyProtoRuleACInfo :: HighlightDocument d => ProtoRuleACInfo -> d
prettyProtoRuleACInfo i =
    (ppVariants $ pracVariants i)
  where
    ppVariants (Disj [subst]) | subst == emptySubstVFresh = emptyDoc
    ppVariants substs = kwVariantsModulo "AC" $-$ prettyDisjLNSubstsVFresh substs

prettyProtoRuleE :: HighlightDocument d => ProtoRuleE -> d
prettyProtoRuleE = prettyNamedRule (kwRuleModulo "E") (const emptyDoc)

prettyRuleAC :: HighlightDocument d => RuleAC -> d
prettyRuleAC = 
    prettyNamedRule (kwRuleModulo "AC") 
        (ruleInfo prettyProtoRuleACInfo (const emptyDoc))

prettyIntrRuleAC :: HighlightDocument d => IntrRuleAC -> d
prettyIntrRuleAC = prettyNamedRule (kwRuleModulo "AC") (const emptyDoc)

prettyProtoRuleAC :: HighlightDocument d => ProtoRuleAC -> d
prettyProtoRuleAC = prettyNamedRule (kwRuleModulo "AC") prettyProtoRuleACInfo

prettyRuleACInst :: HighlightDocument d => RuleACInst -> d
prettyRuleACInst = prettyNamedRule (kwInstanceModulo "AC") (const emptyDoc)

-- derived instances
--------------------

$( derive makeBinary ''Rule)
$( derive makeBinary ''ProtoRuleName)
$( derive makeBinary ''ProtoRuleACInfo)
$( derive makeBinary ''RuleInfo)
$( derive makeBinary ''IntrRuleACInfo)

$( derive makeNFData ''Rule)
$( derive makeNFData ''ProtoRuleName)
$( derive makeNFData ''ProtoRuleACInfo)
$( derive makeNFData ''RuleInfo)
$( derive makeNFData ''IntrRuleACInfo)
