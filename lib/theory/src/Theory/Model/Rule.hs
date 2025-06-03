{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Rewriting rules representing protocol execution and intruder deduction. Once
-- modulo the full Diffie-Hellman equational theory and once modulo AC.
module Theory.Model.Rule (
  -- * General Rules
    Rule(..)
  , PremIdx(..)
  , ConcIdx(..)

  -- ** Accessors
  , rInfo
  , rPrems
  , rConcs
  , rActs
  , rPrem
  , rConc
  , rNewVars
  , lookupPrem
  , lookupConc
  , enumPrems
  , enumConcs

  -- ** Extended positions
  , ExtendedPosition
  , printPosition
  , printFactPosition

  -- ** Genereal protocol and intruder rules
  , RuleInfo(..)
  , ruleInfo

  -- * Protocol Rule Information
  , RuleAttribute(..)
  , ProtoRuleName(..)
  , ProtoRuleEInfo(..)
  , preName
  , preAttributes
  , preRestriction
  , ProtoRuleACInfo(..)
  , pracName
  , pracAttributes
  , pracVariants
  , pracLoopBreakers
  , ProtoRuleACInstInfo(..)
  , praciName
  , praciAttributes
  , praciLoopBreakers
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
  , HasRuleAttributes(..)
  , isIntruderRule
  , isDestrRule
  , isIEqualityRule
  , isConstrRule
  , isPubConstrRule
  , isNatConstrRule
  , isFreshRule
  , isIRecvRule
  , isISendRule
  , isCoerceRule
  , isProtocolRule
  , isConstantRule
  , isSubtermRule
  , containsNewVars
  , getRuleName
  , getRuleNameDiff
  , getRemainingRuleApplications
  , setRemainingRuleApplications
  , nfRule
  , normRule
  , isTrivialProtoVariantAC
  , getNewVariables
  , getSubstitutionsFixingNewVars
  , compareRulesUpToNewVars
  , equalUpToAddedActions
  , equalUpToTerms

  -- ** Conversion
  , ruleACToIntrRuleAC
  , ruleACIntrToRuleAC
  , ruleACIntrToRuleACInst
  , getLeftRule
  , getRightRule
  , constrRuleToDestrRule
  , destrRuleToConstrRule
  , destrRuleToDestrRule

  -- ** Construction
  , someRuleACInst
  , someRuleACInstAvoiding
  , someRuleACInstAvoidingFixing
  , someRuleACInstFixing
  , addDiffLabel
  , removeDiffLabel
  , multRuleInstance
  , unionRuleInstance
  , xorRuleInstance
  , addAction
  , applyMacroInRule

  -- ** Unification
  , unifyRuleACInstEqs
  , unifiableRuleACInsts
  , equalRuleUpToRenaming
  , equalRuleUpToAnnotations
  , equalRuleUpToDiffAnnotation
  , equalRuleUpToDiffAnnotationSym

  -- * Pretty-Printing
  , reservedRuleNames
  , showDotRuleCaseName
  , showRuleCaseName
  , prettyRule
  , prettyRuleRestrGen
  , prettyRuleRestr
  , prettyProtoRuleName
  , prettyRuleName
  , prettyRuleAttribute
  , prettyProtoRuleE
  , prettyProtoRuleAC
  , prettyProtoRuleACasE
  , prettyIntrRuleAC
  , prettyIntrRuleACInfo
  , prettyRuleAC
  , prettyLoopBreakers
  , prettyRuleACInst
  , prettyProtoRuleACInstInfo
  , prettyInstLoopBreakers

  , prettyIntruderVariants)  where

import           Prelude              hiding (id, (.))

import           GHC.Generics (Generic)
import           Data.Binary
import qualified Data.ByteString.Char8 as BC
-- import           Data.Foldable        (foldMap)
import           Data.Data
import           Data.List
import qualified Data.Set              as S
import qualified Data.Map              as M
import           Data.Monoid
-- import           Data.Maybe            (fromMaybe)
import           Data.Color
import           Safe

-- import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Bind
import           Control.Monad.Reader

import           Extension.Data.Label hiding (get)
import qualified Extension.Data.Label as L
import           Logic.Connectives

import           Term.LTerm
import           Term.Positions
import           Term.Macro
import           Term.Rewriting.Norm  (nf', norm')
import           Term.Builtin.Convenience (var)
import           Term.Unification
import           Theory.Model.Fact
import qualified Theory.Model.Formula as F
import           Theory.Text.Pretty
import           Theory.Sapic
import Data.Char (chr, isDigit)
import Data.List.Split (splitOn)

-- import           Debug.Trace

------------------------------------------------------------------------------
-- General Rule
------------------------------------------------------------------------------

-- | Rewriting rules with arbitrary additional information and facts with names
-- and logical variables.
data Rule i = Rule {
         _rInfo    :: i
       , _rPrems   :: [LNFact]
       , _rConcs   :: [LNFact]
       , _rActs    :: [LNFact]
       -- contains initially the new variables, then their instantiations
       , _rNewVars :: [LNTerm]
       }
       deriving(Eq, Ord, Show, Data, Typeable, Generic)

instance NFData i => NFData (Rule i)
instance Binary i => Binary (Rule i)

$(mkLabels [''Rule])

-- | An index of a premise. The first premise has index '0'.
newtype PremIdx = PremIdx { getPremIdx :: Int }
  deriving( Eq, Ord, Show, Enum, Data, Typeable, Binary, NFData )

-- | An index of a conclusion. The first conclusion has index '0'.
newtype ConcIdx = ConcIdx { getConcIdx :: Int }
  deriving( Eq, Ord, Show, Enum, Data, Typeable, Binary, NFData )

-- | @lookupPrem i ru@ returns the @i@-th premise of rule @ru@, if possible.
lookupPrem :: PremIdx -> Rule i -> Maybe LNFact
lookupPrem i = (`atMay` getPremIdx i) . L.get rPrems

-- | @lookupConc i ru@ returns the @i@-th conclusion of rule @ru@, if possible.
lookupConc :: ConcIdx -> Rule i -> Maybe LNFact
lookupConc i = (`atMay` getConcIdx i) . L.get rConcs

-- | @rPrem i@ is a lens for the @i@-th premise of a rule.
rPrem :: PremIdx -> (Rule i :-> LNFact)
rPrem i = nthL (getPremIdx i) . rPrems

-- | @rConc i@ is a lens for the @i@-th conclusion of a rule.
rConc :: ConcIdx -> (Rule i :-> LNFact)
rConc i = nthL (getConcIdx i) . rConcs

-- | Enumerate all premises of a rule.
enumPrems :: Rule i -> [(PremIdx, LNFact)]
enumPrems = zip [(PremIdx 0)..] . L.get rPrems

-- | Enumerate all conclusions of a rule.
enumConcs :: Rule i -> [(ConcIdx, LNFact)]
enumConcs = zip [(ConcIdx 0)..] . L.get rConcs

-- Instances
------------

-- we need special instances for Eq and Ord to ignore the new variable instantiations when comparing rules
-- instance (Eq t) => Eq (Rule t) where
--     (Rule i0 ps0 cs0 as0 _) == (Rule i1 ps1 cs1 as1 _) =
--         (i0 == i1) && (ps0 == ps1) && (cs0 == cs1) && (as0 == as1)

compareRulesUpToNewVars :: (Ord i) => Rule i -> Rule i -> Ordering
compareRulesUpToNewVars (Rule i0 ps0 cs0 as0 _) (Rule i1 ps1 cs1 as1 _) =
        if i0 == i1 then
           if ps0 == ps1 then
              if cs0 == cs1 then
                   compare as0 as1
                 else
                   compare cs0 cs1
              else
                 compare ps0 ps1
           else
              compare i0 i1

-- deriving instance (Ord t) => Ord (Rule t)

instance Functor Rule where
    fmap f (Rule i ps cs as nvs) = Rule (f i) ps cs as nvs

instance (Show i, HasFrees i) => HasFrees (Rule i) where
    foldFrees f (Rule i ps cs as nvs) =
        (foldFrees f i  `mappend`) $
        (foldFrees f ps `mappend`) $
        (foldFrees f cs `mappend`) $
        (foldFrees f as `mappend`) $
        (foldFrees f nvs)
    -- We do not include the new variables in the occurrences
    foldFreesOcc f c (Rule i ps cs as _) =
        foldFreesOcc f ((show i):c) (ps, cs, as)
    mapFrees f (Rule i ps cs as nvs) =
        Rule <$> mapFrees f i
             <*> mapFrees f ps <*> mapFrees f cs <*> mapFrees f as
             <*> mapFrees f nvs

instance Apply LNSubst i => Apply LNSubst (Rule i) where
    apply subst (Rule i ps cs as nvs) =
        Rule (apply subst i) (apply subst ps) (apply subst cs) (apply subst as) (apply subst nvs)

instance Sized (Rule i) where
  size (Rule _ ps cs as _) = size ps + size cs + size as

-----------------------------------------------
-- Extended Positions (of a term inside a rule)
-----------------------------------------------

type ExtendedPosition = (PremIdx, Int, Position)

printPosition :: ExtendedPosition -> String
printPosition (pidx, i, pos) = show (getPremIdx pidx) ++ "_" ++ show i ++ "_" ++ foldl (\x y -> x ++ show y  ++ "_") "" pos

printFactPosition :: ExtendedPosition -> String
printFactPosition (pidx, _, _) = show (getPremIdx pidx)

------------------------------------------------------------------------------
-- Rule information split into intruder rule and protocol rules
------------------------------------------------------------------------------

-- | Rule information for protocol and intruder rules.
data RuleInfo p i =
         ProtoInfo p
       | IntrInfo i
       deriving( Eq, Ord, Show, Generic)

instance (NFData i, NFData p) => NFData (RuleInfo p i)
instance (Binary i, Binary p) => Binary (RuleInfo p i)

-- | @ruleInfo proto intr@ maps the protocol information with @proto@ and the
-- intruder information with @intr@.
ruleInfo :: (p -> c) -> (i -> c) -> RuleInfo p i -> c
ruleInfo proto _    (ProtoInfo x) = proto x
ruleInfo _     intr (IntrInfo  x) = intr x


-- Instances
------------

instance (HasFrees p, HasFrees i) => HasFrees (RuleInfo p i) where
    foldFrees  f = ruleInfo (foldFrees f) (foldFrees f)
    foldFreesOcc _ _ = const mempty
    mapFrees   f = ruleInfo (fmap ProtoInfo . mapFrees   f)
                            (fmap IntrInfo . mapFrees   f)

instance (Apply s p, Apply s i) => Apply s (RuleInfo p i) where
    apply subst = ruleInfo (ProtoInfo . apply subst) (IntrInfo . apply subst)


------------------------------------------------------------------------------
-- Protocol Rule Information
------------------------------------------------------------------------------

-- | An attribute for a Rule, which does not affect the semantics.
data RuleAttribute = RuleColor (RGB Rational) -- Color for display
                   | Process (PlainProcess)-- Process: for display, but also to recognise
                             -- lookup rule generated by SAPIC
                             -- which needs relaxed treatment in wellformedness check
                             -- TODO This type has no annotations, to avoid
                             -- dependency to Sapic.Annotations
                             -- need to see what we need here later.
                  | IgnoreDerivChecks
                  | IsSAPiCRule -- tags the rule as a SAPiC rule
                  | Role String
       deriving( Eq, Ord, Show, Data, Generic)
instance NFData RuleAttribute
instance Binary RuleAttribute

-- | A name of a protocol rule is either one of the special reserved rules or
-- some standard rule.
data ProtoRuleName =
         FreshRule
       | StandRule String -- ^ Some standard protocol rule
       deriving( Eq, Ord, Show, Data, Typeable, Generic)
instance NFData ProtoRuleName
instance Binary ProtoRuleName

-- | Information for protocol rules modulo E.
data ProtoRuleEInfo = ProtoRuleEInfo
       { _preName       :: ProtoRuleName
       , _preAttributes :: [RuleAttribute]
       , _preRestriction:: [F.SyntacticLNFormula]
       }
       deriving( Eq, Ord, Show, Data, Generic)
instance NFData ProtoRuleEInfo
instance Binary ProtoRuleEInfo

-- | Information for protocol rules modulo AC. The variants list the possible
-- instantiations of the free variables of the rule. The source is interpreted
-- modulo AC; i.e., its variants were also built.
data ProtoRuleACInfo = ProtoRuleACInfo
       { _pracName         :: ProtoRuleName
       , _pracAttributes   :: [RuleAttribute]
       , _pracVariants     :: Disj (LNSubstVFresh)
       , _pracLoopBreakers :: [PremIdx]
       }
       deriving(Eq, Ord, Show, Generic)
instance NFData ProtoRuleACInfo
instance Binary ProtoRuleACInfo

-- | Information for instances of protocol rules modulo AC.
data ProtoRuleACInstInfo = ProtoRuleACInstInfo
       { _praciName         :: ProtoRuleName
       , _praciAttributes   :: [RuleAttribute]
       , _praciLoopBreakers :: [PremIdx]
       }
       deriving(Eq, Ord, Show, Generic)
instance NFData ProtoRuleACInstInfo
instance Binary ProtoRuleACInstInfo


$(mkLabels [''ProtoRuleEInfo, ''ProtoRuleACInfo, ''ProtoRuleACInstInfo])


-- Instances
------------
instance Apply s RuleAttribute where
    apply _ = id

instance HasFrees RuleAttribute where
    foldFrees _ = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees  _ = pure

instance Apply s ProtoRuleName where
    apply _ = id

instance HasFrees ProtoRuleName where
    foldFrees  _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees   _ = pure

instance Apply s PremIdx where
    apply _ = id

instance HasFrees PremIdx where
    foldFrees  _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees   _ = pure

instance Apply s ConcIdx where
    apply _ = id

instance HasFrees ConcIdx where
    foldFrees  _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees   _ = pure

instance HasFrees ProtoRuleEInfo where
    foldFrees f (ProtoRuleEInfo na attr rstr) =
        foldFrees f na `mappend` foldFrees f attr `mappend` foldFrees f rstr
    foldFreesOcc  _ _ = const mempty
    mapFrees f (ProtoRuleEInfo na attr rstr) =
        ProtoRuleEInfo na <$> mapFrees f attr <*> mapFrees f rstr

instance Apply s ProtoRuleEInfo where
    apply _ = id

instance HasFrees ProtoRuleACInfo where
    foldFrees f (ProtoRuleACInfo na attr vari breakers) =
        foldFrees f na `mappend` foldFrees f attr
                       `mappend` foldFrees f vari
                       `mappend` foldFrees f breakers
    foldFreesOcc  _ _ = const mempty

    mapFrees f (ProtoRuleACInfo na attr vari breakers) =
        ProtoRuleACInfo na <$> mapFrees f attr
                           <*> mapFrees f vari
                           <*> mapFrees f breakers

instance Apply s ProtoRuleACInstInfo where
    apply subst (ProtoRuleACInstInfo na attr breakers) =
        ProtoRuleACInstInfo (apply subst na) attr breakers

instance HasFrees ProtoRuleACInstInfo where
    foldFrees f (ProtoRuleACInstInfo na attr breakers) =
        foldFrees f na `mappend` foldFrees f attr
                       `mappend` foldFrees f breakers

    foldFreesOcc  _ _ = const mempty

    mapFrees f (ProtoRuleACInstInfo na attr breakers) =
        ProtoRuleACInstInfo na <$> mapFrees f attr <*> mapFrees f breakers


------------------------------------------------------------------------------
-- Intruder Rule Information
------------------------------------------------------------------------------

-- | An intruder rule modulo AC is described by its name.
data IntrRuleACInfo =
    ConstrRule BC.ByteString
  | DestrRule BC.ByteString Int Bool Bool
  -- the number of remaining consecutive applications of this destruction rule, 0 means unbounded, -1 means not yet determined
  -- true if the RHS is a true subterm of the LHS
  -- true if the RHS is a constant
  | CoerceRule
  | IRecvRule
  | ISendRule
  | PubConstrRule
  | NatConstrRule
  | FreshConstrRule
  | IEqualityRule -- Necessary for diff
  deriving( Ord, Eq, Show, Data, Typeable, Generic)
instance NFData IntrRuleACInfo
instance Binary IntrRuleACInfo

-- | An intruder rule modulo AC.
type IntrRuleAC = Rule IntrRuleACInfo

-- | Converts between these two types of rules, if possible.
ruleACToIntrRuleAC :: RuleAC -> Maybe IntrRuleAC
ruleACToIntrRuleAC (Rule (IntrInfo i) ps cs as nvs) = Just (Rule i ps cs as nvs)
ruleACToIntrRuleAC _                                = Nothing

-- | Converts between these two types of rules.
ruleACIntrToRuleAC :: IntrRuleAC -> RuleAC
ruleACIntrToRuleAC (Rule ri ps cs as nvs) = Rule (IntrInfo ri) ps cs as nvs

-- | Converts between these two types of rules.
ruleACIntrToRuleACInst :: IntrRuleAC -> RuleACInst
ruleACIntrToRuleACInst (Rule ri ps cs as nvs) = Rule (IntrInfo ri) ps cs as nvs

-- | Converts between constructor and destructor rules.
constrRuleToDestrRule :: RuleAC -> Int -> Bool -> Bool -> [RuleAC]
constrRuleToDestrRule (Rule (IntrInfo (ConstrRule name)) ps' cs _ _) i s c
    -- we remove the actions and new variables as destructors do not have actions or new variables
    = map toRule $ permutations ps'
    where
        toRule :: [LNFact] -> RuleAC
        toRule []     = error "Bug in constrRuleToDestrRule. Please report."
        toRule (p:ps) = Rule (IntrInfo (DestrRule name i s c)) ((convertKUtoKD p):ps) (map convertKUtoKD cs) [] []
constrRuleToDestrRule _ _ _ _ = error "Not a destructor rule."

-- | Converts between destructor and constructor rules.
destrRuleToConstrRule :: FunSym -> Int -> RuleAC -> [RuleAC]
destrRuleToConstrRule f l (Rule (IntrInfo (DestrRule name _ _ _)) ps cs _ _)
    = map (\x -> toRule x (conclusions cs)) (permutations (map convertKDtoKU ps ++ kuFacts))
    where
        -- we add the conclusion as an action as constructors have this action
        toRule :: [LNFact] -> [LNFact] -> RuleAC
        toRule ps' cs' = Rule (IntrInfo (ConstrRule name)) ps' cs' cs' []

        conclusions [] = []
        -- KD and KU facts only have one term
        conclusions ((Fact KDFact ann (m:ms)):cs') = (Fact KUFact ann ((addTerms m):ms)):(conclusions cs')
        conclusions                    (c:cs') =                               c:(conclusions cs')

        addTerms (FAPP f' t) | f'==f = fApp f (t ++ newvars)
        addTerms  t                  = fApp f (t:newvars)

        kuFacts = map kuFact newvars

        newvars = map (var "z") [1..(toInteger $ l-(length ps))]
destrRuleToConstrRule _ _ _ = error "Not a constructor rule."

-- | Creates variants of a destructor rule, where KD and KU facts are permuted.
destrRuleToDestrRule :: RuleAC -> [RuleAC]
destrRuleToDestrRule (Rule (IntrInfo (DestrRule name i s c)) ps' cs as nv)
    = map toRule $ permutations (map convertKDtoKU ps')
    where
        toRule []     = error "Bug in destrRuleToDestrRule. Please report."
        toRule (p:ps) = Rule (IntrInfo (DestrRule name i s c)) ((convertKUtoKD p):ps) cs as nv
destrRuleToDestrRule _ = error "Not a destructor rule."


-- Instances
------------

instance Apply s IntrRuleACInfo where
    apply _ = id

instance HasFrees IntrRuleACInfo where
    foldFrees _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees _  = pure


------------------------------------------------------------------------------
-- Concrete rules
------------------------------------------------------------------------------

-- | A rule modulo E is always a protocol rule. Intruder rules are specified
-- abstractly by their operations generating them and are only available once
-- their variants are built.
type ProtoRuleE  = Rule ProtoRuleEInfo

-- | A protocol rule modulo AC.
type ProtoRuleAC = Rule ProtoRuleACInfo

-- | A rule modulo AC is either a protocol rule or an intruder rule
type RuleAC      = Rule (RuleInfo ProtoRuleACInfo IntrRuleACInfo)

-- | A rule instance module AC is either a protocol rule or an intruder rule.
-- The info identifies the corresponding rule modulo AC that the instance was
-- derived from.
type RuleACInst  = Rule (RuleInfo ProtoRuleACInstInfo IntrRuleACInfo)

-- Accessing the rule name
--------------------------

-- | Types that have an associated name.
class HasRuleName t where
  ruleName       :: t -> RuleInfo ProtoRuleName IntrRuleACInfo

instance HasRuleName ProtoRuleE where
  ruleName       = ProtoInfo . L.get (preName . rInfo)

instance HasRuleName RuleAC where
  ruleName = ruleInfo (ProtoInfo . L.get pracName) IntrInfo . L.get rInfo

instance HasRuleName ProtoRuleAC where
  ruleName  = ProtoInfo . L.get (pracName . rInfo)

instance HasRuleName IntrRuleAC where
  ruleName = IntrInfo . L.get rInfo

instance HasRuleName RuleACInst where
  ruleName = ruleInfo (ProtoInfo . L.get praciName) IntrInfo . L.get rInfo

class HasRuleAttributes t where
  ruleAttributes :: t -> [RuleAttribute]

instance HasRuleAttributes ProtoRuleE where
  ruleAttributes = L.get (preAttributes . rInfo)

instance HasRuleAttributes RuleAC where
  ruleAttributes (Rule (ProtoInfo ri) _ _ _ _) = L.get pracAttributes ri
  ruleAttributes _                             = []

instance HasRuleAttributes ProtoRuleAC where
  ruleAttributes = L.get (pracAttributes . rInfo)

instance HasRuleAttributes IntrRuleAC where
  ruleAttributes _ = []

instance HasRuleAttributes RuleACInst where
  ruleAttributes (Rule (ProtoInfo ri) _ _ _ _) = L.get praciAttributes ri
  ruleAttributes _                             = []

-- Queries
----------

-- | True iff the rule is a destruction rule.
isDestrRule :: HasRuleName r => r -> Bool
isDestrRule ru = case ruleName ru of
  IntrInfo (DestrRule _ _ _ _) -> True
  IntrInfo IEqualityRule   -> True
  _                        -> False

-- | True iff the rule is an iequality rule.
isIEqualityRule :: HasRuleName r => r -> Bool
isIEqualityRule ru = case ruleName ru of
  IntrInfo IEqualityRule -> True
  _                      -> False

-- | True iff the rule is a construction rule.
isConstrRule :: HasRuleName r => r -> Bool
isConstrRule ru = case ruleName ru of
  IntrInfo (ConstrRule _)  -> True
  IntrInfo FreshConstrRule -> True
  IntrInfo PubConstrRule   -> True
  IntrInfo NatConstrRule   -> True
  IntrInfo CoerceRule      -> True
  _                        -> False

-- | True iff the rule is a construction rule.
isPubConstrRule :: HasRuleName r => r -> Bool
isPubConstrRule ru = case ruleName ru of
  IntrInfo PubConstrRule   -> True
  _                        -> False

-- | True iff the rule is a construction rule.
isNatConstrRule :: HasRuleName r => r -> Bool
isNatConstrRule ru = case ruleName ru of
  IntrInfo NatConstrRule   -> True
  _                        -> False

-- | True iff the rule is the special fresh rule.
isFreshRule :: HasRuleName r => r -> Bool
isFreshRule = (ProtoInfo FreshRule ==) . ruleName

-- | True iff the rule is the special learn rule.
isIRecvRule :: HasRuleName r => r -> Bool
isIRecvRule = (IntrInfo IRecvRule ==) . ruleName

-- | True iff the rule is the special knows rule.
isISendRule :: HasRuleName r => r -> Bool
isISendRule = (IntrInfo ISendRule ==) . ruleName

-- | True iff the rule is the special coerce rule.
isCoerceRule :: HasRuleName r => r -> Bool
isCoerceRule = (IntrInfo CoerceRule ==) . ruleName

-- | True iff the rule is a destruction rule with constant RHS.
isConstantRule :: HasRuleName r => r -> Bool
isConstantRule ru = case ruleName ru of
  IntrInfo (DestrRule _ _ _ constant) -> constant
  _                                   -> False

-- | True iff the rule is a destruction rule where the RHS is a true subterm of the LHS.
isSubtermRule :: HasRuleName r => r -> Bool
isSubtermRule ru = case ruleName ru of
  IntrInfo (DestrRule _ _ subterm _) -> subterm
  IntrInfo IEqualityRule             -> True
  -- the equality rule is considered a subterm rule, as it has no RHS.
  _                                  -> False

-- | True if the messages in premises and conclusions are in normal form
nfRule :: Rule i -> WithMaude Bool
nfRule (Rule _ ps cs as nvs) = reader $ \hnd ->
    all (nfFactList hnd) [ps, cs, as, map termFact nvs]
  where
    nfFactList hnd xs =
        getAll $ foldMap (foldMap (All . (\t -> nf' t `runReader` hnd))) xs

-- | Normalize all terms in premises, actions and conclusions
normRule :: Rule i -> WithMaude (Rule i)
normRule (Rule rn ps cs as nvs) = reader $ \hnd -> (Rule rn (normFacts ps hnd) (normFacts cs hnd) (normFacts as hnd) (normTerms nvs hnd))
  where
    normFacts fs hnd' = map (\f -> runReader (normFact f) hnd') fs
    normTerms fs hnd' = map (\f -> runReader (norm' f) hnd') fs

-- | True iff the rule is an intruder rule
isIntruderRule :: HasRuleName r => r -> Bool
isIntruderRule ru =
    case ruleName ru of IntrInfo _ -> True; ProtoInfo _ -> False

-- | True iff the rule is an intruder rule
isProtocolRule :: HasRuleName r => r -> Bool
isProtocolRule ru =
    case ruleName ru of IntrInfo _ -> False; ProtoInfo _ -> True

-- | True if the protocol rule has only the trivial variant.
isTrivialProtoVariantAC :: ProtoRuleAC -> ProtoRuleE -> Bool
isTrivialProtoVariantAC (Rule info ps as cs nvs) (Rule _ ps' as' cs' nvs') =
    L.get pracVariants info == Disj [emptySubstVFresh]
    && ps == ps' && as == as' && cs == cs' && nvs == nvs'

-- | Returns a rule's name
getRuleName :: HasRuleName (Rule i) => Rule i -> String
getRuleName ru = case ruleName ru of
                      IntrInfo i  -> case i of
                                      ConstrRule x      -> "Constr" ++ (prefixIfReserved ('c' : BC.unpack x))
                                      DestrRule x _ _ _ -> "Destr" ++ (prefixIfReserved ('d' : BC.unpack x))
                                      CoerceRule        -> "Coerce"
                                      IRecvRule         -> "Recv"
                                      ISendRule         -> "Send"
                                      PubConstrRule     -> "PubConstr"
                                      NatConstrRule     -> "NatConstr"
                                      FreshConstrRule   -> "FreshConstr"
                                      IEqualityRule     -> "Equality"
                      ProtoInfo p -> case p of
                                      FreshRule   -> "FreshRule"
                                      StandRule s -> s

-- | Returns a protocol rule's name
getRuleNameDiff :: HasRuleName (Rule i) => Rule i -> String
getRuleNameDiff ru = case ruleName ru of
                      IntrInfo i  -> "Intr" ++ case i of
                                      ConstrRule x      -> "Constr" ++ (prefixIfReserved ('c' : BC.unpack x))
                                      DestrRule x _ _ _ -> "Destr" ++ (prefixIfReserved ('d' : BC.unpack x))
                                      CoerceRule        -> "Coerce"
                                      IRecvRule         -> "Recv"
                                      ISendRule         -> "Send"
                                      PubConstrRule     -> "PubConstr"
                                      NatConstrRule     -> "NatConstr"
                                      FreshConstrRule   -> "FreshConstr"
                                      IEqualityRule     -> "Equality"
                      ProtoInfo p -> "Proto" ++ case p of
                                      FreshRule   -> "FreshRule"
                                      StandRule s -> s

-- | Returns the remaining rule applications within the deconstruction chain if possible, 0 otherwise
getRemainingRuleApplications :: RuleACInst -> Int
getRemainingRuleApplications ru = case ruleName ru of
  IntrInfo (DestrRule _ i _ _) -> i
  _                            -> 0

-- | Sets the remaining rule applications within the deconstruction chain if possible
setRemainingRuleApplications :: RuleACInst -> Int -> RuleACInst
setRemainingRuleApplications (Rule (IntrInfo (DestrRule name _ subterm constant)) prems concs acts nvs) i
    = Rule (IntrInfo (DestrRule name i subterm constant)) prems concs acts nvs
setRemainingRuleApplications rule _
    = rule

-- | Converts a protocol rule to its "left" variant
getLeftRule :: Rule i ->  Rule i
getLeftRule (Rule ri ps cs as nvs) =
   Rule ri (map getLeftFact ps) (map getLeftFact cs) (map getLeftFact as) (map getLeftTerm nvs)

-- | Converts a protocol rule to its "right" variant
getRightRule :: Rule i ->  Rule i
getRightRule (Rule ri ps cs as nvs) =
   Rule ri (map getRightFact ps) (map getRightFact cs) (map getRightFact as) (map getRightTerm nvs)

-- | Returns a list of all new variables that need to be fixed for mirroring
getNewVariables :: Bool -> RuleACInst -> [LVar]
getNewVariables showPubVars (Rule _ _ _ _ nvs) = case showPubVars of
    True  -> newvars
    False -> filter (\v -> not $ lvarSort v == LSortPub) newvars
  where
    newvars = toVariables nvs

    toVariables []     = []
    toVariables (x:xs) = case getVar x of
                              Just v  -> v:(toVariables xs)
                              -- if the variable is already fixed, no need to fix it again!
                              Nothing -> toVariables xs

-- | Returns whether a given rule has new variables
containsNewVars :: RuleACInst -> Bool
containsNewVars (Rule _ _ _ _ nvs) = nvs == []

-- | Given a fresh rule instance and the rule instance to mirror, returns a substitution
--   determining how all new variables need to be instantiated if possible.
--   First parameter: original instance to mirror
--   Second parameter: fresh instance
getSubstitutionsFixingNewVars :: RuleACInst -> RuleACInst -> Maybe LNSubst
getSubstitutionsFixingNewVars (Rule (ProtoInfo (ProtoRuleACInstInfo _ _ _)) _ _ _ instancesO)
   (Rule (ProtoInfo (ProtoRuleACInstInfo _ _ _)) _ _ _ instancesF)
      | all (\(x, y) -> isPubVar x || x == y) $ zip instancesF instancesO
          = Just $ Subst $ M.fromList $ substList instancesF instancesO
      -- otherwise there is no substitution
      | otherwise
          = Nothing
    where
       substList []     []     = []
       substList (f:fs) (o:os) = case getVar f of
                   Nothing -> (substList fs os)
                   Just v  -> (v, o):(substList fs os)
       substList _      _      = error "getSubstitutionsFixingNewVars: different number of new variables"
getSubstitutionsFixingNewVars _ _
          = error "getSubstitutionsFixingNewVars: not called on a protocol rule" -- FIXME: Nothing?

-- | returns true if the first Rule has the same name, premise, conclusion and
-- action facts, ignoring added action facts and other rule information
-- TODO: Ignore renaming?
equalUpToAddedActions :: (HasRuleName (Rule i), HasRuleName (Rule i2)) => (Rule i) -> (Rule i2) -> Bool
equalUpToAddedActions ruAC@(Rule _ ps cs as _) ruE@(Rule _ ps' cs' as' _) =
  ruleName ruE == ruleName ruAC && ps == ps' && cs == cs' && compareActions as as'
  where
    compareActions _      []       = True
    compareActions []     _        = False
    compareActions (a:ass) (a':ass') = if a == a'
      then compareActions ass ass'
      else compareActions ass (a':ass')

-- | returns true if the first Rule has the same name, premise, conclusion and
-- action facts, ignoring terms
equalUpToTerms :: (HasRuleName (Rule i), HasRuleName (Rule i2)) => (Rule i) -> (Rule i2) -> Bool
equalUpToTerms ruAC@(Rule _ ps cs as _) ruE@(Rule _ ps' cs' as' _) =
  ruleName ruE == ruleName ruAC
    && length ps == length ps' && length cs == length cs' && length as == length as'
    && foldl sameFacts True (zip ps ps') && foldl sameFacts True (zip cs cs')
    && foldl sameFacts True (zip as as')
  where
    sameFacts b (f1, f2) = b && sameFact f1 f2
    sameFact (Fact tag _ _) (Fact tag' _ _) = tag == tag'

-- Construction
---------------

-- | Returns a multiplication rule instance of the given size.
multRuleInstance :: Int -> RuleAC
multRuleInstance n = (Rule (IntrInfo (ConstrRule $ BC.pack "_mult")) (map xifact [1..n]) [prod] [prod] [])
  where
    prod = kuFact (FAPP (AC Mult) (map xi [1..n]))

    xi :: Int -> LNTerm
    xi k = (LIT $ Var $ LVar "x" LSortMsg (toInteger k))

    xifact :: Int -> LNFact
    xifact k = kuFact (xi k)

-- | Returns a union rule instance of the given size.
unionRuleInstance :: Int -> RuleAC
unionRuleInstance n = (Rule (IntrInfo (ConstrRule $ BC.pack "_union")) (map xifact [1..n]) [prod] [prod] [])
  where
    prod = kuFact (FAPP (AC Union) (map xi [1..n]))

    xi :: Int -> LNTerm
    xi k = (LIT $ Var $ LVar "x" LSortMsg (toInteger k))

    xifact :: Int -> LNFact
    xifact k = kuFact (xi k)

-- | Returns a xor rule instance of the given size.
xorRuleInstance :: Int -> RuleAC
xorRuleInstance n = (Rule (IntrInfo (ConstrRule $ BC.pack "_xor")) (map xifact [1..n]) [prod] [prod] [])
  where
    prod = Fact KUFact S.empty [(FAPP (AC Xor) (map xi [1..n]))]

    xi :: Int -> LNTerm
    xi k = (LIT $ Var $ LVar "x" LSortMsg (toInteger k))

    xifact :: Int -> LNFact
    xifact k = Fact KUFact S.empty [(xi k)]

type RuleACConstrs = Disj LNSubstVFresh

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInst :: MonadFresh m
               => RuleAC
               -> m (RuleACInst, Maybe RuleACConstrs)
someRuleACInst =
    fmap extractInsts . rename
  where
    extractInsts (Rule (ProtoInfo i) ps cs as nvs) =
      ( Rule (ProtoInfo i') ps cs as nvs
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i)
                                 (L.get pracAttributes i)
                                 (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as nvs) =
      ( Rule (IntrInfo i) ps cs as nvs, Nothing )

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInstAvoiding :: HasFrees t
               => RuleAC
               -> t
               -> (RuleACInst, Maybe RuleACConstrs)
someRuleACInstAvoiding r s =
    renameAvoiding (extractInsts r) s
  where
    extractInsts (Rule (ProtoInfo i) ps cs as nvs) =
      ( Rule (ProtoInfo i') ps cs as nvs
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i)
                                 (L.get pracAttributes i)
                                 (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as nvs) =
      ( Rule (IntrInfo i) ps cs as nvs, Nothing )

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInstFixing :: MonadFresh m
               => RuleAC
               -> LNSubst
               -> m (RuleACInst, Maybe RuleACConstrs)
someRuleACInstFixing r subst =
    renameIgnoring (varsRange subst) (extractInsts r)
  where
    extractInsts (Rule (ProtoInfo i) ps cs as nvs) =
      ( apply subst (Rule (ProtoInfo i') ps cs as nvs)
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i)
                                 (L.get pracAttributes i)
                                 (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as nvs) =
      ( apply subst (Rule (IntrInfo i) ps cs as nvs), Nothing )

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInstAvoidingFixing :: HasFrees t
               => RuleAC
               -> t
               -> LNSubst
               -> (RuleACInst, Maybe RuleACConstrs)
someRuleACInstAvoidingFixing r s subst =
    renameAvoidingIgnoring (extractInsts r) s (varsRange subst)
  where
    extractInsts (Rule (ProtoInfo i) ps cs as nvs) =
      ( apply subst (Rule (ProtoInfo i') ps cs as nvs)
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i)
                                 (L.get pracAttributes i)
                                 (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as nvs) =
      ( apply subst (Rule (IntrInfo i) ps cs as nvs), Nothing )

-- | Add the diff label to a rule
addDiffLabel :: Rule a -> String -> Rule a
addDiffLabel (Rule info prems concs acts nvs) name =
  Rule info prems concs
    (acts ++ [Fact {factTag = ProtoFact Linear name 0,
                    factAnnotations = S.empty, factTerms = []}]) nvs

-- | Remove the diff label from a rule
removeDiffLabel :: Rule a -> String -> Rule a
removeDiffLabel (Rule info prems concs acts nvs) name =
    Rule info prems concs (filter isNotDiffAnnotation acts) nvs
  where
    isNotDiffAnnotation fa =
      fa /= Fact {factTag = ProtoFact Linear name 0,
                  factAnnotations = S.empty, factTerms = []}

-- | Add an action label to a rule
addAction :: Rule a -> LNFact -> Rule a
addAction (Rule info prems concs acts nvs) act =
  if act `elem` acts
    then Rule info prems concs acts nvs
    else Rule info prems concs (act:acts) nvs

-- | Apply macros into a rule
applyMacroInRule :: [Macro] -> Rule i -> Rule i
applyMacroInRule mcs (Rule info ruPrems ruConcs ruActs _) = Rule info mRuPrems mRuConcs mRuActs mRuNewVars
  where
    mRuPrems   = map (applyMacroInFact mcs) ruPrems
    mRuConcs   = map (applyMacroInFact mcs) ruConcs
    mRuActs    = map (applyMacroInFact mcs) ruActs
    mRuNewVars = newVariables mRuPrems (mRuConcs ++ mRuActs)


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

-- | Are these two rule instances unifiable?
unifiableRuleACInsts :: RuleACInst -> RuleACInst -> WithMaude Bool
unifiableRuleACInsts ru1 ru2 =
    (not . null) <$> unifyRuleACInstEqs [Equal ru1 ru2]

-- | Are these two rule instances equal up to renaming of variables?
equalRuleUpToRenaming :: (Show a, Eq a, HasFrees a) => Rule a -> Rule a -> WithMaude Bool
equalRuleUpToRenaming r1@(Rule rn1 pr1 co1 ac1 nvs1) r2@(Rule rn2 pr2 co2 ac2 nvs2) = reader $ \hnd ->
  case eqs of
       Nothing   -> False
       Just eqs' -> (rn1 == rn2) && (any isRenamingPerRule $ unifs eqs' hnd)
    where
       isRenamingPerRule subst = isRenaming (restrictVFresh (vars r1) subst) && isRenaming (restrictVFresh (vars r2) subst)
       vars ru = map fst $ varOccurences ru
       unifs eq hnd = unifyLNTerm eq `runReader` hnd
       eqs = foldl matchFacts (Just $ zipWith Equal nvs1 nvs2) $ zip (pr1++co1++ac1) (pr2++co2++ac2)
       matchFacts Nothing  _                                    = Nothing
       matchFacts (Just l) (Fact f1 _ t1, Fact f2 _ t2) | f1 == f2  = Just ((zipWith Equal t1 t2)++l)
                                                    | otherwise = Nothing

-- | Are these two rule instances equal up to added annotations in @ac2@?
equalRuleUpToAnnotations :: (Eq a) => Rule a -> Rule a -> Bool
equalRuleUpToAnnotations (Rule rn1 pr1 co1 ac1 nvs1) (Rule rn2 pr2 co2 ac2 nvs2) =
  rn1 == rn2 && pr1 == pr2 && co1 == co2 && nvs1 == nvs2 &&
  S.isSubsetOf (S.fromList ac1) (S.fromList ac2)

-- | Are these two rule instances equal up to an added diff annotation in @ac2@?
equalRuleUpToDiffAnnotation :: (HasRuleName (Rule a), Eq a) => Rule a -> Rule a -> Bool
equalRuleUpToDiffAnnotation ru1@(Rule rn1 pr1 co1 ac1 nvs1) (Rule rn2 pr2 co2 ac2 nvs2) =
  rn1 == rn2 && pr1 == pr2 && co1 == co2 && nvs1 == nvs2 &&
  ac1 == filter isNotDiffAnnotation ac2
  where
    isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru1) 0, factAnnotations = S.empty, factTerms = []})

-- | Are these two rule instances equal up to an added diff annotation in @ac2@ or @ac1@?
equalRuleUpToDiffAnnotationSym :: (HasRuleName (Rule a), Eq a) => Rule a -> Rule a -> Bool
equalRuleUpToDiffAnnotationSym ru1 ru2 = equalRuleUpToDiffAnnotation ru1 ru2
                                      || equalRuleUpToDiffAnnotation ru2 ru1

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

-- | Prefix the name if it is equal to a reserved name.
--
-- NOTE: We maintain the invariant that a theory does not contain standard
-- rules with a reserved name. This is a last ressort. The pretty-printed
-- theory can then not be parsed anymore.
prefixIfReserved :: String -> String
prefixIfReserved n
  | n `elem` reservedRuleNames = "_" ++ n
  | "_" `isPrefixOf` n         = "_" ++ n
  | otherwise                  = n

-- | List of all reserved rule names.
reservedRuleNames :: [String]
reservedRuleNames = ["Fresh", "irecv", "isend", "coerce", "fresh", "pub", "iequality"]

prettyProtoRuleName :: Document d => ProtoRuleName -> d
prettyProtoRuleName rn = text $ case rn of
    FreshRule   -> "Fresh"
    StandRule n -> prefixIfReserved n

prettyDotProtoRuleName :: Document d => [RuleAttribute] -> ProtoRuleName -> d
prettyDotProtoRuleName attrs rn = text $ case rn of
    FreshRule   -> "Fresh"
    StandRule n -> if IsSAPiCRule `elem` attrs
                     then (if "new" `isPrefixOf` n then chr 957 : ' ' : drop 3 (trimSapicName n) else trimSapicName n)
                     else prefixIfReserved n
    where
      trimSapicName name =
        case splitString name of
          Just (s, n, m) -> if all isDigit n && all isDigit m then s else name
          Nothing -> name
      splitString str =
        let parts = reverse $ splitOn "_" str in
          if length parts >= 3
            then Just (intercalate "_" (reverse (drop 2 parts)), head (tail parts), head parts)
            else Nothing

prettyRuleName :: (HighlightDocument d, HasRuleName (Rule i)) => Rule i -> d
prettyRuleName = ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName

prettyRuleAttribute :: (HighlightDocument d) => RuleAttribute -> d
prettyRuleAttribute attr = case attr of
    RuleColor c -> text "color=" <> text (rgbToHex c)
    Process   p -> text "process=" <> text ("\"" ++ prettySapicTopLevel' f p ++ "\"")
        where f l a r rest _ = render $ prettyRuleRestr (g l) (g a) (g r) (h rest)
              g = map toLNFact
              h = map toLFormula
    IgnoreDerivChecks -> text "derivchecks"
    IsSAPiCRule       -> text "issapicrule"
    Role roleName -> text "role=\'" <> text roleName <> text "\'"

-- | Pretty print the rule name such that it can be used as a case name
showRuleCaseName :: HasRuleName (Rule i) => Rule i -> String
showRuleCaseName =
    render . ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName

-- | Pretty print the rule name such that it can be used as a case name in a dot node
showDotRuleCaseName :: (HasRuleName (Rule i), HasRuleAttributes (Rule i)) => Rule i -> String
showDotRuleCaseName ru =
    render . ruleInfo (prettyDotProtoRuleName (ruleAttributes ru)) prettyIntrRuleACInfo . ruleName $ ru

prettyIntrRuleACInfo :: Document d => IntrRuleACInfo -> d
prettyIntrRuleACInfo rn = text $ case rn of
    IRecvRule            -> "irecv"
    ISendRule            -> "isend"
    CoerceRule           -> "coerce"
    FreshConstrRule      -> "fresh"
    PubConstrRule        -> "pub"
    NatConstrRule        -> "nat"
    IEqualityRule        -> "iequality"
    ConstrRule name      -> prefixIfReserved ('c' : BC.unpack name)
    DestrRule name _ _ _ -> prefixIfReserved ('d' : BC.unpack name)
--     DestrRule name i -> prefixIfReserved ('d' : BC.unpack name ++ "_" ++ show i)


-- TODO may be removed
-- prettyRestr :: HighlightDocument d => F.SyntacticLNFormula -> d
-- prettyRestr fact =  operator_ "_restrict(" <> text (filter (/= '#') $ render $ F.prettySyntacticLNFormula fact) <> operator_ ")"

-- | pretty-print rules with restrictions
prettyRuleRestrGen :: (HighlightDocument d) => (f -> d) -> (r -> d) -> [f] -> [f] -> [f] -> [r] -> d
prettyRuleRestrGen ppFact ppRestr prems acts concls restr=
    sep [ nest 1 $ ppFactsList prems
                , if null acts && null restr
                    then operator_ "-->"
                    else fsep [operator_ "--["
                             , ppList (map ppFact acts
                                    ++ map ppRestr' restr)
                             , operator_ "]->"]
                , nest 1 $ ppFactsList concls]
-- Debug:
--     (keyword_ "new variables: ") <> (ppList prettyLNTerm $ L.get rNewVars ru)
  where
    ppList           = fsep . punctuate comma
    ppFacts'         = ppList . map ppFact
    ppFactsList list = fsep [operator_ "[", ppFacts' list, operator_ "]"]
    ppRestr' fact    = operator_ "_restrict(" <> ppRestr fact <> operator_ ")"

-- | pretty-print rules with restrictions
prettyRuleRestr :: HighlightDocument d => [LNFact] -> [LNFact] -> [LNFact] -> [F.SyntacticLNFormula] -> d
prettyRuleRestr = prettyRuleRestrGen prettyLNFact F.prettySyntacticLNFormula

-- | pretty-print rules without restrictions
prettyRule :: HighlightDocument d => [LNFact] -> [LNFact] -> [LNFact] -> d
prettyRule prems acts concls = prettyRuleRestr prems acts concls []


prettyNamedRule :: (HighlightDocument d, HasRuleName (Rule i), HasRuleAttributes (Rule i))
                => d           -- ^ Prefix.
                -> (i -> d)    -- ^ Rule info pretty printing.
                -> Rule i -> d
prettyNamedRule prefix ppInfo ru =
    prefix <-> prettyRuleName ru <> ppAttributes <> colon $-$
    nest 2
    (prettyRule (facts rPrems) acts (facts rConcs))  $-$
    nest 2 (ppInfo $ L.get rInfo ru) --- $-$
    where
    acts             = filter isNotDiffAnnotation (L.get rActs ru)
    isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0, factAnnotations = S.empty, factTerms = []})
    facts proj     = L.get proj ru
    ppAttributes = case ruleAttributes ru of
        []    -> text ""
        attrs -> hcat [text "[", ppList $ map prettyRuleAttribute attrs, text "]"]
    ppList           = fsep . punctuate comma

prettyProtoRuleACInfo :: HighlightDocument d => ProtoRuleACInfo -> d
prettyProtoRuleACInfo i =
    (ppVariants $ L.get pracVariants i) $-$
    prettyLoopBreakers i
  where
    ppVariants (Disj [subst]) | subst == emptySubstVFresh = emptyDoc
    ppVariants substs = kwVariantsModulo "AC" $-$ prettyDisjLNSubstsVFresh substs

prettyProtoRuleACInstInfo :: HighlightDocument d => ProtoRuleACInstInfo -> d
prettyProtoRuleACInstInfo i = prettyInstLoopBreakers i

prettyLoopBreakers :: HighlightDocument d => ProtoRuleACInfo -> d
prettyLoopBreakers i = case breakers of
    []  -> emptyDoc
    [_] -> lineComment_ $ "loop breaker: "  ++ show breakers
    _   -> lineComment_ $ "loop breakers: " ++ show breakers
  where
    breakers = getPremIdx <$> L.get pracLoopBreakers i

prettyInstLoopBreakers :: HighlightDocument d => ProtoRuleACInstInfo -> d
prettyInstLoopBreakers i = case breakers of
    []  -> emptyDoc
    [_] -> lineComment_ $ "loop breaker: "  ++ show breakers
    _   -> lineComment_ $ "loop breakers: " ++ show breakers
  where
    breakers = getPremIdx <$> L.get praciLoopBreakers i

prettyProtoRuleE :: HighlightDocument d => ProtoRuleE -> d
prettyProtoRuleE = prettyNamedRule (kwRuleModulo "E") (const emptyDoc)

prettyRuleAC :: HighlightDocument d => RuleAC -> d
prettyRuleAC =
    prettyNamedRule (kwRuleModulo "AC")
        (ruleInfo prettyProtoRuleACInfo (const emptyDoc))

prettyProtoRuleACasE :: HighlightDocument d => ProtoRuleAC -> d
prettyProtoRuleACasE =
    prettyNamedRule (kwRuleModulo "E") (const emptyDoc)

prettyIntrRuleAC :: HighlightDocument d => IntrRuleAC -> d
prettyIntrRuleAC = prettyNamedRule (kwRuleModulo "AC") (const emptyDoc)

prettyProtoRuleAC :: HighlightDocument d => ProtoRuleAC -> d
prettyProtoRuleAC = prettyNamedRule (kwRuleModulo "AC") prettyProtoRuleACInfo

prettyRuleACInst :: HighlightDocument d => RuleACInst -> d
prettyRuleACInst = prettyNamedRule (kwInstanceModulo "AC") (const emptyDoc)

-- | Pretty-print a non-empty bunch of intruder rules.
prettyIntruderVariants :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntruderVariants vs = vcat . intersperse (text "") $ map prettyIntrRuleAC vs

{-
-- | Pretty-print the intruder variants section.
prettyIntrVariantsSection :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntrVariantsSection rules =
    prettyFormalComment "section" " Finite Variants of the Intruder Rules " $--$
    nest 1 (prettyIntruderVariants rules)
-}
