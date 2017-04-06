{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
-- |
-- Copyright   : (c) 2011, 2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Facts used to formulate and reason about protocol execution.
module Theory.Model.Fact (

  -- * Fact
    Fact(..)
  , Multiplicity(..)
  , FactTag(..)

  , matchFact
  , normFact

  -- ** Queries
  , isLinearFact
  , isPersistentFact
  , isProtoFact

  , factTagName
  , showFactTag
  , showFactTagArity
  , factTagArity
  , factTagMultiplicity
  , factArity
  , factMultiplicity
  , getLeftFact
  , getRightFact
  , getFactVariables
  , getFactTerms
  , isTrivialFact

  , DirTag(..)
  , kuFact
  , kdFact
  , kFactView
  , dedFactView

  , isKFact
  , isKUFact
  , isKDFact

  -- ** Construction
  , freshFact
  , outFact
  , inFact
  , kLogFact
  , dedLogFact
  , protoFact

  -- * NFact
  , NFact

  -- * LFact
  , LFact
  , LNFact
  , unifyLNFactEqs
  , unifiableLNFacts

  -- * Pretty-Printing

  , prettyFact
  , prettyNFact
  , prettyLNFact

  ) where

-- import           Control.Basics
import           Control.DeepSeq
import           Control.Monad.Reader

import           GHC.Generics (Generic)
import           Data.Binary
-- import           Data.Foldable          (Foldable(..))
import           Data.Data
import           Data.Maybe             (isJust)
import           Data.Monoid
-- import           Data.Traversable       (Traversable(..))
import qualified Data.Set               as S

import           Term.Unification
import           Term.Rewriting.Norm

import           Text.PrettyPrint.Class


------------------------------------------------------------------------------
-- Fact
------------------------------------------------------------------------------

data Multiplicity = Persistent | Linear
                  deriving( Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary )

-- | Fact tags/symbols
data FactTag = ProtoFact Multiplicity String Int
               -- ^ A protocol fact together with its arity and multiplicity.
             | FreshFact  -- ^ Freshly generated value.
             | OutFact    -- ^ Sent by the protocol
             | InFact     -- ^ Officially known by the intruder/network.
             | KUFact     -- ^ Up-knowledge fact in messsage deduction.
             | KDFact     -- ^ Down-knowledge fact in message deduction.
             | DedFact    -- ^ Log-fact denoting that the intruder deduced
                          -- a message using a construction rule.
    deriving( Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary )

-- | Facts.
data Fact t = Fact
    { factTag   :: FactTag
    , factTerms :: [t]
    }
    deriving( Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary )


-- Instances
------------

instance Functor Fact where
    fmap f (Fact tag ts) = Fact tag (fmap f ts)

instance Foldable Fact where
    foldMap f (Fact _ ts) = foldMap f ts

instance Traversable Fact where
    sequenceA (Fact tag ts) = Fact tag <$> sequenceA ts
    traverse f (Fact tag ts) = Fact tag <$> traverse f ts

instance Sized t => Sized (Fact t) where
  size (Fact _ args) = size args

instance HasFrees t => HasFrees (Fact t) where
    foldFrees  f = foldMap  (foldFrees f)
    foldFreesOcc f c fa = foldFreesOcc f ((show $ factTag fa):c) (factTerms fa)
    mapFrees   f = traverse (mapFrees f)

instance Apply t => Apply (Fact t) where
    apply subst = fmap (apply subst)


-- KU and KD facts
------------------

-- | A direction tag
data DirTag = UpK | DnK
            deriving( Eq, Ord, Show )

kdFact, kuFact :: t -> Fact t
kdFact = Fact KDFact . return
kuFact = Fact KUFact . return

-- | View a message-deduction fact.
kFactView :: LNFact -> Maybe (DirTag, LNTerm)
kFactView fa = case fa of
    Fact KUFact [m] -> Just (UpK, m)
    Fact KUFact _   -> errMalformed "kFactView" fa
    Fact KDFact [m] -> Just (DnK, m)
    Fact KDFact _   -> errMalformed "kFactView" fa
    _               -> Nothing

-- | View a deduction logging fact.
dedFactView :: LNFact -> Maybe LNTerm
dedFactView fa = case fa of
    Fact DedFact [m] -> Just m
    Fact DedFact _   -> errMalformed "dedFactView" fa
    _                -> Nothing

-- | True if the fact is a message-deduction fact.
isKFact :: LNFact -> Bool
isKFact = isJust . kFactView

-- | True if the fact is a KU-fact.
isKUFact :: LNFact -> Bool
isKUFact (Fact KUFact _) = True
isKUFact _               = False

-- | True if the fact is a KD-fact.
isKDFact :: LNFact -> Bool
isKDFact (Fact KDFact _) = True
isKDFact _               = False

-- | Mark a fact as malformed.
errMalformed :: String -> LNFact -> a
errMalformed caller fa =
    error $ caller ++ show ": malformed fact: " ++ show fa

-- Constructing facts
---------------------

-- | A fact denoting a message sent by the protocol to the intruder.
outFact :: t -> Fact t
outFact = Fact OutFact . return

-- | A fresh fact denotes a fresh unguessable name.
freshFact :: t -> Fact t
freshFact = Fact FreshFact . return

-- | A fact denoting that the intruder sent a message to the protocol.
inFact :: t -> Fact t
inFact = Fact InFact . return

-- | A fact logging that the intruder knows a message.
kLogFact :: t -> Fact t
kLogFact = protoFact Linear "K" . return

-- | A fact logging that the intruder deduced a message using a construction
-- rule. We use this to formulate invariants over normal dependency graphs.
dedLogFact :: t -> Fact t
dedLogFact = Fact DedFact . return

-- | A protocol fact denotes a fact generated by a protocol rule.
protoFact :: Multiplicity -> String -> [t] -> Fact t
protoFact multi name ts = Fact (ProtoFact multi name (length ts)) ts


-- Queries on facts
-------------------

-- | True iff the fact is a non-special protocol fact.
isProtoFact :: Fact t -> Bool
isProtoFact (Fact (ProtoFact _ _ _) _) = True
isProtoFact _                          = False

-- | True if the fact is a linear fact.
isLinearFact :: Fact t -> Bool
isLinearFact = (Linear ==) . factMultiplicity

-- | True if the fact is a persistent fact.
isPersistentFact :: Fact t -> Bool
isPersistentFact = (Persistent ==) . factMultiplicity

-- | The multiplicity of a 'FactTag'.
factTagMultiplicity :: FactTag -> Multiplicity
factTagMultiplicity tag = case tag of
    ProtoFact multi _ _ -> multi
    KUFact              -> Persistent
    KDFact              -> Persistent
    _                   -> Linear

-- | The arity of a 'FactTag'.
factTagArity :: FactTag -> Int
factTagArity tag = case  tag of
    ProtoFact _ _ k -> k
    KUFact          -> 1
    KDFact          -> 1
    DedFact         -> 1
    FreshFact       -> 1
    InFact          -> 1
    OutFact         -> 1

-- | The arity of a 'Fact'.
factArity :: Fact t -> Int
factArity (Fact tag ts)
  | length ts == k = k
  | otherwise      = error $ "factArity: tag of arity " ++ show k ++
                             " applied to " ++ show (length ts) ++ " terms"
  where
    k = factTagArity tag

-- | The multiplicity of a 'Fact'.
factMultiplicity :: Fact t -> Multiplicity
factMultiplicity = factTagMultiplicity . factTag

-- | The terms of a 'Fact'.
getFactTerms :: Fact t -> [t]
getFactTerms (Fact _ ts) = ts 

------------------------------------------------------------------------------
-- NFact
------------------------------------------------------------------------------

-- | Facts with literals containing names and arbitrary variables.
type NFact v = Fact (NTerm v)


------------------------------------------------------------------------------
-- LFact
------------------------------------------------------------------------------

-- | Facts with literals arbitrary constants and logical variables.
type LFact c = Fact (LTerm c)

-- | Facts used for proving; i.e. variables fixed to logical variables
-- and constant fixed to names.
type LNFact = Fact LNTerm

-- | Unify a list of @LFact@ equalities.
unifyLNFactEqs :: [Equal LNFact] -> WithMaude [LNSubstVFresh]
unifyLNFactEqs eqs
  | all (evalEqual . fmap factTag) eqs =
      unifyLNTerm (map (fmap (fAppList . factTerms)) eqs)
  | otherwise = return []

-- | 'True' iff the two facts are unifiable.
unifiableLNFacts :: LNFact -> LNFact -> WithMaude Bool
unifiableLNFacts fa1 fa2 = (not . null) <$> unifyLNFactEqs [Equal fa1 fa2]

-- | Normalize all terms in the fact
normFact :: LNFact -> WithMaude LNFact
normFact (Fact h ts) = reader $ \hnd -> (Fact h (map (\term -> runReader (norm' term) hnd) ts))

-- | @matchLFact t p@ is a complete set of AC matchers for the term fact @t@
-- and the pattern fact @p@.
matchFact :: Fact t -- ^ Term
            -> Fact t -- ^ Pattern
            -> Match t
matchFact t p =
    matchOnlyIf (factTag t == factTag p &&
                 length (factTerms t) == length (factTerms p))
    <> mconcat (zipWith matchWith (factTerms t) (factTerms p))
    
-- | Get "left" variant of a diff fact
getLeftFact :: LNFact -> LNFact
getLeftFact (Fact tag ts) =
   (Fact tag (map getLeftTerm ts))

-- | Get "left" variant of a diff fact
getRightFact :: LNFact -> LNFact
getRightFact (Fact tag ts) =
   (Fact tag (map getRightTerm ts))

-- | Get all variables inside a fact
getFactVariables :: LNFact -> [LVar]
getFactVariables (Fact _ ts) =
   map fst $ varOccurences ts

-- | If all the fact terms are simple and different msg variables (i.e., not fresh or public), returns the list of all these variables. Otherwise returns Nothing. [This could be relaxed to work for all variables (including fresh and public) if Facts were typed, so that an argument would always have to be fresh or public or general.]
isTrivialFact :: LNFact -> Maybe [LVar]
isTrivialFact (Fact _ ts) = case ts of
      []   -> Just []
      x:xs -> Prelude.foldl combine (getMsgVar x) (map getMsgVar xs)
    where
      combine :: Maybe [LVar] -> Maybe [LVar] -> Maybe [LVar]
      combine Nothing    _        = Nothing
      combine (Just _ )  Nothing  = Nothing
      combine (Just l1) (Just l2) = if noDuplicates l1 l2 then (Just (l1++l2)) else Nothing
      
      noDuplicates l1 l2 = S.null (S.intersection (S.fromList l1) (S.fromList l2))
   
------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | The name of a fact tag, e.g., @factTagName KUFact = "KU"@.
factTagName :: FactTag -> String
factTagName tag = case tag of
    KUFact            -> "KU"
    KDFact            -> "KD"
    DedFact           -> "Ded"
    InFact            -> "In"
    OutFact           -> "Out"
    FreshFact         -> "Fr"
    (ProtoFact _ n _) -> n

-- | Show a fact tag as a 'String'. This is the 'factTagName' prefixed with
-- the multiplicity.
showFactTag :: FactTag -> String
showFactTag tag =
    (++ factTagName tag) $ case factTagMultiplicity tag of
                             Linear     -> ""
                             Persistent -> "!"

-- | Show a fact tag together with its aritiy.
showFactTagArity :: FactTag -> String
showFactTagArity tag = showFactTag tag ++ "/" ++ show (factTagArity tag)

-- | Pretty print a fact.
prettyFact :: Document d => (t -> d) -> Fact t -> d
prettyFact ppTerm (Fact tag ts)
  | factTagArity tag /= length ts = ppFact ("MALFORMED-" ++ show tag) ts
  | otherwise                     = ppFact (showFactTag tag) ts
  where
    ppFact n = nestShort' (n ++ "(") ")" . fsep . punctuate comma . map ppTerm

-- | Pretty print a 'NFact'.
prettyNFact :: Document d => LNFact -> d
prettyNFact = prettyFact prettyNTerm

-- | Pretty print a 'LFact'.
prettyLNFact :: Document d => LNFact -> d
prettyLNFact fa = prettyFact prettyNTerm fa
