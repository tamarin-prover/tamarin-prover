{-# LANGUAGE TemplateHaskell, FlexibleContexts, DeriveDataTypeable #-}
-- |
-- Copyright   : (c) 2011, 2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Facts used to formulate and reason about protocol execution.
module Theory.Fact (

  -- * Fact
    Fact(..)
  , Multiplicity(..)
  , FactTag(..)

  -- ** Queries
  , isLinearFact   
  , isPersistentFact
  , isProtoFact

  , showFactTag
  , showFactTagArity
  , factTagArity
  , factTagMultiplicity
  , factArity
  , factMultiplicity

  -- ** Message deduction facts
  , ExpTag(..)
  , expTagToTerm
  , termToExpTag

  , DirTag(..)
  , kFactView
  , isKFact
  , kuFact
  , kdFact

  -- ** Construction
  , freshFact
  , outFact
  , inFact
  , kLogFact
  , protoFact

  -- * NFact
  , NFact

  -- * LFact
  , LFact
  , LNFact
  , unifyLNFactEqs
  , matchLNFact

  -- * Pretty-Printing
  
  , prettyFact
  , prettyNFact
  , prettyLNFact

  -- * Convenience exports
  , module Term.Unification

  ) where

import Control.Basics
import Control.Monad.Fresh
import Control.DeepSeq

import Data.DeriveTH
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Binary
import Data.Generics 
import Data.Maybe (isJust)

import Term.Unification

import Text.Isar


------------------------------------------------------------------------------
-- Fact
------------------------------------------------------------------------------

data Multiplicity = Persistent | Linear
                  deriving( Eq, Ord, Show, Typeable, Data )

-- | Fact tags/symbols
data FactTag = ProtoFact Multiplicity String Int
               -- ^ A protocol fact together with its arity and multiplicity.
             | FreshFact  -- ^ Freshly generated value.
             | OutFact   -- ^ Sent by the protocol
             | InFact  -- ^ Officially known by the intruder/network.
             | KUFact     -- ^ Up-knowledge fact in messsage deduction.
             | KDFact     -- ^ Down-knowledge fact in message deduction.
    deriving( Eq, Ord, Show, Typeable, Data )

-- | Facts.
data Fact t = Fact 
    { factTag   :: FactTag 
    , factTerms :: [t]
    }
    deriving( Eq, Ord, Show, Typeable, Data )


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
    mapFrees   f = traverse (mapFrees f)

instance Apply t => Apply (Fact t) where
    apply subst = fmap (apply subst)


-- KU and KD facts
------------------

-- | Message fact exponentation tag.
data ExpTag = CannotExp | CanExp
            deriving( Eq, Ord, Show)

-- | Exponentiation-symbol to term.
expTagToTerm :: ExpTag -> LNTerm
expTagToTerm CannotExp   = Lit (Con (Name PubName (NameId ("noexp"))))
expTagToTerm CanExp      = Lit (Con (Name PubName (NameId ("exp"))))

-- | Term to exponentiation-symbol.
termToExpTag :: LNTerm -> Maybe ExpTag
termToExpTag (Lit (Con (Name PubName (NameId ("noexp"))))) = return CannotExp
termToExpTag (Lit (Con (Name PubName (NameId ("exp")))))   = return CanExp
termToExpTag _                                             = mzero


-- | A direction tag 
data DirTag = UpK | DnK
            deriving( Eq, Ord, Show )

-- | Construct a message fact. If no 'ExpTag' is given, then
-- a fresh variable that matches any 'ExpTag' is constructed.
kuFact, kdFact :: MonadFresh m => Maybe ExpTag -> LNTerm -> m LNFact
kuFact = mkFact KUFact
kdFact = mkFact KDFact

-- | A generic fact creation function.
mkFact :: MonadFresh m => FactTag -> Maybe ExpTag -> LNTerm -> m LNFact
mkFact tag (Just t) m = return $ Fact tag [expTagToTerm t, m]
mkFact tag Nothing  m = do
    v <- freshLVar "f_" LSortMsg
    return $ Fact tag [varTerm v, m]

-- | View a message-deduction fact.
kFactView :: LNFact -> Maybe (DirTag, Maybe ExpTag, LNTerm)
kFactView fa = case fa of
    Fact KUFact [e, m] -> Just (UpK, termToExpTag e, m)
    Fact KUFact _      -> errMalformed
    Fact KDFact [e, m] -> Just (DnK, termToExpTag e, m)
    Fact KDFact _      -> errMalformed
    _                  -> Nothing
  where
    errMalformed = error $ show "viewKFact: malformed fact: " ++ show fa

-- | True if the fact is a message-deduction fact.
isKFact :: LNFact -> Bool
isKFact = isJust . kFactView

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
factTagArity tag = case tag of 
    ProtoFact _ _ k -> k
    KUFact          -> 2
    KDFact          -> 2
    FreshFact       -> 1
    InFact       -> 1
    OutFact        -> 1

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
  -- TODO: Check if the arity of the facts is also checked.
  | all (evalEqual . fmap factTag) eqs = 
      unifyLNTerm (map (fmap (listToTerm . factTerms)) eqs)
  | otherwise = return []
 
-- | @matchLFact t p@ is a complete set of AC matchers for the term fact @t@
-- and the pattern fact @p@.
matchLNFact :: LNFact -- ^ Term
            -> LNFact -- ^ Pattern
            -> WithMaude [LNSubst]
matchLNFact t p
  | (factTag t == factTag p && length (factTerms t) == length (factTerms p)) =
       matchLNTerm $ zipWith MatchWith (factTerms t) (factTerms p)
  | otherwise = return []


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | Show a fact tag as a 'String'.
showFactTag :: FactTag -> String
showFactTag tag = case tag of
    KUFact            -> "!KU"
    KDFact            -> "!KD"
    InFact            -> "In"
    OutFact           -> "Out"
    FreshFact         -> "Fr"
    (ProtoFact m n _) -> multi m ++ n
  where
    multi Linear     = ""
    multi Persistent = "!"

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

-- derived instances
--------------------

$( derive makeBinary ''Multiplicity)
$( derive makeBinary ''FactTag)
$( derive makeBinary ''Fact)

$( derive makeNFData ''Multiplicity)
$( derive makeNFData ''FactTag)
$( derive makeNFData ''Fact)
