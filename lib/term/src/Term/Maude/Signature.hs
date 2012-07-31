{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Equational signatures for Maude.
module Term.Maude.Signature (
  -- * Maude signatures
    MaudeSig
  , enableDH
  , enableBP
  , enableMSet
  , stFunSyms
  , stRules
  , funSyms
  , irreducibleFunSyms
  , rrulesForMaudeSig
  , noEqFunSyms

  -- * predefined maude signatures
  , dhMaudeSig
  , pairMaudeSig
  , asymEncMaudeSig
  , symEncMaudeSig
  , signatureMaudeSig
  , hashMaudeSig
  , msetMaudeSig
  , bpMaudeSig
  , minimalMaudeSig

  -- * extend maude signatures
  , addFunSym
  , addStRule

  -- * pretty printing
  , prettyMaudeSig
  ) where

import Term.Term
import Term.LTerm
import Term.Builtin.Rules
import Term.SubtermRule

import Control.Monad.Fresh
import Control.Applicative
import Control.DeepSeq

import Data.DeriveTH
import Data.Binary
import Data.Foldable (asum)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as S

import qualified Data.ByteString.Char8 as BC

import qualified Text.PrettyPrint.Highlight as P

------------------------------------------------------------------------------
-- Maude Signatures
----------------------------------------------------------------------

-- | The required information to define a @Maude functional module@.
data MaudeSig = MaudeSig
    { enableDH           :: Bool
    , enableBP           :: Bool
    , enableMSet         :: Bool
    , stFunSyms          :: S.Set NoEqSym -- ^ function signature for subterm theory
    , stRules            :: S.Set StRule  -- ^ rewriting rules for subterm theory

    , funSyms            :: FunSig        -- ^ function signature including the
                                          -- function symbols for DH, BP, and Multiset
                                          -- can be computed from enableX and stFunSyms
    , irreducibleFunSyms :: FunSig        -- ^ irreducible function symbols (can be computed)
    }
    deriving (Ord, Show, Eq)

-- | Smart constructor for maude signatures. Computes funSyms and irreducibleFunSyms.
maudeSig :: MaudeSig -> MaudeSig
maudeSig msig@(MaudeSig {enableDH,enableBP,enableMSet,stFunSyms,stRules}) =
    msig {enableDH=enableDH||enableBP, funSyms=allfuns, irreducibleFunSyms=irreduciblefuns}
  where
    allfuns = (S.map NoEq stFunSyms)
                `S.union` (if enableDH || enableBP then dhFunSig   else S.empty)
                `S.union` (if enableBP             then bpFunSig   else S.empty)
                `S.union` (if enableMSet           then msetFunSig else S.empty)
    irreduciblefuns = allfuns `S.difference` reducible
    reducible =
        S.fromList [ o | StRule (viewTerm -> FApp o _) _ <- S.toList stRules ]
          `S.union` dhReducibleFunSig `S.union` bpReducibleFunSig

-- | A monoid instance to combine maude signatures.
instance Monoid MaudeSig where
    (MaudeSig dh1 bp1 mset1 stFunSyms1 stRules1 _ _) `mappend`
      (MaudeSig dh2 bp2 mset2 stFunSyms2 stRules2 _ _) =
          maudeSig (mempty {enableDH=dh1||dh2
                           ,enableBP=bp1||bp2
                           ,enableMSet=mset1||mset2
                           ,stFunSyms=S.union stFunSyms1 stFunSyms2
                           ,stRules=S.union stRules1 stRules2})
    mempty = MaudeSig False False False S.empty S.empty S.empty S.empty

-- | Non-AC function symbols.
noEqFunSyms :: MaudeSig -> NoEqFunSig
noEqFunSyms msig = S.fromList [ o | NoEq o <- S.toList (funSyms msig) ]

-- | Add function symbol to given maude signature.
addFunSym :: NoEqSym -> MaudeSig -> MaudeSig
addFunSym funsym msig =
    msig `mappend` mempty {stFunSyms=S.fromList [funsym]}

-- | Add subterm rule to given maude signature.
addStRule :: StRule -> MaudeSig -> MaudeSig
addStRule str msig =
    msig `mappend` mempty {stRules=S.fromList [str]}

-- | Returns all rewriting rules including the rules
--   for DH, BP, and multiset.
rrulesForMaudeSig :: MaudeSig -> Set (RRule LNTerm)
rrulesForMaudeSig (MaudeSig {enableDH, enableBP, enableMSet, stRules}) =
    (S.map stRuleToRRule stRules)
    `S.union` (if enableDH   then dhRules   else S.empty)
    `S.union` (if enableBP   then bpRules   else S.empty)
    `S.union` (if enableMSet then msetRules else S.empty)

------------------------------------------------------------------------------
-- Builtin maude signatures
------------------------------------------------------------------------------

-- | Maude signatures for the AC symbols.
dhMaudeSig, bpMaudeSig, msetMaudeSig :: MaudeSig
dhMaudeSig   = maudeSig $ mempty {enableDH=True}
bpMaudeSig   = maudeSig $ mempty {enableBP=True}
msetMaudeSig = maudeSig $ mempty {enableMSet=True}

-- | Maude signatures for the default subterm symbols.
pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, hashMaudeSig :: MaudeSig
pairMaudeSig      = maudeSig $ mempty {stFunSyms=pairFunSig,stRules=pairRules}
symEncMaudeSig    = maudeSig $ mempty {stFunSyms=symEncFunSig,stRules=symEncRules}
asymEncMaudeSig   = maudeSig $ mempty {stFunSyms=asymEncFunSig,stRules=asymEncRules}
signatureMaudeSig = maudeSig $ mempty {stFunSyms=signatureFunSig,stRules=signatureRules}
hashMaudeSig      = maudeSig $ mempty {stFunSyms=hashFunSig}

-- | The minimal maude signature.
minimalMaudeSig :: MaudeSig
minimalMaudeSig = pairMaudeSig

------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

prettyMaudeSig :: P.HighlightDocument d => MaudeSig -> d
prettyMaudeSig sig = P.vcat
    [ ppNonEmptyList' "builtins:"  P.text      builtIns
    , ppNonEmptyList' "functions:" ppFunSymb $ S.toList (stFunSyms sig)
    , ppNonEmptyList
        (\ds -> P.sep (P.keyword_ "equations:" : map (P.nest 2) ds))
        prettyStRule $ S.toList (stRules sig)
    ]
  where
    ppNonEmptyList' name     = ppNonEmptyList ((P.keyword_ name P.<->) . P.fsep)
    ppNonEmptyList _   _  [] = P.emptyDoc
    ppNonEmptyList hdr pp xs = hdr $ P.punctuate P.comma $ map pp xs

    builtIns = asum $ map (\(f, x) -> guard (f sig) *> pure x)
      [ (enableDH,   "diffie-hellman")
      , (enableBP,   "bilinear-pairing")
      , (enableMSet, "multiset")
      ]

    ppFunSymb (f,k) = P.text $ BC.unpack f ++ "/" ++ show k


-- derived instances
--------------------

$(derive makeBinary ''MaudeSig)
$(derive makeNFData ''MaudeSig)
