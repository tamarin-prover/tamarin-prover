{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections #-}
{-# LANGUAGE ViewPatterns, NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Euqatiuonal signatures for Maude.
module Term.Maude.Signature (
  -- * Maude signatures
    MaudeSig
  , enableDH
  , enableXor
  , enableMultiset
  , functionSymbols
  , stRules
  , allFunctionSymbols
  , irreducibleFunctionSymbols
  , rrulesForMaudeSig

  -- * predefined maude signatures
  , dhMaudeSig
  , xorMaudeSig
  , pairMaudeSig
  , asymEncMaudeSig
  , symEncMaudeSig
  , signatureMaudeSig
  , hashMaudeSig
  , msetMaudeSig
  , minimalMaudeSig

  -- * extend maude signatures
  , addFunctionSymbol
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
    { enableDH        :: Bool
    , enableXor       :: Bool
    , enableMultiset  :: Bool
    , functionSymbols :: Set NonACSym    -- ^ function signature not including the function
                                         --   symbols for DH, Xor, and Multiset
    , stRules         :: Set StRule
    , allFunctionSymbols :: Set NonACSym -- ^ function signature including the
                                         --   nonAC function symbols for DH, Xor, and Multiset
                                         --   can be computed from enableX and functionSymbols
    , irreducibleFunctionSymbols :: Set NonACSym
    }
    deriving (Ord, Show, Eq)

-- | Smart constructor for MaudeSig. Computes allFunctionSymbols and irreducibleFunctionSymbols.
maudeSig :: Bool -> Bool -> Bool -> Set NonACSym -> Set StRule -> MaudeSig
maudeSig dh xor mset funs strs =
    MaudeSig dh xor mset funs strs allfuns irreduciblefuns
  where
    allfuns = funs `S.union` (if dh   then dhFunSig   else S.empty)
                   `S.union` (if xor  then xorFunSig  else S.empty)
                   `S.union` (if mset then msetFunSig else S.empty)
    irreduciblefuns = allfuns `S.difference` reducible
    reducible =
        S.fromList [ o | StRule (viewTerm -> FApp (NonAC o) _) _ <- S.toList strs ]
          `S.union` dhReducibleFunSig

-- | A monoid instance to combine maude signatures.
instance Monoid MaudeSig where
    (MaudeSig dh1 xor1 mset1 funsymbols1 stRules1 _ _) `mappend` (MaudeSig dh2 xor2 mset2 funsymbols2 stRules2 _ _) =
        maudeSig (dh1 || dh2) (xor1 || xor2)  (mset1 || mset2)
                 (S.union funsymbols1 funsymbols2)
                 (S.union stRules1 stRules2)
    mempty = maudeSig False False False S.empty S.empty

-- | Add function symbol to given maude signature.
addFunctionSymbol :: NonACSym -> MaudeSig -> MaudeSig
addFunctionSymbol funsym msig =
    msig `mappend` maudeSig False False False (S.fromList [funsym]) S.empty

-- | Add subterm rule to given maude signature.
addStRule :: StRule -> MaudeSig -> MaudeSig
addStRule str msig =
    msig `mappend` maudeSig False False False S.empty (S.fromList [str])

-- | @rrulesForMaudeSig msig@ returns all rewriting rules including the rules
--   for xor, dh, and multiset.
rrulesForMaudeSig :: MaudeSig -> Set (RRule LNTerm)
rrulesForMaudeSig (MaudeSig {enableXor, enableDH, enableMultiset, stRules}) =
    (S.map stRuleToRRule stRules)
    `S.union` (if enableDH       then dhRules   else S.empty)
    `S.union` (if enableXor      then xorRules  else S.empty)
    `S.union` (if enableMultiset then msetRules else S.empty)

------------------------------------------------------------------------------
-- Builtin maude signatures
------------------------------------------------------------------------------

-- | Maude signatures for the AC symbols.
dhMaudeSig, xorMaudeSig, msetMaudeSig :: MaudeSig
dhMaudeSig   = maudeSig True False False S.empty S.empty
xorMaudeSig  = maudeSig False True False S.empty S.empty
msetMaudeSig = maudeSig False False True S.empty S.empty

-- | Maude signatures for the default subterm symbols.
pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, hashMaudeSig :: MaudeSig
pairMaudeSig      = maudeSig False False False pairFunSig      pairRules
symEncMaudeSig    = maudeSig False False False symEncFunSig    symEncRules
asymEncMaudeSig   = maudeSig False False False asymEncFunSig   asymEncRules
signatureMaudeSig = maudeSig False False False signatureFunSig signatureRules
hashMaudeSig      = maudeSig False False False hashFunSig      S.empty

-- | The minimal maude signature.
minimalMaudeSig :: MaudeSig
minimalMaudeSig = pairMaudeSig

------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

prettyMaudeSig :: P.HighlightDocument d => MaudeSig -> d
prettyMaudeSig sig = P.vcat
    [ ppNonEmptyList' "builtins:"  P.text      builtIns
    , ppNonEmptyList' "functions:" ppFunSymb $ S.toList (functionSymbols sig)
    , ppNonEmptyList
        (\ds -> P.sep (P.keyword_ "equations:" : map (P.nest 2) ds))
        prettyStRule $ S.toList (stRules sig)
    ]
  where
    ppNonEmptyList' name     = ppNonEmptyList ((P.keyword_ name P.<->) . P.fsep)
    ppNonEmptyList _   _  [] = P.emptyDoc
    ppNonEmptyList hdr pp xs = hdr $ P.punctuate P.comma $ map pp xs

    builtIns = asum $ map (\(f, x) -> guard (f sig) *> pure x)
      [ (enableDH,       "diffie-hellman")
      , (enableXor,      "xor")
      , (enableMultiset, "multiset")
      ]

    ppFunSymb (f,k) = P.text $ BC.unpack f ++ "/" ++ show k


-- derived instances
--------------------

$(derive makeBinary ''MaudeSig)
$(derive makeNFData ''MaudeSig)
