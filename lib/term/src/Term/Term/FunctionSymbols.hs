{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
  -- for ByteString
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Function Symbols and Signatures.
module Term.Term.FunctionSymbols (
    -- ** AC, C, and NonAC funcion symbols
      FunSym(..)
    , ACSym(..)
    , CSym(..)
    , Privacy(..)
    , NoEqSym(..)
    , SymSorts

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , expSymString
    , invSymString
    , pmultSymString
    , emapSymString
    , unionSymString
    , natPlusSymString
    , natOneSymString
    , natZeroSymString

    -- ** concrete symbols
    , expSym
    , pmultSym
    , oneSym
    , invSym
    , pairSym
    , fstSym
    , sndSym
    , natZeroSym
    , natOneSym

    -- ** concrete signatures
    , dhFunSig
    , bpFunSig
    , msetFunSig
    , natFunSig
    , pairFunSig
    , dhReducibleFunSig
    , bpReducibleFunSig
    , implicitFunSig
    ) where

import           Data.Typeable
import           Data.Generics
import           Data.DeriveTH
import           Data.Binary

import           Control.DeepSeq

import           Data.ByteString (ByteString)
import           Extension.Data.ByteString ()
import           Data.ByteString.Char8 ()

import           Data.Set (Set)
import qualified Data.Set as S

----------------------------------------------------------------------
-- Function symbols
----------------------------------------------------------------------

-- | AC function symbols.
data ACSym = Union | Mult | NatPlus | UserAC String String 
  deriving (Eq, Ord, Typeable, Data, Show)

-- | A function symbol can be either Private (unknown to adversary) or Public.
data Privacy = Private | Public
  deriving (Eq, Ord, Typeable, Data, Show)

-- | Some function symbols can be restricted to certain sorts.
type SymSorts = Maybe [String]

-- | NoEq function symbols (with respect to the background theory).
data NoEqSym = NoEqSym
               ByteString -- ^ Operator
               Int        -- ^ Arity
               Privacy    -- ^ Privacy (Public/Private)
               SymSorts   -- ^ Signature (optional) 
               Bool       -- ^ Iterated function?
  deriving (Eq, Ord, Typeable, Data, Show)

-- | C(ommutative) function symbols
data CSym = EMap
  deriving (Eq, Ord, Typeable, Data, Show)

-- | Function symbols
data FunSym = NoEq  NoEqSym   -- ^ a free function function symbol of a given arity
            | AC    ACSym     -- ^ an AC function symbol, can be used n-ary
            | C     CSym      -- ^ a C function symbol of a given arity
            | List            -- ^ a free n-ary function symbol of TOP sort
  deriving (Eq, Ord, Typeable, Data, Show)

-- | Function signatures.
type FunSig = Set FunSym

-- | NoEq function signatures.
type NoEqFunSig = Set NoEqSym

----------------------------------------------------------------------
-- Fixed function symbols
----------------------------------------------------------------------

expSymString, invSymString :: ByteString
expSymString = "exp"
invSymString = "inv"

unionSymString :: ByteString
unionSymString = "union"

emapSymString, pmultSymString :: ByteString
emapSymString  = "em"
pmultSymString = "pmult"

natPlusSymString, natZeroSymString, natOneSymString :: ByteString
natPlusSymString = "tplus"
natZeroSymString = "tzero"
natOneSymString = "tone"


pairSym, expSym, invSym, oneSym, fstSym, sndSym, pmultSym, natZeroSym, natOneSym :: NoEqSym
-- | Pairing.
pairSym    = NoEqSym "pair" 2 Public Nothing False
-- | Exponentiation.
expSym     = NoEqSym expSymString 2 Public Nothing False
-- | The inverse in the groups of exponents.
invSym     = NoEqSym invSymString 1 Public Nothing False
-- | The one in the group of exponents.
oneSym     = NoEqSym "one" 0 Public Nothing False
-- | Projection of first component of pair.
fstSym     = NoEqSym "fst" 1 Public Nothing False
-- | Projection of second component of pair.
sndSym     = NoEqSym "snd" 1 Public Nothing False
-- | Multiplication of points (in G1) on elliptic curve by scalars.
pmultSym   = NoEqSym pmultSymString 2 Public Nothing False
-- | Zero for natural numbers.
natZeroSym = NoEqSym natZeroSymString 0 Public (Just ["Nat"]) False
-- | One for natural numbers.
natOneSym  = NoEqSym natOneSymString 0 Public (Just ["Nat"]) False

----------------------------------------------------------------------
-- Fixed signatures
----------------------------------------------------------------------

-- | The signature for Diffie-Hellman function symbols.
dhFunSig :: FunSig
dhFunSig = S.fromList [ AC Mult, NoEq expSym, NoEq oneSym, NoEq invSym ]

-- | The signature for the bilinear pairing function symbols.
bpFunSig :: FunSig
bpFunSig = S.fromList [ NoEq pmultSym, C EMap ]

-- | The signature for the multiset function symbols.
msetFunSig :: FunSig
msetFunSig = S.fromList [ AC Union ]

-- | The signature for the natural numbers addition function symbols.
natFunSig :: FunSig
natFunSig = S.fromList [ NoEq natZeroSym, NoEq natOneSym, AC NatPlus ]

-- | The signature for pairing.
pairFunSig :: NoEqFunSig
pairFunSig = S.fromList [ pairSym, fstSym, sndSym ]

-- | Reducible function symbols for DH.
dhReducibleFunSig :: FunSig
dhReducibleFunSig = S.fromList [ NoEq expSym, NoEq invSym ]

-- | Reducible function symbols for BP.
bpReducibleFunSig :: FunSig
bpReducibleFunSig = S.fromList [ NoEq pmultSym, C EMap ]

-- | Implicit function symbols.
implicitFunSig :: FunSig
implicitFunSig = S.fromList [ NoEq invSym, NoEq pairSym
                            , AC Mult, AC Union ]

----------------------------------------------------------------------
-- Derived instances
----------------------------------------------------------------------

$( derive makeNFData ''Privacy)
$( derive makeNFData ''NoEqSym)
$( derive makeNFData ''CSym)
$( derive makeNFData ''FunSym)
$( derive makeNFData ''ACSym)

$( derive makeBinary ''Privacy)
$( derive makeBinary ''NoEqSym)
$( derive makeBinary ''CSym)
$( derive makeBinary ''FunSym)
$( derive makeBinary ''ACSym)
