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
    , NoEqSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , expSymString
    , invSymString
    , pmultSymString
    , emapSymString
    , unionSymString

    -- ** concrete symbols
    , expSym
    , pmultSym
    , oneSym
    , invSym
    , pairSym
    , fstSym
    , sndSym

    -- ** concrete signatures
    , dhFunSig
    , bpFunSig
    , msetFunSig
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
data ACSym = Union | Mult
  deriving (Eq, Ord, Typeable, Data, Show)

-- | NoEq function symbols (with respect to the background theory).
type NoEqSym = (ByteString, Int)

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

pairSym, expSym, invSym, oneSym, fstSym, sndSym, pmultSym :: NoEqSym
-- | Pairing.
pairSym  = ("pair",2)
-- | Exponentiation.
expSym   = (expSymString,2)
-- | The inverse in the groups of exponents.
invSym   = (invSymString,1)
-- | The one in the group of exponents.
oneSym   = ("one", 0)
-- | Projection of first component of pair.
fstSym   = ("fst",1)
-- | Projection of second component of pair.
sndSym   = ("snd",1)
-- | Multiplication of points (in G1) on elliptic curve by scalars.
pmultSym = (pmultSymString,2)

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
msetFunSig = S.fromList [AC Union]

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

$( derive makeNFData ''CSym)
$( derive makeNFData ''FunSym)
$( derive makeNFData ''ACSym)

$( derive makeBinary ''CSym)
$( derive makeBinary ''FunSym)
$( derive makeBinary ''ACSym)