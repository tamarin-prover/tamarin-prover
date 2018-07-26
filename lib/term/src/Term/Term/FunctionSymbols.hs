{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
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
    , NoEqSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , diffSymString
    , expSymString
    , invSymString
    , pmultSymString
    , emapSymString
    , unionSymString
    , oneSymString
    , multSymString

    -- ** concrete symbols
    , diffSym
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
    , diffFunSig
    , dhReducibleFunSig
    , bpReducibleFunSig
    , implicitFunSig
    ) where

import           GHC.Generics (Generic)
import           Data.Typeable
import           Data.Binary
import           Data.Data


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
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | A function symbol can be either Private (unknown to adversary) or Public.
data Privacy = Private | Public
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | NoEq function symbols (with respect to the background theory).
type NoEqSym = (ByteString, (Int, Privacy)) -- ^ operator name, arity, private

-- | C(ommutative) function symbols
data CSym = EMap
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | Function symbols
data FunSym = NoEq  NoEqSym   -- ^ a free function function symbol of a given arity
            | AC    ACSym     -- ^ an AC function symbol, can be used n-ary
            | C     CSym      -- ^ a C function symbol of a given arity
            | List            -- ^ a free n-ary function symbol of TOP sort
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | Function signatures.
type FunSig = Set FunSym

-- | NoEq function signatures.
type NoEqFunSig = Set NoEqSym

----------------------------------------------------------------------
-- Fixed function symbols
----------------------------------------------------------------------

diffSymString, expSymString, invSymString, oneSymString, multSymString :: ByteString
diffSymString = "diff"
expSymString = "exp"
invSymString = "inv"
oneSymString = "one"
multSymString = "mult"

unionSymString :: ByteString
unionSymString = "union"

emapSymString, pmultSymString :: ByteString
emapSymString  = "em"
pmultSymString = "pmult"

pairSym, diffSym, expSym, invSym, oneSym, fstSym, sndSym, pmultSym :: NoEqSym
-- | Pairing.
pairSym  = ("pair",(2,Public))
-- | Diff.
diffSym  = (diffSymString,(2,Private))
-- | Exponentiation.
expSym   = (expSymString,(2,Public))
-- | The inverse in the groups of exponents.
invSym   = (invSymString,(1,Public))
-- | The one in the group of exponents.
oneSym   = (oneSymString,(0,Public))
-- | Projection of first component of pair.
fstSym   = ("fst",(1,Public))
-- | Projection of second component of pair.
sndSym   = ("snd",(1,Public))
-- | Multiplication of points (in G1) on elliptic curve by scalars.
pmultSym = (pmultSymString,(2,Public))

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

-- | The signature for diff terms.
diffFunSig :: NoEqFunSig
diffFunSig = S.fromList [ diffSym ]

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
