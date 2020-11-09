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
    , NoEqSym(..)
    , SymSorts

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
    , fstSymString
    , sndSymString
    , multSymString
    , zeroSymString
    , xorSymString
    , natPlusSymString
    , natOneSymString

    -- ** concrete symbols
    , diffSym
    , expSym
    , pmultSym
    , oneSym
    , invSym
    , pairSym
    , fstSym
    , sndSym
    , zeroSym
    , natOneSym

    -- ** concrete signatures
    , dhFunSig
    , xorFunSig
    , bpFunSig
    , msetFunSig
    , pairFunSig
    , dhReducibleFunSig
    , bpReducibleFunSig
    , xorReducibleFunSig
    , implicitFunSig
    , natFunSig
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
data ACSym = Union | Mult | Xor | NatPlus | UserAC String String   --TODO-MY | EqSym with type EqSym = (ByteString, (Int, Privacy)) or re-use NoEqSym
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | A function symbol can be either Private (unknown to adversary) or Public.
data Privacy = Private | Public
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | Some function symbols can be restricted to certain sorts.
type SymSorts = Maybe [String]

-- | NoEq function symbols (with respect to the background theory).
data NoEqSym = NoEqSym
               ByteString -- ^ Operator
               Int        -- ^ Arity
               Privacy    -- ^ Privacy (Public/Private)
               SymSorts   -- ^ Signature (optional)  --TODO-UNCERTAIN: removed iterated functions (and in all uses of NoEqSym)
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)  --TODO-UNCERTAIN: not sure what Generic, NFData, Binary do...

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
type NoEqFunSig = Set NoEqSym  --COMMENT-MY used to group symbols, e.g., in Builtin/Signature

----------------------------------------------------------------------
-- Fixed function symbols
----------------------------------------------------------------------

diffSymString, expSymString, invSymString, oneSymString, fstSymString, sndSymString, multSymString, xorSymString, zeroSymString :: ByteString
diffSymString = "diff"
expSymString = "exp"
invSymString = "inv"
oneSymString = "one"
fstSymString = "fst"
sndSymString = "snd"
multSymString = "mult"
zeroSymString = "zero"
xorSymString = "xor"

natPlusSymString, natOneSymString :: ByteString
natPlusSymString = "tplus"
natOneSymString = "tone"

unionSymString :: ByteString
unionSymString = "union"

emapSymString, pmultSymString :: ByteString
emapSymString  = "em"
pmultSymString = "pmult"

pairSym, diffSym, expSym, invSym, oneSym, fstSym, sndSym, pmultSym, zeroSym, natOneSym :: NoEqSym
-- | Pairing.
pairSym    = NoEqSym "pair" 2 Public Nothing
-- | Diff.
diffSym    = NoEqSym diffSymString 2 Private Nothing
-- | Exponentiation.
expSym     = NoEqSym expSymString 2 Public Nothing
-- | The inverse in the groups of exponents.
invSym     = NoEqSym invSymString 1 Public Nothing
-- | The one in the group of exponents.
oneSym     = NoEqSym oneSymString 0 Public Nothing
-- | Projection of first component of pair.
fstSym     = NoEqSym fstSymString 1 Public Nothing
-- | Projection of second component of pair.
sndSym     = NoEqSym sndSymString 1 Public Nothing
-- | Multiplication of points (in G1) on elliptic curve by scalars.
pmultSym   = NoEqSym pmultSymString 2 Public Nothing
-- | The zero for XOR.
zeroSym    = NoEqSym zeroSymString 0 Public Nothing
-- | One for natural numbers.
natOneSym  = NoEqSym natOneSymString 0 Public (Just ["Nat"])


----------------------------------------------------------------------
-- Fixed signatures
----------------------------------------------------------------------

-- | The signature for Diffie-Hellman function symbols.
dhFunSig :: FunSig
dhFunSig = S.fromList [ AC Mult, NoEq expSym, NoEq oneSym, NoEq invSym ]

-- | The signature for Xor function symbols.
xorFunSig :: FunSig
xorFunSig = S.fromList [ AC Xor, NoEq zeroSym ]

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

-- | Reducible function symbols for XOR.
xorReducibleFunSig :: FunSig
xorReducibleFunSig = S.fromList [ AC Xor ]

-- | Implicit function symbols.
implicitFunSig :: FunSig
implicitFunSig = S.fromList [ NoEq invSym, NoEq pairSym
                            , AC Mult, AC Union ]

-- | The signature for the natural numbers addition function symbols.
natFunSig :: FunSig
natFunSig = S.fromList [ NoEq natOneSym, AC NatPlus ]