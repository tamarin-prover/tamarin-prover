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
    , Constructability(..)
    , NoEqSym

    -- ** Signatures
    , FunSig
    , NoEqFunSig

    -- ** concrete symbols strings
    , diffSymString
    , munSymString
    , expSymString
    , invSymString
    , dhNeutralSymString
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
    , dhNeutralSym
    , invSym
    , pairSym
    , fstSym
    , sndSym
    , fstDestSym
    , sndDestSym    
    , zeroSym
    , natOneSym

    -- ** concrete signatures
    , dhFunSig
    , xorFunSig
    , bpFunSig
    , msetFunSig
    , pairFunSig
    , pairFunDestSig    
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
data ACSym = Union | Mult | Xor | NatPlus
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | A function symbol can be either Private (unknown to adversary) or Public.
data Privacy = Private | Public
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | A function symbol can be either a constructor or a destructor in which
-- case it only applies if it reduces.
data Constructability = Constructor | Destructor
  deriving (Eq, Ord, Typeable, Data, Show, Generic, NFData, Binary)

-- | NoEq function symbols (with respect to the background theory).
type NoEqSym = (ByteString, (Int, Privacy,Constructability)) -- ^ operator name, arity, private, destructor

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

diffSymString, munSymString, expSymString, invSymString, dhNeutralSymString, oneSymString, xorSymString, multSymString, zeroSymString, fstSymString, sndSymString :: ByteString
diffSymString = "diff"
munSymString = "mun"
expSymString = "exp"
invSymString = "inv"
oneSymString = "one"
fstSymString = "fst"
sndSymString = "snd"
dhNeutralSymString = "DH_neutral"
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

pairSym, diffSym, expSym, invSym, oneSym, dhNeutralSym, fstSym, sndSym, pmultSym, zeroSym, natOneSym :: NoEqSym
-- | Pairing.
pairSym  = ("pair",(2,Public,Constructor))
-- | Diff.
diffSym  = (diffSymString,(2,Private,Constructor))
-- | Exponentiation.
expSym   = (expSymString,(2,Public,Constructor))
-- | The inverse in the groups of exponents.
invSym   = (invSymString,(1,Public,Constructor))
-- | The one in the group of exponents.
oneSym   = (oneSymString,(0,Public,Constructor))
-- | The groupd identity
dhNeutralSym = (dhNeutralSymString,(0,Public, Constructor))
-- | Projection of first component of pair.
fstSym   = (fstSymString,(1,Public,Destructor))
-- | Projection of second component of pair.
sndSym   = (sndSymString,(1,Public,Destructor))
-- | Multiplication of points (in G1) on elliptic curve by scalars.
pmultSym = (pmultSymString,(2,Public,Constructor))
-- | The zero for XOR.
zeroSym  = (zeroSymString,(0,Public,Constructor))
-- | One for natural numbers.
natOneSym = (natOneSymString, (0,Public,Constructor))

mkDestSym :: NoEqSym -> NoEqSym
mkDestSym (name,(k,p,_)) = (name,(k,p, Destructor))

fstDestSym, sndDestSym :: NoEqSym
-- | Projection of first component of pair.
fstDestSym   = mkDestSym fstSym
-- | Projection of second component of pair.
sndDestSym   = mkDestSym sndSym

----------------------------------------------------------------------
-- Fixed signatures
----------------------------------------------------------------------

-- | The signature for Diffie-Hellman function symbols.
dhFunSig :: FunSig
dhFunSig = S.fromList [ AC Mult, NoEq expSym, NoEq oneSym, NoEq invSym, NoEq dhNeutralSym ]

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

-- | The signature for pairing with destructors.
pairFunDestSig :: NoEqFunSig
pairFunDestSig = S.fromList [ pairSym, fstDestSym, sndDestSym ]

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
