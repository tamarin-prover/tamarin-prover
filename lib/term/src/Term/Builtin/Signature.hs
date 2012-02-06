-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Builtin function symbols and signatures.
module Term.Builtin.Signature where

import Term.LTerm


-- Builtin symbols (pair and inv are defined in Term.Term)
----------------------------------------------------------------------

-- | Binary builtin non-ac function symbols.
sdecSym, sencSym, adecSym, aencSym, signSym :: NonACSym
sdecSym   = ("sdec",2)
sencSym   = ("senc",2)
adecSym   = ("adec",2)
aencSym   = ("aenc",2)
signSym   = ("sign",2)

verifySym :: NonACSym
verifySym = ("verify",3)

-- | Unary builtin non-ac function symbols.
fstSym, sndSym, pkSym, hashSym :: NonACSym
fstSym     = ("fst",1)
sndSym     = ("snd",1)
pkSym      = ("pk",1)
hashSym    = ("h",1)

-- | Nullary builtin non-ac function symbols.
trueSym :: NonACSym
trueSym = ("true",0)

-- Builtin signatures
----------------------------------------------------------------------

-- | The signature for the non-AC Diffie-Hellman function symbols.
dhFunSig :: FunSig
dhFunSig = [ expSym, oneSym, invSym ]

-- | The signature for the non-AC Xor function symbols.
xorFunSig :: FunSig
xorFunSig = [ zeroSym ]

-- | The signature for then non-AC multiset function symbols.
msetFunSig :: FunSig
msetFunSig = [ emptySym ]

-- | The signature for pairs.
pairFunSig :: FunSig
pairFunSig = [ pairSym, fstSym, sndSym ]

-- | The signature for symmetric encryption.
symEncFunSig :: FunSig
symEncFunSig = [ sdecSym, sencSym ]

-- | The signature for asymmetric encryption.
asymEncFunSig :: FunSig
asymEncFunSig = [ adecSym, aencSym, pkSym ]

-- | The signature for cryptographic signatures.
signatureFunSig :: FunSig
signatureFunSig = [ signSym, verifySym, trueSym, pkSym ]

-- | The signature for hashing.
hashFunSig :: FunSig
hashFunSig = [ hashSym ]
