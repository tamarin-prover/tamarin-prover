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
sdecSym, sencSym, adecSym, aencSym, signSym, verifySym :: NonACSym
sdecSym   = ("sdec",2)
sencSym   = ("senc",2)
adecSym   = ("adec",2)
aencSym   = ("aenc",2)
signSym   = ("sign",2)
verifySym = ("verify",2)

-- | Uinary builtin non-ac function symbols.
fstSym, sndSym, pkSym, extractSym, hashSym :: NonACSym
fstSym     = ("fst",1)
sndSym     = ("snd",1)
pkSym      = ("pk",1)
extractSym = ("extract",1)
hashSym    = ("h",1)

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
signatureFunSig = [ signSym, verifySym, extractSym ]

-- | The signature for hashing.
hashFunSig :: FunSig
hashFunSig = [ hashSym ]
