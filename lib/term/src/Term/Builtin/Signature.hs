{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Builtin function symbols and signatures.
module Term.Builtin.Signature where

import Term.LTerm
import qualified Data.Set as S

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
pkSym, hashSym :: NonACSym
pkSym      = ("pk",1)
hashSym    = ("h",1)

-- | Nullary builtin non-ac function symbols.
trueSym :: NonACSym
trueSym = ("true",0)

-- Builtin signatures
----------------------------------------------------------------------

-- | The signature for symmetric encryption.
symEncFunSig :: FunSig
symEncFunSig = S.fromList [ sdecSym, sencSym ]

-- | The signature for asymmetric encryption.
asymEncFunSig :: FunSig
asymEncFunSig = S.fromList [ adecSym, aencSym, pkSym ]

-- | The signature for cryptographic signatures.
signatureFunSig :: FunSig
signatureFunSig = S.fromList [ signSym, verifySym, trueSym, pkSym ]

-- | The signature for hashing.
hashFunSig :: FunSig
hashFunSig = S.fromList [ hashSym ]
