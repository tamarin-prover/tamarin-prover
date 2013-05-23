{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Builtin function symbols and signatures.
module Term.Builtin.Signature where

import Term.LTerm
import qualified Data.Set as S

----------------------------------------------------------------------
-- Builtin symbols (pair and inv are defined in Term.Term)
----------------------------------------------------------------------

-- | Binary builtin function symbols.
sdecSym, sencSym, adecSym, aencSym, signSym :: NoEqSym
sdecSym = NoEqSym "sdec" 2 Public Nothing False
sencSym = NoEqSym "senc" 2 Public Nothing False
adecSym = NoEqSym "adec" 2 Public Nothing False
aencSym = NoEqSym "aenc" 2 Public Nothing False
signSym = NoEqSym "sign" 2 Public Nothing False

-- | Ternary builtin function symbols.
verifySym :: NoEqSym
verifySym = NoEqSym "verify" 3 Public Nothing False

-- | Unary builtin function symbols.
pkSym, hashSym :: NoEqSym
pkSym = NoEqSym "pk" 1 Public Nothing False
hashSym = NoEqSym "h" 1 Public Nothing False

-- | Nullary builtin function symbols.
trueSym :: NoEqSym
trueSym = NoEqSym "true" 0 Public Nothing False

----------------------------------------------------------------------
-- Builtin signatures
----------------------------------------------------------------------

-- | The signature for symmetric encryption.
symEncFunSig :: NoEqFunSig
symEncFunSig = S.fromList $ [ sdecSym, sencSym ]

-- | The signature for asymmetric encryption.
asymEncFunSig :: NoEqFunSig
asymEncFunSig = S.fromList $ [ adecSym, aencSym, pkSym ]

-- | The signature for cryptographic signatures.
signatureFunSig :: NoEqFunSig
signatureFunSig = S.fromList $ [ signSym, verifySym, trueSym, pkSym ]

-- | The signature for hashing.
hashFunSig :: NoEqFunSig
hashFunSig = S.fromList [ hashSym ]
