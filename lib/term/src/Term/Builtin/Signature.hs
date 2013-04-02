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
sdecSym = ("sdec",(2, (Public, Nothing)))
sencSym = ("senc",(2, (Public, Nothing)))
adecSym = ("adec",(2, (Public, Nothing)))
aencSym = ("aenc",(2, (Public, Nothing)))
signSym = ("sign",(2, (Public, Nothing)))

-- | Ternary builtin function symbols.
verifySym :: NoEqSym
verifySym = ("verify",(3, (Public, Nothing)))

-- | Unary builtin function symbols.
pkSym, hashSym :: NoEqSym
pkSym = ("pk",(1, (Public, Nothing)))
hashSym = ("h",(1, (Public, Nothing)))

-- | Nullary builtin function symbols.
trueSym :: NoEqSym
trueSym = ("true",(0, (Public, Nothing)))

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
