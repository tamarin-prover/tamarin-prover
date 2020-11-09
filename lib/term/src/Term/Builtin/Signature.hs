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

--TODO-MY add the + for the natural numbers
-- | Binary builtin function symbols.
sdecSym, sencSym, adecSym, aencSym, signSym, revealSignSym, repSym, checkRepSym :: NoEqSym
sdecSym = NoEqSym "sdec" 2 Public Nothing
sencSym = NoEqSym "senc" 2 Public Nothing
adecSym = NoEqSym "adec" 2 Public Nothing
aencSym = NoEqSym "aenc" 2 Public Nothing
signSym = NoEqSym "sign" 2 Public Nothing
revealSignSym = NoEqSym "revealSign" 2 Public Nothing
repSym = NoEqSym "rep" 2 Private Nothing
checkRepSym = NoEqSym "check_rep" 2 Public Nothing

-- | Ternary builtin function symbols.
verifySym, revealVerifySym :: NoEqSym
verifySym = NoEqSym "verify" 3 Public Nothing
revealVerifySym = NoEqSym "revealVerify" 3 Public Nothing

-- | Unary builtin function symbols.
pkSym, hashSym, extractMessageSym, getRepSym, reportSym :: NoEqSym
pkSym = NoEqSym "pk" 1 Public Nothing
hashSym = NoEqSym "h" 1 Public Nothing
extractMessageSym = NoEqSym "getMessage" 1 Public Nothing
getRepSym = NoEqSym "get_rep" 1 Public Nothing
reportSym = NoEqSym "report" 1 Public Nothing

-- | Nullary builtin function symbols.
trueSym :: NoEqSym
trueSym = NoEqSym "true" 0 Public Nothing

----------------------------------------------------------------------
-- Builtin signatures
----------------------------------------------------------------------

--TODO-MY add the natural numbers
-- | The signature for symmetric encryption.
symEncFunSig :: NoEqFunSig
symEncFunSig = S.fromList $ [ sdecSym, sencSym ]

-- | The signature for asymmetric encryption.
asymEncFunSig :: NoEqFunSig
asymEncFunSig = S.fromList $ [ adecSym, aencSym, pkSym ]

-- | The signature for cryptographic signatures.
signatureFunSig :: NoEqFunSig
signatureFunSig = S.fromList $ [ signSym, verifySym, trueSym, pkSym ]

-- | The signature for cryptographic signatures that are message-revealing.
revealSignatureFunSig :: NoEqFunSig
revealSignatureFunSig = S.fromList $ [ revealSignSym, revealVerifySym, extractMessageSym, trueSym, pkSym ]

locationReportFunSig :: NoEqFunSig
locationReportFunSig = S.fromList $ [ repSym, checkRepSym, getRepSym, reportSym]

-- | The signature for hashing.
hashFunSig :: NoEqFunSig
hashFunSig = S.fromList [ hashSym ]
