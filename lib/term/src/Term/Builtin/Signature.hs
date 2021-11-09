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
sdecSym = ("sdec",(2, Public))
sencSym = ("senc",(2, Public))
adecSym = ("adec",(2, Public))
aencSym = ("aenc",(2, Public))
signSym = ("sign",(2, Public))
revealSignSym = ("revealSign",(2, Public))
repSym = ("rep",(2,Private))
checkRepSym = ("check_rep",(2,Public))

-- | Ternary builtin function symbols.
verifySym, revealVerifySym :: NoEqSym
verifySym = ("verify",(3, Public))
revealVerifySym = ("revealVerify",(3, Public))

-- | Unary builtin function symbols.
pkSym, hashSym, extractMessageSym, getRepSym, reportSym :: NoEqSym
pkSym = ("pk",(1, Public))
hashSym = ("h",(1, Public))
extractMessageSym = ("getMessage",(1, Public))
getRepSym = ("get_rep",(1, Public))
reportSym = ("report",(1, Public))

-- | Nullary builtin function symbols.
trueSym :: NoEqSym
trueSym = ("true",(0, Public))

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
