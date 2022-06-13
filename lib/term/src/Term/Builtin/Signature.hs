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
sdecSym = ("sdec",(2, Public, Destructor))
sencSym = ("senc",(2, Public, Constructor))
adecSym = ("adec",(2, Public, Destructor))
aencSym = ("aenc",(2, Public, Constructor))
signSym = ("sign",(2, Public, Constructor))
revealSignSym = ("revealSign",(2, Public, Constructor))
repSym = ("rep",(2,Private,Constructor))
checkRepSym = ("check_rep",(2,Public,Destructor))

-- | Ternary builtin function symbols.
verifySym, revealVerifySym :: NoEqSym
verifySym = ("verify",(3, Public, Destructor))
revealVerifySym = ("revealVerify",(3, Public,Constructor))

-- | Unary builtin function symbols.

pkSym, hashSym, extractMessageSym, getRepSym, reportSym :: NoEqSym
pkSym =  ("pk",(1, Public, Constructor))
hashSym = ("h",(1, Public, Constructor))
extractMessageSym = ("getMessage",(1, Public, Constructor))
getRepSym = ("get_rep",(1, Public,Destructor))
reportSym = ("report",(1, Public,Constructor))

-- | Nullary builtin function symbols.
trueSym :: NoEqSym
trueSym = ("true",(0, Public, Constructor))

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
