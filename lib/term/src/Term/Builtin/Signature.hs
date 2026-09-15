{-# LANGUAGE OverloadedStrings #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
--
-- Builtin function symbols and signatures.
module Term.Builtin.Signature where

import Term.LTerm
import qualified Data.Set as S

----------------------------------------------------------------------
-- Builtin symbols (pair and inv are defined in Term.Term)
----------------------------------------------------------------------

-- | Binary builtin function symbols.
sdecSym, sencSym, adecSym, aencSym, signSym, revealSignSym, repSym, checkRepSym :: NoEqSym
sdecSym = ("sdec",(2, Public, Constructor, NotNDC))
sencSym = ("senc",(2, Public, Constructor, NotNDC))
adecSym = ("adec",(2, Public, Constructor, NotNDC))
aencSym = ("aenc",(2, Public, Constructor, NotNDC))
signSym = ("sign",(2, Public, Constructor, NotNDC))
revealSignSym = ("revealSign",(2, Public, Constructor, NotNDC))
repSym = ("rep",(2,Private, Constructor, NotNDC))
checkRepSym = ("check_rep",(2,Public, Destructor, NotNDC))

-- | Ternary builtin function symbols.
verifySym, revealVerifySym :: NoEqSym
verifySym = ("verify",(3, Public, Constructor, NotNDC))
revealVerifySym = ("revealVerify",(3, Public,Constructor, NotNDC))

-- | Unary builtin function symbols.

pkSym, hashSym, extractMessageSym, getRepSym, reportSym :: NoEqSym
pkSym =  ("pk",(1, Public, Constructor, NotNDC))
hashSym = ("h",(1, Public, Constructor, NotNDC))
extractMessageSym = ("getMessage",(1, Public, Constructor, NotNDC))
getRepSym = ("get_rep",(1, Public,Destructor, NotNDC))
reportSym = ("report",(1, Public,Constructor, NotNDC))

-- | Nullary builtin function symbols.
trueSym :: NoEqSym
trueSym = ("true",(0, Public, Constructor, NotNDC))


-- | Destructor variants
mkDestSym :: NoEqSym -> NoEqSym
mkDestSym (name,(k,p,_,n)) = (name,(k,p, Destructor, n))

sdecDestSym, adecDestSym, verifyDestSym :: NoEqSym
sdecDestSym = mkDestSym sdecSym
adecDestSym = mkDestSym adecSym
verifyDestSym = mkDestSym verifySym
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

-- | The signature for cryptographic signatures that are message-revealing.
revealSignatureFunSig :: NoEqFunSig
revealSignatureFunSig = S.fromList $ [ revealSignSym, revealVerifySym, extractMessageSym, trueSym, pkSym ]

locationReportFunSig :: NoEqFunSig
locationReportFunSig = S.fromList $ [ repSym, checkRepSym, getRepSym, reportSym]

-- | The signature for hashing.
hashFunSig :: NoEqFunSig
hashFunSig = S.fromList [ hashSym ]


----------------------------------------------------------------------
-- Destructor builtin signatures
----------------------------------------------------------------------

-- | The signature for symmetric encryption.
symEncFunDestSig :: NoEqFunSig
symEncFunDestSig = S.fromList $ [ sdecDestSym, sencSym ]

-- | The signature for asymmetric encryption.
asymEncFunDestSig :: NoEqFunSig
asymEncFunDestSig = S.fromList $ [ adecDestSym, aencSym, pkSym ]

-- | The signature for cryptographic signatures.
signatureFunDestSig :: NoEqFunSig
signatureFunDestSig = S.fromList $ [ signSym, verifyDestSym, trueSym, pkSym ]
