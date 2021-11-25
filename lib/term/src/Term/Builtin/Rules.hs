-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Builtin rewriting rules.
module Term.Builtin.Rules (
  -- * Rewriting rules
    RRule(..)
  , dhRules
  , bpRules
  , msetRules
  , pairRules
  , xorRules
  , symEncRules
  , asymEncRules
  , signatureRules
  , revealSignatureRules
  , locationReportRules
  -- * Convenience export
  , module Term.Builtin.Signature
) where

import Term.LTerm
import Term.SubtermRule
import Term.Builtin.Signature
import Term.Builtin.Convenience

import qualified Data.Set as S
import Data.Set (Set)

-- Rules for DH theory
----------------------------------------------------------------------

-- | The rewriting rules for Diffie-Hellman. This is a presentation due to Lankford
--   with the finite variant property.
dhRules :: Set (RRule LNTerm)
dhRules = S.fromList
    [ expo(x1,one) `RRule` x1
    , expo(expo(x1,x2),x3) `RRule` expo(x1,(x2 *: x3))

    , x1 *: one `RRule` x1
    , inv (inv x1) `RRule` x1
    , inv one `RRule` one
    , x1 *: (inv x1) `RRule` one
    , inv x1 *: inv x2 `RRule` inv (x1 *: x2)
    , inv (x1 *: x2) *: x2 `RRule` inv x1
    , inv (inv x1 *: x2) `RRule` (x1 *: inv x2)
    , x1 *: (inv (x1) *: x2) `RRule` x2
    , inv x1 *: (inv x2 *: x3) `RRule` (inv (x1 *: x2) *: x3)
    , inv (x1 *: x2) *: (x2 *: x3) `RRule` (inv x1 *: x3)
    ]
  where
    expo = fAppExp
    inv  = fAppInv
    one  = fAppOne

-- | The rewriting rules for bilinear pairing. These rules extend the
--   the rules for Diffie-Hellman.
bpRules :: Set (RRule LNTerm)
bpRules = S.fromList
    [ pmult(one,x1) `RRule` x1
      -- x1 and x2 are scalars, x3 is a point on an elliptic curve
    , pmult(x3,pmult(x2,x1)) `RRule` pmult(x3 *: x2, x1)

    -- em is commutative, so this rule is sufficient
    , em(x1, pmult(x2,x3)) `RRule` expo(em(x1,x3), x2)
    ]
  where
    one   = fAppOne
    expo  = fAppExp
    pmult = fAppPMult
    em    = fAppEMap

-- | The rewriting rules for multisets.
msetRules :: Set (RRule LNTerm)
msetRules = S.empty

-- | The rewriting rules for Xor. This is a presentation with the finite variant property.
xorRules :: Set (RRule LNTerm)
xorRules = S.fromList
    [ x1 +: zero `RRule` x1
    , x1 +: x1 `RRule` zero
    , x1 +: x1 +: x2 `RRule` x2
    ]
  where
    zero  = fAppZero

-- | The rewriting rules for standard subterm operators that are builtin.
pairRules, symEncRules, asymEncRules, signatureRules, revealSignatureRules :: Set (CtxtStRule)
pairRules = S.fromList
    [ fAppFst (fAppPair (x1,x2)) `CtxtStRule` (StRhs [[0,0]] x1)
    , fAppSnd (fAppPair (x1,x2)) `CtxtStRule` (StRhs [[0,1]] x2) ]
symEncRules    = S.fromList [ sdec (senc (x1,x2), x2)     `CtxtStRule` (StRhs [[0,0]] x1) ]
asymEncRules   = S.fromList [ adec (aenc (x1, pk x2), x2) `CtxtStRule` (StRhs [[0,0]] x1) ]
signatureRules = S.fromList [ verify (sign (x1,x2), x1, pk x2) `CtxtStRule` (StRhs [[0,0]] trueC) ]
revealSignatureRules = S.fromList [ revealVerify (revealSign (x1,x2), x1, pk x2) `CtxtStRule` (StRhs [[0,0]] trueC),
                                    extractMessage (revealSign (x1,x2)) `CtxtStRule` (StRhs [[0,0]] x1)]

locationReportRules :: Set (CtxtStRule)
locationReportRules = S.fromList [ check_rep (rep (x1,x2), x2) `CtxtStRule` (StRhs [[0,0]] x1),
                                   get_rep (rep (x1,x2)) `CtxtStRule` (StRhs [[0,0]] x1)
                                 ]
