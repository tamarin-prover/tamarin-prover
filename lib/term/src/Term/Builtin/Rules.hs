-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Builtin rewriting rules.
module Term.Builtin.Rules (
  -- * Rewriting rules
    RRule(..)
  , dhRules
  , xorRules
  , msetRules
  , pairRules
  , symEncRules
  , asymEncRules
  , signatureRules

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

-- | The rewriting rules for Xor.
xorRules :: Set (RRule LNTerm)
xorRules = S.fromList
    [ x1 +: x1 `RRule` zero
    , x1 +: zero `RRule` x1
    , x1 +: (x1 +: x2) `RRule` x2 ]
  where
    zero = fAppZero

-- | The rewriting rules for multisets.
msetRules :: Set (RRule LNTerm)
msetRules = S.fromList [ x1 # fAppEmpty `RRule` x1 ]


-- | The rewriting rules for standard subterm operators that are builtin.
pairRules, symEncRules, asymEncRules, signatureRules :: Set (StRule)
pairRules = S.fromList
    [ fAppFst (fAppPair (x1,x2)) `StRule` (RhsPosition [0,0])
    , fAppSnd (fAppPair (x1,x2)) `StRule` (RhsPosition [0,1]) ]
symEncRules    = S.fromList [ sdec (senc (x1,x2), x2)     `StRule` (RhsPosition [0,0]) ]
asymEncRules   = S.fromList [ adec (aenc (x1, pk x2), x2) `StRule` (RhsPosition [0,0]) ]
signatureRules = S.fromList [ verify (sign (x1,x2), x1, pk x2) `StRule` (RhsGround trueC) ]