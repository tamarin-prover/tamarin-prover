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
import Term.Builtin.Signature
import Term.Builtin.Convenience

-- Rules for DH theory
----------------------------------------------------------------------

-- | The rewriting rules for Diffie-Hellman. This is a presentation due to Lankford
--   with the finite variant property.
dhRules :: [RRule LNTerm]
dhRules =
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

-- | The rewriting rules for Xor.
xorRules :: [RRule LNTerm]
xorRules =
    [ x1 +: x1 `RRule` zero
    , x1 +: zero `RRule` x1
    , x1 +: (x1 +: x2) `RRule` x2 ]

-- | The rewriting rules for multisets.
msetRules :: [RRule LNTerm]
msetRules = [ s1 # empty `RRule` s1 ]


-- | The rewriting rules for standard subterm operators that are builtin.
pairRules, symEncRules, asymEncRules, signatureRules :: [RRule LNTerm]
pairRules      =
    [ fstC (pair (x1,x2)) `RRule` x1
    , sndC (pair (x1,x2)) `RRule` x2 ]
symEncRules    = [ sdec (senc (x1,x2), x2) `RRule` x1 ]
asymEncRules   = [ adec (aenc (x1, pk x2), x2) `RRule` x1 ]
signatureRules =
    [ verify (sign (x1,x2), pk x2) `RRule` x1
    , extract (sign (x1,x2)) `RRule` x1 ]