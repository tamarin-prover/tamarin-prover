-- Regression tests for singleton guarded connectives after deduplication.
module Test.GuardedTests (tests) where

import Test.HUnit
import Logic.Connectives
import Theory.Constraint.System.Guarded
import Theory.Model

-- In particular, normalization must preserve encounter order: sorting would
-- change the order of alternatives under variable renaming.
tests :: Test
tests = TestList
    [ TestLabel label $ TestCase $ assertEqual label expected actual
    | (label, expected, actual) <-
        [ ("duplicate conjunction", a, gconj [a, a])
        , ("duplicate disjunction", a, gdisj [a, a])
        , ("empty conjunction", gtrue, gconj [])
        , ("empty disjunction", gfalse, gdisj [])
        , ("conjunction identity", a, gconj [a, gtrue, a])
        , ("disjunction identity", a, gdisj [a, gfalse, a])
        , ("conjunction absorption", gfalse, gconj [a, gfalse, a])
        , ("disjunction absorption", gtrue, gdisj [a, gtrue, a])
        , ("conjunction order", GConj (Conj [b, a]), gconj [b, a, b])
        , ("disjunction order", GDisj (Disj [b, a]), gdisj [b, a, b])
        , ("grouped conjunction", gconj [a, a, gtrue], gconj [gconj [a, a], gtrue])
        , ("grouped disjunction", gdisj [a, a, gfalse], gdisj [gdisj [a, a], gfalse])
        , ("conjunction idempotence", gconj [a, a], gconj [gconj [a, a]])
        , ("disjunction idempotence", gdisj [a, a], gdisj [gdisj [a, a]])
        , ("one-pass conjunction simplification", a, simplify (GConj (Conj [a, a])))
        , ("one-pass disjunction simplification", a, simplify (GDisj (Disj [a, a])))
        , ("atom valuation preserves conjuncts", gconj [a, c],
            simplifyGuardedOrReturn (\atom -> if atom == Last (varTerm j) then Just False else Nothing)
                (gdisj [gconj [a, c], b]))
        , ("substitution preserves conjuncts", gconj [a, c], simplify substituted)
        , ("substitution simplification is stable", simplify substituted, simplify (simplify substituted))
        -- Storage normalization preserves the wrapper used by a DisjG goal,
        -- even though formula simplification collapses the same singleton.
        , ("stored disjunction preserves its goal wrapper", GDisj (Disj [gconj [a, c]]),
            normaliseStoredFormula substituted)
        , ("stored disjunction agrees with its goal", normaliseStoredFormula substituted,
            GDisj (normaliseDisjList (Disj [gconj [a, c], gconj [a, c]])))
        , ("stored disjunction normalization is stable", normaliseStoredFormula substituted,
            normaliseStoredFormula (normaliseStoredFormula substituted))
        ]
    ]
  where
    i = LVar "i" LSortNode 0
    j = LVar "j" LSortNode 0
    k = LVar "k" LSortNode 0
    a = GAto (Last (varTerm (Free i))) :: LNGuarded
    b = GAto (Last (varTerm (Free j)))
    c = GAto (Less (varTerm (Free i)) (varTerm (Free k)))
    substituted = apply (substFromList [(j, varTerm i)] :: LNSubst)
        (gdisj [gconj [a, c], gconj [b, c]])
    simplify = simplifyGuardedOrReturn (const Nothing)
