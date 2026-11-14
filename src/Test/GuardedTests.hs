-- Regression tests for singleton guarded connectives after deduplication.
module Test.GuardedTests (tests) where

import Test.HUnit
import Data.Binary (decode, encode)
import Data.Functor.Identity (Identity(..))
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Extension.Data.Label as L
import Logic.Connectives
import Theory.Constraint.System
import qualified Theory.Constraint.System.StoredFormulas as Stored
import Theory.Model

-- In particular, normalization must preserve encounter order: sorting would
-- change the order of alternatives under variable renaming.
tests :: Test
tests = TestList [connectiveTests, storedTests]

connectiveTests :: Test
connectiveTests = TestList
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

-- Exercise the invariant at every way into a StoredFormulas value, including
-- legacy encodings and transformations which merge operands or set entries.
storedTests :: Test
storedTests = TestList
    [ check "raw construction" [a] (Stored.singleton raw)
    , check "raw insertion" [a] (Stored.insert raw Stored.empty)
    , check "construction merges normalized entries" [a] (Stored.fromList [raw, a])
    , check "empty substitution after raw insertion" [a]
        (apply (emptySubst :: LNSubst) (Stored.singleton raw))
    , check "unrelated substitution" [a]
        (apply (substFromList [(k, varTerm j)] :: LNSubst) (Stored.singleton raw))
    , check "substitution collapses conjunction" [a]
        (apply subst (Stored.singleton (gconj [a, b])))
    , check "substitution merges set entries" [a]
        (apply subst (Stored.fromList [a, b]))
    , check "substitution preserves disjunction wrapper" [GDisj (Disj [a])]
        (apply subst disjunction)
    , check "union and deletion preserve normalization" [a]
        (Stored.delete b (Stored.union (Stored.singleton raw) (Stored.singleton b)))
    , check "variable mapping collapses operands" [a]
        (collapseVariables (Stored.singleton (gconj [a, b])))
    , check "variable mapping rebuilds set order" [a, b]
        (runIdentity (mapFrees (Arbitrary (Identity . swap)) (Stored.fromList [a, b])))
    , check "legacy decoding normalizes and merges entries" [a]
        (decode (encode (S.fromList [raw, a])))
    , TestCase $ assertEqual "binary representation remains compatible"
        (encode (S.singleton a)) (encode (Stored.singleton a))
    , TestCase $ assertEqual "binary round trip" disjunction (decode (encode disjunction))
    , TestCase $ assertEqual "substituted disjunction goal matches stored formula"
        (Stored.toList (apply subst disjunction)) [goalFormula (apply subst goal)]
    , TestCase $ assertEqual "mapped disjunction goal matches stored formula"
        (Stored.toList (collapseVariables disjunction)) [goalFormula (collapseVariables goal)]
    , TestCase $ do
        let mapped = collapseVariables system
        assertEqual "system mapping keeps disjunction goals aligned"
            (Stored.toList (L.get sFormulas mapped))
            (map goalFormula (M.keys (L.get sGoals mapped)))
    , TestCase $ do
        let decoded = decode (encode legacyGoals) :: System
        assertEqual "decoding merges normalized goal keys and statuses"
            (M.singleton (DisjG (Disj [a])) (GoalStatus True 1 True))
            (L.get sGoals decoded)
        assertEqual "decoded goals match stored formulas"
            (Stored.toList (L.get sFormulas decoded))
            (map goalFormula (M.keys (L.get sGoals decoded)))
    ]
  where
    i = LVar "i" LSortNode 0
    j = LVar "j" LSortNode 0
    k = LVar "k" LSortNode 0
    a = GAto (Last (varTerm (Free i))) :: LNGuarded
    b = GAto (Last (varTerm (Free j)))
    raw = GConj (Conj [a, a])
    disjunction = Stored.singleton (GDisj (Disj [a, b]))
    goal = DisjG (Disj [a, b])
    subst = substFromList [(j, varTerm i)] :: LNSubst
    collapseVariables :: HasFrees t => t -> t
    collapseVariables = runIdentity . mapFrees (Arbitrary (Identity . (\v -> if v == j then i else v)))
    swap v | v == i = j
           | v == j = i
           | otherwise = v
    goalFormula (DisjG d) = GDisj d
    goalFormula _ = error "expected a disjunction goal"
    system = L.set sFormulas disjunction
        $ L.set sGoals (M.singleton goal (GoalStatus False 1 False))
        $ emptySystem RawSource False
    legacyGoals = L.set sFormulas (Stored.singleton (GDisj (Disj [a])))
        $ L.set sGoals (M.fromList
            [(DisjG (Disj [a, a]), GoalStatus False 2 True)
            ,(DisjG (Disj [a]), GoalStatus True 1 False)]) system
    check label expected actual = TestCase $ assertEqual label
        (S.toList (S.fromList expected)) (Stored.toList actual)
