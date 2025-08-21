{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}

-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Computate an under-approximation to the set of all facts with unique
-- instances, i.e., fact whose instances never occur more than once in a
-- state. We use this information to reason about protocols that exploit
-- exclusivity of linear facts.
module Theory.Tools.InjectiveFactInstances
  ( -- * Computing injective fact instances.
    MonotonicBehaviour (..),
    simpleInjectiveFactInstances,
  )
where

import Control.Applicative (empty)
import Control.DeepSeq
import Control.Monad.Fresh
import Data.Binary
import Data.Label as L
import Data.List
import Data.Map qualified as M
import Data.Maybe
import Data.Set qualified as S
import GHC.Generics (Generic)
import Safe (headMay)
import Theory.Model

-- import           Debug.Trace

-- unspecified = there is no rule using this fact
-- unstable = increasing and decreasing or not at all related inputs and outputs
data MonotonicBehaviour = Constant | Increasing | Decreasing | StrictlyIncreasing | StrictlyDecreasing | Unstable | Unspecified
  deriving (Eq, Ord, Generic, NFData, Binary)

instance Show MonotonicBehaviour where
  show Constant = "="
  show Increasing = "≤"
  show Decreasing = "≥"
  show StrictlyIncreasing = "<"
  show StrictlyDecreasing = ">"
  show Unstable = "."
  show Unspecified = "?"


-- | under-approximate monotonicity constraints from a formula.
-- For now, we only deal with a formula that corresponds to a subterm atom
-- If we want to express things like OR, we need to return a more refined value.
extractConstraints :: (Ord c, Ord b) => ProtoFormula syn s c b -> [(Term (Lit c b), Term (Lit c b))]
extractConstraints (Ato (Subterm t1 t2)) = [(bvarToLVar t1, bvarToLVar t2)]
    where
        bvarToLVar =
            fmapTerm (fmap (foldBVar boundError id))
        boundError _ = error "implementation error: bounded variable in top-level atom"
extractConstraints _ = []


-- | Compute a simple under-approximation to the set of facts with injective
-- instances. A fact-tag is has injective instances, if there is no state of
-- the protocol with more than one instance with the same term as a first
-- argument of the fact-tag.
--
-- We compute the under-approximation by checking that
-- (1) the fact-tag is linear
-- (2) for each occurrence of the fact-tag in a rule:
--     there is no other occurrence with the same first term and
--       (a) either there is a Fr-fact of the first term as a premise
--       (b) or there is exactly one fact-tag with the same first term in a premise
--
-- Additionally, we determine the term positions that are
-- - Constant
-- - Increasing/Decreasing according to `elemNotBelowReducible` and equality
-- - Strictly Increasing/Decreasing according to `elemNotBelowReducible`
--
-- We also try to detect these positions inside of tuples that occur at
-- the top-level of an injective fact. For instance,
-- if injective fact S is used like this: [S(~id, <a, b>)] --> [S(~id, <a, a>)]
-- position two of S is not constant but position 2.2 is.

-- To detect this, one needs to compute the _shape_ of a term at position i for
-- each protocol rule (modulo E) by checking how it is pattern-matched inside of
-- each rule. A natural choice would be to represent this shape via a binary tree
-- that matches the tuples shape, however, we choose to implement an
-- under-approximation of this by only flattening tuples to the right.
-- E.g., <<a, b>, c> gets flattened into [<a, b>, c]. This allows us to
-- detect constant/increasing etc. positions for the most common use case:
-- a tuple that contains 'dynamic' state and is only expanded to the right.
-- I.e., [S(~id, <a, b>)] --> [S(~id, <a, b, c>)]. In this example, the current
-- implement can still detect that 'a' is constant, but not 'b'.
--
-- We exclude facts that are not copied in a rule, as they are already handled
-- properly by the naive backwards reasoning.
simpleInjectiveFactInstances :: FunSig -> [ProtoRuleE] -> S.Set (FactTag, [[MonotonicBehaviour]])
simpleInjectiveFactInstances reducible rules = S.fromList $ do
  tag <- M.keys candidates
  let resultTag = combineAll (map (getMaybeEqStrict tag) rules) tag
  case resultTag of
    Just behaviours -> return (tag, behaviours) -- remove the 0-position from eqPos as this is the ~fr
    Nothing -> empty
  where
    -- Flatten only the right-hand side of a tuple
    getPairTerms :: LNTerm -> [LNTerm]
    getPairTerms (viewTerm2 -> FPair t1 t2) = t1 : getPairTerms t2
    getPairTerms t = [t]

    -- Compute the potentially injective facts and their _shape_.
    -- The shape `s` of a FactTag is a list of lists where the inner list
    -- `s[i]` describes the shape of the term at position `i+1` in the fact.
    -- The shape of a term is the right-handed flattening of it as computed
    -- by 'getPairTerms'. E.g., shape (Var x) = [x], shape (<t1, t2>) = [t1, t2]
    -- and shape (<<t1, t2>, t3>) = [<t1, t2>, t3].
    -- Intuitively, if `length shape' = n, then `shape' can be unfolded to the
    -- right n - 1 times.
    candidates :: M.Map FactTag [[MonotonicBehaviour]]
    candidates = M.fromListWith combineShapes $ do
      ru <- rules
      conc <- L.get rConcs ru
      let tag = factTag conc
      guard $
        (factTagMultiplicity tag == Linear)
          && (tag `elem` (factTag <$> L.get rPrems ru))
      prem <- L.get rPrems ru
      guard (factTag prem == tag)
      guard (not (null $ factTerms conc))
      return (tag, combineShapes (getShape conc) (getShape prem))
      where
        -- Compute the default shape of the fact. I.e., a correct shape
        -- with unspecified behaviour.
        getShape :: LNFact -> [[MonotonicBehaviour]]
        getShape (factTerms -> _ : terms) = map (flip replicate Unspecified . length . getPairTerms) terms
        getShape _ = error "a fact without terms cannot be injective"

        -- Combining two shapes is simply taking the shorter list at each position
        combineShapes :: [[MonotonicBehaviour]] -> [[MonotonicBehaviour]] -> [[MonotonicBehaviour]]
        combineShapes behaviours behaviours1 = map (map fst) $ zipWith zip behaviours behaviours1 -- zip automatically orients itself on the shorter list

    combineAll :: [Maybe [[MonotonicBehaviour]]] -> FactTag -> Maybe [[MonotonicBehaviour]]
    combineAll list _ | any isNothing list = Nothing -- if any of the elements say that the tag is not injective, then return nothing
    combineAll (Just behaviours : Just behaviours1 : rest) tag =
      -- trace (show("combineAll", behaviours, behaviours1, (map (map combine) $ zipWith zip behaviours behaviours1))) $
      combineAll (Just (map (map combine) $ zipWith zip behaviours behaviours1) : rest) tag
    combineAll [x] _ = x
    combineAll [] tag = M.lookup tag candidates -- start with the empty shape of Unspecified
    combineAll _ _ = error "The haskell compiler is too dumb to know that the pattern matching is actually exhaustive."

    combine :: (MonotonicBehaviour, MonotonicBehaviour) -> MonotonicBehaviour
    combine (x, y) | x == y = x
    combine (Unstable, _) = Unstable
    combine (_, Unstable) = Unstable
    combine (Unspecified, y) = y
    combine (x, Unspecified) = x
    combine (StrictlyIncreasing, y) | y `elem` [Increasing, Constant] = Increasing
    combine (StrictlyDecreasing, y) | y `elem` [Decreasing, Constant] = Decreasing
    combine (StrictlyIncreasing, _) = Unstable -- with [Strictly]Decreasing
    combine (StrictlyDecreasing, _) = Unstable -- with [Strictly]Increasing
    combine (Increasing, Decreasing) = Unstable
    combine (Increasing, Constant) = Increasing
    combine (Decreasing, Constant) = Decreasing
    combine (x, y) = combine (y, x)

    -- Returns Nothing if the fact $tag$ violates injectivity guidelines in rule $ru$
    -- If the fact is injective, it computes the shape/behaviour of the fact.
    getMaybeEqStrict :: FactTag -> ProtoRuleE -> Maybe [[MonotonicBehaviour]]
    getMaybeEqStrict tag ru =
      -- trace (show ("getMaybeEqStrict", tag, ru, combineAll (map getMaybeEqMonConclusion copies) tag)) $
      combineAll (map getMaybeEqMonConclusion copies) tag
      where
        prems = L.get rPrems ru
        copies = filter ((tag ==) . factTag) (L.get rConcs ru)
        constraints = concatMap extractConstraints (L.get preRestriction (L.get rInfo ru))
        firstTerm = headMay . factTerms

        -- duplicateFirstTerms are the first terms that appear at least twice - i.e. the corresponding fact cannot be injective
        allFirstTerms = sort $ mapMaybe firstTerm copies
        duplicateFirstTerms = S.fromList [a | (a, b) <- zip (drop 1 allFirstTerms) (take (length allFirstTerms - 1) allFirstTerms), a == b]

        -- For a given fact, computes whether it is injective and, if so, computes its shape/behaviour in the rule
        getMaybeEqMonConclusion :: LNFact -> Maybe [[MonotonicBehaviour]]
        getMaybeEqMonConclusion faConc = case firstTerm faConc of
          Nothing -> Nothing -- cannot be an injective fact if it has no arguments
          Just tConc | tConc `S.member` duplicateFirstTerms -> Nothing -- violating (2)
          Just tConc | freshFact tConc `elem` prems -> M.lookup tag candidates -- applying (2)(a)
          Just tConc -> case getPrem tConc of
            Nothing -> Nothing -- violating (2)(b)
            Just faPrem -> Just behaviours
              where
                -- The default shape for this candidate
                shape = fromJust $ M.lookup tag candidates

                -- Unfold the tuple to the right N -1 times.
                shapeTerm :: LNTerm -> Int -> [LNTerm]
                shapeTerm (viewTerm2 -> FPair t1 t2) x | x > 1 = t1 : shapeTerm t2 (x - 1)
                shapeTerm _ x | x > 1 = error "shapeTerm: the term does not have enough pairs"
                shapeTerm t x | x == 1 = [t]
                shapeTerm _ _ = error "shapeTerm: cannot take an integer with size less than 1"

                -- Unfold each term according to the default shape
                trimmedPairTerms :: LNFact -> [[LNTerm]]
                trimmedPairTerms (factTerms -> _ : terms) = zipWith shapeTerm terms (map length shape)
                trimmedPairTerms _ = error "a fact with no terms cannot be injective"

                -- Zip the matching terms from premise instance and conclusion instance
                zipped = zipWith zip (trimmedPairTerms faPrem) (trimmedPairTerms faConc)

                -- Compute the behaviour for two matching terms as computed by zip
                getBehaviour :: (LNTerm, LNTerm) -> MonotonicBehaviour
                getBehaviour (t1, t2) | t1 == t2 = Constant
                getBehaviour (t1, t2) | elemNotBelowReducible reducible t1 t2 = StrictlyIncreasing
                getBehaviour (t1, t2) | elemNotBelowReducible reducible t2 t1 = StrictlyDecreasing
                getBehaviour (t1, t2) | (t1,t2) `elem` constraints = StrictlyIncreasing
                getBehaviour (t1, t2) | (t2,t1) `elem` constraints = StrictlyDecreasing
                getBehaviour _ = Unstable

                behaviours =
                  -- trace (show("zipped,final", zipped, map (map getBehaviour) zipped)) $
                  map (map getBehaviour) zipped

        -- get the corresponding fact in the premise
        getPrem tConc = case (`filter` prems) (\faPrem -> factTag faPrem == tag && Just tConc == firstTerm faPrem) of
          [g] -> Just g
          _ -> Nothing -- if there are multiple such guards, the rule cannot be executed
