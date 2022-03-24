{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Computate an under-approximation to the set of all facts with unique
-- instances, i.e., fact whose instances never occur more than once in a
-- state. We use this information to reason about protocols that exploit
-- exclusivity of linear facts.
module Theory.Tools.InjectiveFactInstances (

  -- * Computing injective fact instances.
  simpleInjectiveFactInstances
  ) where

import           Extension.Prelude   (sortednub)

-- import           Control.Applicative
import           Control.Monad.Fresh
import           Data.Label
import qualified Data.Set            as S
import           Data.List
import           Data.Maybe
import           Safe                (headMay)
import           Control.Applicative (empty)
import           Debug.Trace

import           Theory.Model

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
-- Additionally, we determine the term positions that always stay the same
-- And the term positions that are strictly increasing (elemNotBelowReducible)
--
-- TODO-MY: extend this to capture pairs, e.g., use [Int] as description of the position in the pair-tree
--   intersection-merge should be done with [4,1] representing [4,1,0] as well (as a kind of hierarchy)
--   i.e., { [4,1] } ∩ { [4,1,2] } = { [4,1,2] }
--   well, that intersection style probably does not work for subterms interfering with the pairs...
--
-- We exclude facts that are not copied in a rule, as they are already handled
-- properly by the naive backwards reasoning.
simpleInjectiveFactInstances :: FunSig -> [ProtoRuleE] -> S.Set (FactTag, (S.Set Int, S.Set Int))
simpleInjectiveFactInstances reducible rules = S.fromList $ do
    tag <- candidates
    let resultTag = intersectAll (map (getMaybeEqStrict tag) rules) (factTagArity tag)
    case resultTag of
      Just (eqPos, monPos) -> return (tag, (S.delete 0 eqPos, monPos))  -- remove the 0-position from eqPos as this is the ~fr
      Nothing -> empty
  where
    candidates = sortednub $ do
        ru  <- rules
        tag <- factTag <$> get rConcs ru
        guard $    (factTagMultiplicity tag == Linear)
                && (tag `elem` (factTag <$> get rPrems ru))
        return tag

    intersectAll :: [Maybe (S.Set Int, S.Set Int)] -> Int -> Maybe (S.Set Int, S.Set Int)
    intersectAll list _ | any isNothing list = Nothing  -- if any of the elements say that the tag is not injective, then return nothing
    intersectAll (Just (eqPos, monPos) : Just (eqPos2, monPos2) : rest) maxN = intersectAll (Just (eqPos `S.intersection` eqPos2, monPos `S.intersection` monPos2):rest) maxN
    intersectAll [x] _ = x
    intersectAll [] maxN = Just (S.fromList [1..maxN-1], S.fromList [1..maxN-1])
    intersectAll _ _ = error "the haskell compiler is too dumb to know that the pattern matching is actually exhaustive"

    -- | returns Nothing if the fact $tag$ violates injectivity guidelines in rule $ru$
    -- otherwise, two sets of positions are returned
    --   - the first  to indicate where the arguments do not change
    --   - the second to indicate where the arguments are strictly increasing
    -- all conclusions of the given FactTag have to fulfill that
    getMaybeEqStrict :: FactTag -> ProtoRuleE -> Maybe (S.Set Int, S.Set Int)
    getMaybeEqStrict tag ru = --trace (show ("getMaybeEqStrict", tag, ru, intersectAll (map getMaybeEqMonConclusion copies) (factTagArity tag))) $
        intersectAll (map getMaybeEqMonConclusion copies) (factTagArity tag)
      where
        prems              = get rPrems ru
        copies             = filter ((tag ==) . factTag) (get rConcs ru)
        firstTerm          = headMay . factTerms

        -- duplicateFirstTerms are the first terms that appear at least twice - i.e. the corresponding fact cannot be injective
        allFirstTerms = sort [t | c <- copies, let Just t = firstTerm c]
        duplicateFirstTerms = S.fromList [a | (a, b) <- zip (drop 1 allFirstTerms) (take (length allFirstTerms - 1) allFirstTerms), a==b]

        -- behaves like allCopiesGuarded, but specific to one conclusion instead of all conclusions
        getMaybeEqMonConclusion :: LNFact -> Maybe (S.Set Int, S.Set Int)
        getMaybeEqMonConclusion faConc = case firstTerm faConc of
            Nothing    -> Nothing  -- cannot be an injective fact if it has no arguments
            Just tConc | tConc `S.member` duplicateFirstTerms -> Nothing  -- violating (2)
            Just tConc | freshFact tConc `elem` prems -> Just (allPositions, allPositions)  -- applying (2)(a)
              where allPositions = S.fromList [1 .. factTagArity tag - 1]
            Just tConc -> case getPrem tConc of
               Nothing -> Nothing  -- violating (2)(b)
               Just faPrem -> Just (eqPos, monPos)
                 where
                   zipped = zip3 [0 .. factTagArity tag - 1] (factTerms faPrem) (factTerms faConc)
                   eqPos = S.fromList [ x | (x, p, c) <- zipped, p==c]
                   monPos = S.fromList [ x | (x, p, c) <- zipped, elemNotBelowReducible reducible p c, p /= c]

        -- get the corresponding fact in the premise
        getPrem tConc = case (`filter` prems) (\faPrem -> factTag faPrem == tag && Just tConc == firstTerm faPrem) of
            [g] -> Just g
            _   -> Nothing  -- if there are multiple such guards, the rule cannot be executed

