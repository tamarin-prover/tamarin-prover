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
import           Safe                (headMay)

import           Theory.Model

-- | Compute a simple under-approximation to the set of facts with injective
-- instances. A fact-tag is has injective instances, if there is no state of
-- the protocol with more than one instance with the same term as a first
-- argument of the fact-tag.
--
-- We compute the under-approximation by checking that
-- (1) the fact-tag is linear,
-- (2) every introduction of such a fact-tag is protected by a Fr-fact of the
--     first term, and
-- (3) every rule has at most one copy of this fact-tag in the conclusion and
--     the first term arguments agree.
--
-- We exclude facts that are not copied in a rule, as they are already handled
-- properly by the naive backwards reasoning.
simpleInjectiveFactInstances :: [ProtoRuleE] -> S.Set FactTag
simpleInjectiveFactInstances rules = S.fromList $ do
    tag <- candidates
    guard (all (guardedSingletonCopy tag) rules)
    return tag
  where
    candidates = sortednub $ do
        ru  <- rules
        tag <- factTag <$> get rConcs ru
        guard $    (factTagMultiplicity tag == Linear)
                && (tag `elem` (factTag <$> get rPrems ru))
        return tag

    guardedSingletonCopy tag ru =
        length copies <= 1 && all guardedCopy copies
      where
        prems              = get rPrems ru
        copies             = filter ((tag ==) . factTag) (get rConcs ru)
        firstTerm          = headMay . factTerms

        -- True if there is a first term and a premise guarding it
        guardedCopy faConc = case firstTerm faConc of
            Nothing    -> False
            Just tConc -> freshFact tConc `elem` prems || guardedInPrems tConc

        -- True if there is a premise with the same tag and first term
        guardedInPrems tConc = (`any` prems) $ \faPrem ->
            factTag faPrem == tag && maybe False (tConc ==) (firstTerm faPrem)

