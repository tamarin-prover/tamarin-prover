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
import           Safe                (headMay)

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
--       (b) or there is the same fact-tag with the same first term in a premise
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
        all guardedCopy copies
      where
        prems              = get rPrems ru
        copies             = filter ((tag ==) . factTag) (get rConcs ru)
        firstTerm          = headMay . factTerms
        
        -- duplicateFirstTerms are the first terms that appear at least twice - i.e. the corresponding fact cannot be injective 
        allFirstTerms = sort [t | c <- copies, let Just t = firstTerm c]
        duplicateFirstTerms = S.fromList [a | (a, b) <- zip (drop 1 allFirstTerms) (take (length allFirstTerms - 1) allFirstTerms), a==b]
        
        -- True if there is a first term and a premise guarding it
        guardedCopy faConc = case firstTerm faConc of
            Nothing    -> False
            Just tConc -> tConc `S.notMember` duplicateFirstTerms && (freshFact tConc `elem` prems || guardedInPrems tConc)

        -- True if there is a premise with the same tag and first term
        guardedInPrems tConc = (`any` prems) $ \faPrem ->
            factTag faPrem == tag && maybe False (tConc ==) (firstTerm faPrem)

