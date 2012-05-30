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
module Theory.Tools.UniqueFactInstances (

  -- * Computing unique fact instances.
  simpleUniqueFactInstances
  ) where

import           Extension.Prelude   (sortednub)

import           Control.Applicative
import           Control.Monad.Fresh
import           Data.Label
import qualified Data.Set            as S

import           Theory.Model

-- | Compute a simple under-approximation to the set of facts with uniqe
-- instances. A fact-tag is guaranteed to have uniqe instances, if it never
-- occurs twice in the conclusions of a rule and each of its occurrences in
-- the conclusion of a rule is guarded by an equal premise or a Fr-fact
-- generating one of the terms used in the fact that we are analyzing.
--
-- We exclude facts that are not copied in a rule, as they are already handled
-- properly by the naive backwards reasoning.
simpleUniqueFactInstances :: [ProtoRuleE] -> S.Set FactTag
simpleUniqueFactInstances rules = S.fromList $ do
    tag <- candidates
    guard (all (guardedSingletonCopy tag) rules)
    return tag
  where
    candidates = sortednub $ do
        ru <- rules
        filter (`elem` (factTag <$> get rPrems ru)) (factTag <$> get rConcs ru)

    guardedSingletonCopy tag ru = and $ do
        copy <- filter ((tag ==) . factTag) (get rConcs ru)
        return $
             (length copies <= 1)
          && (    (copy `elem` get rPrems ru)
               || any (\t -> freshFact t `elem` get rPrems ru) (factTerms copy)
             )
      where
        copies = filter ((tag ==) . factTag) (get rConcs ru)
