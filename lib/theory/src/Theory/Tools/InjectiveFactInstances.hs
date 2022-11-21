{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
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
-- exclusivity of facts.
module Theory.Tools.InjectiveFactInstances (

  -- * Computing injective fact instances.
  MonotonicBehaviour(..)
  , simpleInjectiveFactInstances
  ) where

import           Extension.Prelude   (sortednub)

-- import           Control.Applicative
import           Control.Monad.Fresh
import           Control.DeepSeq

import           GHC.Generics        (Generic)
import           Data.Label          as L
import qualified Data.Set            as S
import qualified Data.Map            as M
import           Data.List
import           Data.Maybe
import           Data.Binary
import           Safe                (headMay)
import           Control.Applicative (empty)
import           Debug.Trace

import           Theory.Model
--import Control.DeepSeq (NFData)

-- unspecified = there is no rule using this fact
-- unstable = increasing and decreasing or not at all related inputs and outputs
data MonotonicBehaviour = Constant | Increasing | Decreasing | StrictlyIncreasing | StrictlyDecreasing | Unstable | Unspecified
  deriving( Eq, Ord, Generic, NFData, Binary )

instance Show MonotonicBehaviour where
    show Constant = "="
    show Increasing = "≤"
    show Decreasing = "≥"
    show StrictlyIncreasing = "<"
    show StrictlyDecreasing = ">"
    show Unstable = "."
    show Unspecified = "?"


-- | Compute a simple under-approximation to the set of facts with injective
-- instances. A fact-tag is has injective instances, if there is no state of
-- the protocol with more than one instance with the same term as a first
-- argument of the fact-tag.
--
-- We compute the under-approximation by checking that
-- for each occurrence of the fact-tag in a rule:
-- there is no other occurrence with the same first term and
--   (a) either there is a Fr-fact of the first term as a premise
--   (b) or there is exactly one consume fact-tag with the same first term in a premise
--
-- Additionally, we determine the term positions that are
-- - Constant
-- - Increasing/Decreasing according to `elemNotBelowReducible` and equality
-- - Strictly Increasing/Decreasing according to `elemNotBelowReducible`
--
-- Positions can also be inside tuples if these tuples are always explicitly used in the rules.
--
-- We exclude facts that are not copied in a rule, as they are already handled
-- properly by the naive backwards reasoning.
simpleInjectiveFactInstances :: [ProtoRuleE] -> S.Set FactTag  --TODO-Subterm when enabling subterms, change it to  FunSig -> [ProtoRuleE] -> S.Set (FactTag, [[MonotonicBehaviour]])
simpleInjectiveFactInstances rules = S.fromList $ do  --TODO-Subterm when enabling subterms, add reducible before rules
    tag <- M.keys shapes
    let resultTag = combineAll (map (getInjectiveMon tag) rules) tag
    case resultTag of
      Just behaviours -> return tag --(tag, behaviours)  -- remove the 0-position from eqPos as this is the ~fr
      Nothing -> empty
  where

    getPairTerms :: LNTerm -> [LNTerm]
    getPairTerms (viewTerm2 -> FPair t1 t2) = t1 : getPairTerms t2
    getPairTerms t = [t]

    shapes :: M.Map FactTag [[MonotonicBehaviour]]  -- basic filtering and finding shape (the more fine-grained filtering one comes later)
    shapes = M.fromListWith combineShapes $ do
        ru  <- rules
        prem <- L.get rPrems ru
        guard (not (null $ factTerms prem))
        let tag = factTag prem
        if factTagMultiplicity tag == ReadOnly
          then return (tag, getShape prem)
          else do
            conc <- L.get rConcs ru
            guard (factTag conc == tag)
            return (tag, combineShapes (getShape conc) (getShape prem))

        where
          getShape :: LNFact -> [[MonotonicBehaviour]]
          getShape (factTerms->_:terms) = map (flip replicate Unspecified . length . getPairTerms) terms
          getShape _ = error "a fact without terms cannot be injective (as id is missing)"

          combineShapes :: [[MonotonicBehaviour]] -> [[MonotonicBehaviour]] -> [[MonotonicBehaviour]]
          combineShapes behaviours behaviours1 = map (map fst) $ zipWith zip behaviours behaviours1  -- zip automatically orients itself on the shorter list



    combineAll :: [Maybe [[MonotonicBehaviour]]] -> FactTag -> Maybe [[MonotonicBehaviour]]
    combineAll list _ | any isNothing list = Nothing  -- if any of the elements say that the tag is not injective, then return nothing
    combineAll (Just behaviours : Just behaviours1 : rest) tag = --trace (show("combineAll", behaviours, behaviours1, (map (map combine) $ zipWith zip behaviours behaviours1))) $
                                                                 combineAll (Just (map (map combine) $ zipWith zip behaviours behaviours1):rest) tag
    combineAll [x] _ = x
    combineAll [] tag = M.lookup tag shapes  --start with the empty shape of Unspecified
    combineAll _ _ = error "the haskell compiler is too dumb to know that the pattern matching is actually exhaustive"

    combine :: (MonotonicBehaviour, MonotonicBehaviour) -> MonotonicBehaviour
    combine (x, y) | x == y = x
    combine (Unstable, _) = Unstable
    combine (_, Unstable) = Unstable
    combine (Unspecified, y) = y
    combine (x, Unspecified) = x
    combine (StrictlyIncreasing, y) | y `elem` [Increasing, Constant] = Increasing
    combine (StrictlyDecreasing, y) | y `elem` [Decreasing, Constant] = Decreasing
    combine (StrictlyIncreasing, _) = Unstable  -- with [Strictly]Decreasing
    combine (StrictlyDecreasing, _) = Unstable  -- with [Strictly]Increasing
    combine (Increasing, Decreasing) = Unstable
    combine (Increasing, Constant) = Increasing
    combine (Decreasing, Constant) = Decreasing
    combine (x, y) = combine (y, x)

    -- | returns Nothing if the fact $tag$ violates injectivity guidelines in rule $ru$
    -- otherwise, a list of MonotonicBehaviour is returned
    --   - the list is nested such that it can capture terms in tuples
    --   - i.e., if there are no tuples, a list of singletons is returned
    -- all conclusions of the given FactTag have to fulfill that
    getInjectiveMon :: FactTag -> ProtoRuleE -> Maybe [[MonotonicBehaviour]]
    getInjectiveMon tag ru = --trace (show ("getInjectiveMon", tag, ru, map getInjectiveMonConc concs, map getInjectiveMonPrem prems)) $
        combineAll (map getInjectiveMonConc concs {- ++ map getInjectiveMonPrem prems -}) tag
      where
        prems              = filter ((tag ==) . factTag) $ L.get rPrems ru
        freshPrems         = filter ((FreshFact ==) . factTag) $ L.get rPrems ru
        concs              = filter ((tag ==) . factTag) $ L.get rConcs ru
        firstTerm          = headMay . factTerms

        -- duplicateFirstTerms are the first terms that appear at least twice - i.e. the corresponding fact cannot be injective
        allFirstTerms = sort [t | c <- concs, let Just t = firstTerm c]
        duplicateFirstTerms = S.fromList [a | (a, b) <- zip (drop 1 allFirstTerms) (take (length allFirstTerms - 1) allFirstTerms), a==b]

        {-
        -- DISABLED as we only concern the writing-chain for any injectiveness simplifications/contradictions)
        -- advantage of disabling: we can often have a strictly increasing < instead of just increasing ≤
        getInjectiveMonPrem :: LNFact -> Maybe [[MonotonicBehaviour]]
        getInjectiveMonPrem (Fact t@(ProtoFact ReadOnly _ _) _ _) | tag == t = map (map $ const Constant) <$> M.lookup tag shapes
        getInjectiveMonPrem _                                                = M.lookup tag shapes
        -}

        -- behaves like getInjectiveMon, but specific to one conclusion instead of all conclusions
        getInjectiveMonConc :: LNFact -> Maybe [[MonotonicBehaviour]]
        getInjectiveMonConc faConc = case firstTerm faConc of
            Nothing                                           -> Nothing  -- cannot be an injective fact if it has no arguments
            Just tConc | tConc `S.member` duplicateFirstTerms -> Nothing  -- violating (2)
            Just tConc | freshFact tConc `elem` freshPrems    -> M.lookup tag shapes  -- applying (2)(a)
            Just tConc -> case getPrem tConc of
              Nothing                                         -> Nothing  -- violating (2)(b)
              Just faPrem                                     -> Just behaviours
                where
                  shape = fromJust $ M.lookup tag shapes
                  
                  shapeTerm :: LNTerm -> Int -> [LNTerm]
                  shapeTerm (viewTerm2 -> FPair t1 t2) x | x>1 = t1 : shapeTerm t2 (x-1)
                  shapeTerm _ x | x>1 = error "shapeTerm: the term does not have enough pairs"
                  shapeTerm t x | x==1 = [t]
                  shapeTerm _ _ = error "shapeTerm: cannot take an integer with size less than 1" 
                  
                  trimmedPairTerms :: LNFact -> [[LNTerm]]
                  trimmedPairTerms (factTerms->_:terms) = zipWith shapeTerm terms (map length shape)
                  trimmedPairTerms _ = error "a fact with no terms cannot be injective"

                  zipped = zipWith zip (trimmedPairTerms faPrem) (trimmedPairTerms faConc)

                  getBehaviour :: (LNTerm, LNTerm) -> MonotonicBehaviour
                  getBehaviour (t1, t2) | t1 == t2 = Constant
                  --getBehaviour (t1, t2) | elemNotBelowReducible reducible t1 t2 = StrictlyIncreasing
                  --getBehaviour (t1, t2) | elemNotBelowReducible reducible t2 t1 = StrictlyDecreasing  --TODO-Subterm when enabling subterms, uncomment these two lines
                  getBehaviour _ = Unstable

                  behaviours = --trace (show("zipped,final", zipped, map (map getBehaviour) zipped)) $
                               map (map getBehaviour) zipped

        -- get the corresponding fact in the premise
        getPrem tConc = case (`filter` prems) (\faPrem -> factMultiplicity faPrem == Consume && Just tConc == firstTerm faPrem) of
            [g] -> Just g
            _   -> Nothing  -- if there are multiple such guards, the rule cannot be executed

