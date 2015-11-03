{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Computate the loop-breakers in the premise-conclusion graph of a set of
-- multiset rewriting rules.
module Theory.Tools.LoopBreakers (

  -- * Computing loop breakers for solving premises
  useAutoLoopBreakersAC
  ) where

-- import Control.Applicative
import Control.Monad.Fresh
import Control.Monad.Reader

import Data.DAG.Simple

import Theory.Model


-- | An over-approximation of the dependency of solving premises. An element
-- @((fromRu, fromPrem), (toRu, toPrem))@ denotes that solving the premise
-- @(fromRu,fromPrem)@ might lead to a case where the premise @(toRu, toPrem)@
-- is open.
premSolvingRelAC :: (a -> [(PremIdx, LNFact)])  -- ^ Enumerate premises
                 -> (a -> [(ConcIdx, LNFact)])  -- ^ Enumerate conclusions
                 -> (a -> [LNSubstVFresh])      -- ^ Enumerate variants
                 -> [a]                         -- ^ Base carrier
                 -> WithMaude (Relation (a, PremIdx))
premSolvingRelAC ePrems eConcs eVariants rules = reader $ \hnd -> do
    (toRu, from) <- dataflowRelAC hnd
    (toPrem, _)  <- ePrems toRu
    return (from, (toRu, toPrem))
  where
    -- An over-approxmiation of the dataflow relation. An element @(fromRu,
    -- (toRu, toPrem))@ denotes that there is a conclusion of @fromRu@
    -- unifying with the premise @(toRu, toPrem)@.
    dataflowRelAC hnd = do
        ruFrom <- rules
        ruTo   <- rules
        (premIdx, premFa0) <- ePrems ruTo
        guard $ or $ do
            premFa <- instances ruTo premFa0
            concFa <- instances ruFrom =<< (snd <$> eConcs ruFrom)
            let concFaFresh = rename concFa `evalFresh` avoid premFa
            return $ (`runReader` hnd) (unifiableLNFacts concFaFresh premFa)
        return (ruFrom, (ruTo, premIdx))

    instances ru fa = do
        subst <- eVariants ru
        return (apply (subst `freshToFreeAvoiding` fa) fa)


-- | Replace all loop-breaker information with loop-breakers computed
-- automatically from the dataflow relation 'dataflowRelAC'.
useAutoLoopBreakersAC
  :: Ord a
  => (a -> [(PremIdx, LNFact)])  -- ^ Enumerate premises
  -> (a -> [(ConcIdx, LNFact)])  -- ^ Enumerate conclusions
  -> (a -> [LNSubstVFresh])      -- ^ Enumerate variants
  -> ([PremIdx] -> a -> a)       -- ^ Add annotation
  -> [a]                         -- ^ Original rules
  -> WithMaude ([a], Relation (a, PremIdx), [(a, PremIdx)])
  -- ^ Annotated rules and the premise solving relation
useAutoLoopBreakersAC ePrems eConcs eVariants addAnn rules =
    reader $ \hnd ->
      let solveRel = (`runReader` hnd) $
              premSolvingRelAC ePrems eConcs eVariants rules
          breakers = dfsLoopBreakers $ solveRel
      in ( do ru <- rules
              return (addAnn [ u | (ru', u) <- breakers, ru == ru' ] ru)
         , solveRel
         , breakers
         )

