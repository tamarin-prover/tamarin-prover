-- FIXME: Better solution for dfsLoopBreakers
{-# LANGUAGE FlexibleContexts #-}
-- |
-- Copyright   : (c) 2010,2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Simple  vertice list based representation of DAGs and some common operations on it.
module Data.DAG.Simple (
  -- * Computing with binary relations
    Relation
  , inverse
  , image
  , reachableSet
  , restrict

  -- ** Cycles
  , dfsLoopBreakers
  , cyclic
  , toposort

) where


import           Control.Basics
import           Control.Monad.Writer
import           Control.Monad.RWS

import           Data.List
import qualified Data.DList as D
import qualified Data.Set   as S

-- import Test.QuickCheck.Property (label)
-- import Test.QuickCheck (quickCheck)

-- | Produce a topological sorting of the given relation. If the relation is
-- cyclic, then the result is at least some permutation of all elements of
-- the given relation.
toposort :: Ord a => [(a, a)] -> [a]
toposort dag = 
    execWriter . foldM visit S.empty $ map fst dag ++ map snd dag
  where 
    visit visited x 
      | x `S.member` visited = return visited
      | otherwise            =
          foldM visit (S.insert x visited) preds <* tell (pure x)
      where
        preds = x `image` inverse dag


-- | Compute the set of nodes reachable from the given set of nodes.
reachableSet :: Ord a => [a] -> [(a,a)] -> S.Set a
reachableSet start dag = 
    foldl' visit S.empty start
  where 
    visit visited x 
      | x `S.member` visited = visited
      | otherwise            =
          foldl' visit (S.insert x visited) (x `image` dag)

-- | Is the relation cyclic.
cyclic :: Ord a => [(a,a)] -> Bool
cyclic rel = 
    maybe True (const False) $ foldM visitForest S.empty $ map fst rel
  where 
    visitForest visited x
      | x `S.member` visited = return visited
      | otherwise            = findLoop S.empty visited x

    findLoop parents visited x 
      | x `S.member` parents = mzero
      | x `S.member` visited = return visited
      | otherwise            = 
          S.insert x <$> foldM (findLoop parents') visited next
      where
        next     = [ e' | (e,e') <- rel, e == x ]
        parents' = S.insert x parents


-- TODO: Consider implementing something along the lines of Ann Becker, Dan
-- Geiger, Optimization of Pearl's method of conditioning and greedy-like
-- approximation algorithms for the vertex feedback set problem, Artificial
-- Intelligence, Volume 83, Issue 1, May 1996, Pages 167-188, ISSN 0004-3702,
-- 10.1016/0004-3702(95)00004-6.
-- <http://www.sciencedirect.com/science/article/pii/0004370295000046>.

-- | Compute a minimal set of loop-breakers using a greedy DFS strategy. A set
-- of loop-breakers is a set of nodes such that removing them ensures the
-- acyclicity of the relation. It is minimal, if no node can be removed from
-- the set.
dfsLoopBreakers :: Ord a => [(a,a)] -> [a]
dfsLoopBreakers rel = 
    D.toList $ snd $ execRWS (mapM_ (visit . fst) rel) () S.empty
  where 
    visit x = do
        visited <- gets (S.member x)
        unless visited $ findLoopBreakers S.empty x

    -- PRE: x0 is not yet visited
    findLoopBreakers parents0 x = do
        modify (S.insert x)
        let parents = S.insert x parents0
            ys      = x `image` rel
        if any (`S.member` parents) ys
          then tell (return x) 
          else forM_ ys $ \y -> do 
                   visited <- gets (S.member y)
                   unless visited $ findLoopBreakers parents y

-- | A relation represented as a list of tuples.
type Relation a = [(a,a)]

-- | Restrict a relation to elements satisfying a predicate.
restrict :: (a -> Bool) -> Relation a -> Relation a
restrict p = filter (\(x,y) -> p x && p y)

-- | The image of an element under a 'Relation'.
image :: Eq a => a -> Relation a -> [a]
image x rel = [ y' | (x', y') <- rel, x == x' ]

-- | The inverse of a 'Relation'.
inverse :: Relation a -> Relation a
inverse rel = [ (y,x) | (x, y) <- rel ]

{-
prop_dfsLoopBreakers noSelfLoops rel0
  | cyclic rel = label cycleLabel (minimal && not (cyclic (rel' breakers)))
  | otherwise  = label "acyclic" (null breakers)
  where
    -- remove (x,x) entries in half of the cases
    removeSelfLoops | noSelfLoops = filter (not . (uncurry (==)))
                    | otherwise   = id
    -- restrict the relation to get more cyclic cases
    rel      =  removeSelfLoops $ map ((`mod` (20 :: Int)) *** (`mod` 20)) rel0
    rel' bs  = restrict (not . (`elem` bs)) rel
    breakers = dfsLoopBreakers rel
    cycleLabel | any (uncurry (==)) rel = "cyclic (with self-loop)"
               | otherwise              = "cyclic (no self-loop)"
    -- true if loop breakers are minimal
    minimal = all (\b -> cyclic (rel' (filter (/= b) breakers))) breakers
-}
