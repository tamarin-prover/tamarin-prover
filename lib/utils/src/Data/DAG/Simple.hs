-- | Simple  vertice list based representation of DAGs and some common operations on it.
module Data.DAG.Simple (
    toposort
  , reachableSet
  , cyclic
) where


import Data.List
import qualified Data.Set as S

import Control.Basics
import Control.Monad.Writer


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
        preds = [ e | (e,e') <- dag, e' == x ]


-- | Compute the set of nodes reachable from the given set of nodes.
reachableSet :: Ord a => [a] -> [(a,a)] -> S.Set a
reachableSet start dag = 
    foldl' visit S.empty start
  where 
    visit visited x 
      | x `S.member` visited = visited
      | otherwise            =
          foldl' visit (S.insert x visited) succs
      where
        succs = [ e' | (e,e') <- dag, e == x ]

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

