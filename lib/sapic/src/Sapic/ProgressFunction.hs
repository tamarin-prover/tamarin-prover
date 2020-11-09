{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann 
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute a functiont hat maps positions in a process to where they will need
-- to move to ensure local progress whereever possible 
module Sapic.ProgressFunction (
    pfFrom
   ,pf
   ,ProgressFunction
   ,pfRange
   ,pfInv
) where
import Data.Typeable
import Control.Monad.Catch
import Control.Monad
import Theory.Sapic
import Sapic.ProcessUtils
import qualified Data.Set                   as S
import qualified Data.List                   as L
import qualified Data.Map.Strict as M

type ProgressFunction = M.Map ProcessPosition (S.Set (S.Set ProcessPosition))
 
--- | suffix list p to each element of set *)
(<.>) :: Ord a => [a] -> S.Set [a]  -> S.Set [a]
(<.>) pos set = S.map (\pos' -> pos ++ pos' ) set 

--- | suffix list p to each element in a set of set of sets *)
(<..>) :: Ord a => [a] -> S.Set (S.Set [a]) -> S.Set (S.Set [a])
(<..>) pos setset  = S.map (\set' -> pos <.> set') setset

-- -- | Combinators that are exclusive, i.e., only one child can be visited
-- isExclusive  (Cond _)     = True
-- isExclusive  (CondEq _ _) = True
-- isExclusive  (Lookup _ _) = True
-- isExclusive  _            = False

-- | Actions that are blocking
isBlockingAct :: SapicAction -> Bool
isBlockingAct Rep        = True
isBlockingAct (ChIn _ _) = True
isBlockingAct _          = False

-- | determine whether process is blocking 
blocking :: AnProcess ann -> Bool
blocking (ProcessNull _)           = True
blocking (ProcessAction ac _ _ )   = isBlockingAct ac
blocking (ProcessComb NDC _ pl pr) = blocking pl && blocking pr
blocking _                         =  False

-- | next position to jump to
next :: (Num a, Ord a) => AnProcess ann -> S.Set [a]
next (ProcessNull _) = S.empty
next (ProcessAction _ _ _ ) = S.singleton [1]
next (ProcessComb NDC _ pl pr) = nextOrChild pl [1] `S.union` nextOrChild pr [2]
    where nextOrChild p' pos = if blocking p' then
                                pos <.> next p'
                               else S.singleton pos
next ProcessComb{} = S.fromList $ [[1],[2]]

-- | next position to jump but consider empty position for null process, used in pi 
next0 :: (Num a, Ord a) => AnProcess ann -> S.Set [a]
next0 (ProcessNull _) = S.singleton []
next0 (ProcessAction _ _ _ ) = S.singleton [1]
next0 (ProcessComb NDC _ pl pr) = next0OrChild pl [1] `S.union` next0OrChild pr [2]
    where next0OrChild p' pos = if blocking p' then
                                pos <.> next0 p'
                               else S.singleton pos
next0 ProcessComb{} = S.fromList [[1],[2]]

pfFrom :: (MonadCatch m, Show ann, Typeable ann) => AnProcess ann -> m (S.Set ProcessPosition)
pfFrom process = from' process True
    where
    from' proc b 
        | ProcessNull _ <- proc  = return S.empty
        | otherwise = do
        res <- foldM (addWithRecursive proc) S.empty (next proc)
        return $ singletonOrEmpty (conditionAction proc b) `S.union` res
    singletonOrEmpty True  =  S.singleton []
    singletonOrEmpty False =  S.empty
    conditionAction proc b = not (blocking proc) && b -- condition to add singleton set is given, see Def. 14 in paper
    addWithRecursive proc accu pos = do
                        p'   <- processAt proc pos
                        res  <- from' p' (blocking proc)
                        return $ accu `S.union` (pos <.> res)

-- | Combine set of sets of position so that they describe alternatives (see comment for progressTo)
-- combine x y = { union of xi and yi | xi in x and yi in y}
combine :: Ord a => S.Set (S.Set a) -> S.Set (S.Set a) -> S.Set (S.Set a)
combine x y = S.foldr  (combine_with y) S.empty x

-- | Take x_i, take union with y_i for all y_i in y and add result to accumulator set1.
combine_with :: Ord a => S.Set (S.Set a) -> S.Set a -> S.Set (S.Set a) -> S.Set (S.Set a)
combine_with y x_i set1 = S.foldr (\y_i set2 -> (x_i `S.union` y_i) `S.insert` set2) set1 y

-- | Given a process p, find set of set of positions describing the conjunctive
-- normal form of the positions that    we need to go to.
-- For example: {{p1},{p2,p3}} means we need to go to p1 AND to either p2 or p3.
-- Correspond to f in Def. 15
f :: (Show ann, MonadCatch m, Typeable ann) => (AnProcess ann) -> m (S.Set (S.Set ProcessPosition))
f  p -- corresponds to f within generate progressfunction.ml
    | blocking p = return $ ss []
    | (ProcessComb Parallel  _ pl pr) <- p =  do
                ll <- f pl
                lr <- f pr
                return $ S.union ([1] <..>  ll) ([2] <..>  lr)
    | otherwise = foldM combineWithRecursive
                            (S.singleton S.empty) -- accumulator, set of sets of position
                                                  -- not that the Singleton set of the empty set is
                                                  -- the neutral element with respect to combine
                                                  -- the empty set combined with anything gives an emptyset
                            (next0 p) -- list of p∈next^0(proc)
    where ss x = S.singleton ( S.singleton x) -- shortcut for singleton set of singleton set
          combineWithRecursive acc pos = do -- combine pss with positions from recursive call (case of nested NDCs)
                        proc'   <- (processAt p pos)
                        lpos <- f proc'
                        return $ combine (pos <..> lpos) acc 

-- | Compute progress function of proc
pf :: (Show ann, MonadCatch m, Typeable ann) => AnProcess ann -> ProcessPosition -> m (S.Set (S.Set ProcessPosition))
pf proc pos = do proc' <- processAt proc pos
                 res  <- f proc'
                 return $ pos <..> res

flatten :: Ord a =>  S.Set (S.Set a) -> S.Set a
flatten = S.foldr S.union S.empty 

pfRange' :: (Show ann, Typeable ann, MonadCatch m) => AnProcess ann -> m (S.Set (ProcessPosition, ProcessPosition))
pfRange' proc = do 
                   froms <- pfFrom proc
                   res   <- foldM  mapFlat S.empty froms
                   return res
                   where
                      mapFlat acc pos = do res <- flatten <$> pf proc pos 
                                           return (acc `S.union` S.map (\r -> (r,pos)) res)

pfRange :: (Show ann, Typeable ann, MonadCatch m) => AnProcess ann -> m (S.Set ProcessPosition)
pfRange proc = do 
                  set <- pfRange' proc
                  return $ S.map fst  set

pfInv :: (Show ann, Typeable ann, MonadCatch m) => AnProcess ann -> m (ProcessPosition -> Maybe ProcessPosition)
pfInv proc = do
                  set <- pfRange' proc
                  return $ \x -> snd <$> L.find (\(to,_) -> to == x ) (S.toList set)
