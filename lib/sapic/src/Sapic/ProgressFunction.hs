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
    from
   ,pi
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
import Data.Typeable
import Control.Monad.Catch
import Control.Monad
-- import Sapic.Exceptions
-- import Theory
import Theory.Sapic
import Sapic.Exceptions
import Sapic.ProcessUtils
-- import Theory.Model.Rule
-- import Data.Typeable
import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh
import qualified Data.Map.Strict as M

type ProgressFunction = M.Map ProcessPosition (S.Set (S.Set ProcessPosition))
 
 -- | suffix list p to each element of set *)
(<.>) :: Ord a => [a] -> S.Set [a]  -> S.Set [a]
(<.>) pos set = S.map (\pos' -> pos ++ pos' ) set 

-- | suffix list p to each element in a set of set of sets *)
(<..>) :: Ord a => [a] -> S.Set (S.Set [a]) -> S.Set (S.Set [a])
(<..>) pos setset  = S.map (\set' -> pos <.> set') setset

-- | Combinators that are exclusive, i.e., only one child can be visited
isExclusive  (Cond _)     = True
isExclusive  (CondEq _ _) = True
isExclusive  (Lookup _ _) = True
isExclusive  _            = False

-- | Actions that are blocking
isBlockingAct Rep        = True
isBlockingAct (ChIn _ _) = True

-- | determine whether process is blocking 
blocking (ProcessNull _)           = True
blocking (ProcessAction ac _ _ )   = isBlockingAct ac
blocking (ProcessComb NDC _ pl pr) = blocking pl && blocking pr
blocking _                         =  False

-- | next position to jump to
next (ProcessNull _) = S.empty
next (ProcessAction ac _ _ ) = S.singleton [1]
next (ProcessComb NDC _ pl pr) = nextOrChild pl [1] `S.union` nextOrChild pl [2]
    where nextOrChild p' pos = if blocking p' then
                                pos <.> next p'
                               else S.singleton pos
next ProcessComb{} = S.fromList $ [[1],[2]]

-- | next position to jump but consider empty position for null process, used in pi 
next0 (ProcessNull _) = S.empty
next0 (ProcessAction ac _ _ ) = S.singleton [1]
next0 (ProcessComb NDC _ pl pr) = next0OrChild pl [1] `S.union` next0OrChild pl [2]
    where next0OrChild p' pos = if blocking p' then
                                pos <.> next0 p'
                               else S.singleton pos
next0 ProcessComb{} = S.fromList [[1],[2]]

-- blocking0 (ProcessAction ac _ _ )
--         | isBlocking ac = Just (S.singleton [1])
--         | otherwise     = Nothing
-- blocking0 (ProcessComb NDC _ pl pr)
--     | (Just sl) <- blocking0 pl, (Just sr) <- blocking0 pr = Just (([1] <.>sl) `S.union` ([2]<.>sr))
--     | otherwise = Nothing
-- blocking0 _ =  Nothing

from proc = from' proc True
    where
    from' proc b 
        | ProcessNull _ <- proc  = return S.empty
        | otherwise = do
        -- |  (ProcessAction ac _ p' ) <- proc = 
        -- singletonOrEmpty (conditionAction proc b) `S.union` [1]<.> from' p' (isBlocking ac)
        -- TODO can shorten once addWithRecursive is correct
        -- | (ProcessComb comb _ pl pr) <- proc =
        res <- foldM addWithRecursive S.empty (next proc)
        return $ singletonOrEmpty (conditionAction proc b) `S.union` res
        -- `S.union`   ([1] <.> from' pl False)
        -- `S.union`   ([2] <.> from' pr False)
    singletonOrEmpty True  =  S.singleton []
    singletonOrEmpty False =  S.empty
    conditionAction proc b = not (blocking proc) && b -- condition to add singleton set is given, see Def. 14 in paper
    addWithRecursive accu pos = do
                        p'   <- processAt proc pos
                        res  <- from' p' (blocking proc)
                        return $ accu `S.union` (pos <.> res)

-- | Combine set of sets of position so that they describe alternatives (see comment for progressTo)
-- combine x y = { union of xi and yi | xi in x and yi in y}
combine x y = S.fold (combine_with y) x S.empty --

-- | Take x_i, take union with y_i for all y_i in y and add result to accumulator set1.
combine_with y x_i set1 = S.fold (\y_i set2 -> (x_i `S.union` y_i) `S.insert` set2) y set1

-- | Given a process p, find set of set of positions describing the conjunctive
-- normal form of the positions that    we need to go to.
-- For example: {{p1},{p2,p3}} means we need to go to p1 AND to either p2 or p3.
-- TODO This is massively refactored code. Remove stuff that's commented out once everything wors.
pi :: (Show ann, MonadCatch m, Typeable ann) => (AnProcess ann) -> m (S.Set (S.Set ProcessPosition))
pi  p -- corresponds to f within generate progressfunction.ml
    | blocking p = return $ ss []
    | (ProcessComb Parallel  _ pl pr) <- p =  do
                ll <- f pl
                lr <- f pr
                return $ S.union ([1] <..>  ll) ([2] <..>  lr)
    | otherwise = foldM combineWithRecursive
                            S.empty      -- accumulator, set of sets of position
                            (next0 p) -- list of p∈next^0(proc)
    -- | (ProcessNull _) <- p = return $ ss []
    -- | (ProcessAction Rep _ _ ) <-p = return $ ss []
    -- | (ProcessAction (ChIn _ _) _ _) <-p = return $ ss []
    -- | (ProcessComb comb _ pl pr) <- p 
    -- , isExclusive comb = foldM combineWithRecursive 
    --                         S.empty      -- accumulator, set of sets of position
    --                         (next0 proc) -- list of p∈next^0(proc) 
    -- | (ProcessComb NDC _ pl pr) <- p 
    -- , Just psl <- blocking0 pl, Just psr <- blocking0 pr = return $ ss [] 
    -- | (ProcessComb NDC _ pl pr) <- p
    -- , Just psl <- blocking0 pl, Nothing <- blocking0 pr = do
    --           lr <- f pr
    --           foldM combineWithRecursive 
    --                     ([2] <..>  lr) -- accumulator start with rhs positions
    --                     ([1] <.>  psl) -- fold over lhs positions
    -- | (ProcessComb NDC _ pl pr) <- p
    -- , Nothing <- blocking0 pl, Just psr <- blocking0 pr = do
    --           ll <- f pl
	      -- foldM combineWithRecursive ([1] <..>  ll) ([2] <.>  psr)
    -- | (ProcessComb NDC _ pl pr) <- p
    -- , Nothing <- blocking0 pl, Nothing <- blocking0 pr =  do
    --             ll <- f pl
    --             lr <- f pr
    --             return $ combine ([1]  <..>  ll) ([2] <..>  lr)
    -- | (ProcessComb Parallel  _ pl pr) <- p =  do
    --             ll <- f pl
    --             lr <- f pr
    --             return $ S.union ([1] <..>  ll) ([2] <..>  lr) 
    -- | (ProcessAction _ _ p')  <- p = do l' <- f p'
    --                                     return $ [1] <..> l'
    where ss x = S.singleton ( S.singleton x) -- shortcut for singleton set of singleton set
          f  =  pi  -- shortcut for recursive call
          combineWithRecursive  acc pos = do -- combine pss with positions from recursive call (case of nested NDCs)
                        proc'   <- (processAt p pos)
                        lpos <- f proc'
                        return $ combine (pos <..> lpos) acc 
