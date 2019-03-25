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

blocking :: (Num a, Ord a) => AnProcess ann -> Maybe (S.Set [a])
blocking (ProcessNull _) = Just (S.singleton [1])
blocking (ProcessAction Rep _ _ ) = Just (S.singleton [1])
blocking (ProcessAction (ChIn _ _) _ _) = Just (S.singleton [1])
blocking (ProcessComb NDC _ pl pr) 
    | (Just sl) <- blocking pl, (Just sr) <- blocking pr = Just (([1] <.>sl) `S.union` ([2]<.>sr))
    | otherwise = Nothing
blocking _ =  Nothing


-- | Combine set of sets of position so that they describe alternatives (see comment for progressTo)
-- combine x y = { union of xi and yi | xi in x and yi in y}
combine x y = S.fold (combine_with y) x S.empty --

-- | Take x_i, take union with y_i for all y_i in y and add result to accumulator set1.
combine_with y x_i set1 = S.fold (\y_i set2 -> (x_i `S.union` y_i) `S.insert` set2) y set1

-- | Given a process p, find set of set of positions describing the conjunctive
-- normal form of the positions that    we need to go to.
-- For example: {{p1},{p2,p3}} means we need to go to p1 AND to either p2 or p3.
defPi :: (Show ann, MonadCatch m, Typeable ann) => (AnProcess ann) -> m (S.Set (S.Set ProcessPosition))
defPi  p -- corresponds to f within generate progressfunction.ml
    | (ProcessNull _) <- p = return $ ss []
    | (ProcessAction Rep _ _ ) <-p = return $ ss []
    | (ProcessAction (ChIn _ _) _ _) <-p = return $ ss []
    | (ProcessComb comb _ pl pr) <- p 
    , isExclusive comb = do
                ll <- f pl
                lr <- f pr
                return $ combine ([1] <..> ll) ([2] <..>  lr)  
    | (ProcessComb NDC _ pl pr) <- p
    , Just psl <- blocking pl, Just psr <- blocking pr = return $ ss [] 
    | (ProcessComb NDC _ pl pr) <- p
    , Just psl <- blocking pl, Nothing <- blocking pr = do
              lr <- f pr
              foldM combineWithRecursive 
                        ([2] <..>  lr) -- accumulator start with rhs positions
                        ([1] <.>  psl) -- fold over lhs positions
    | (ProcessComb NDC _ pl pr) <- p
    , Nothing <- blocking pl, Just psr <- blocking pr = do
              ll <- f pl
	      foldM combineWithRecursive ([1] <..>  ll) ([2] <.>  psr)
    | (ProcessComb NDC _ pl pr) <- p
    , Nothing <- blocking pl, Nothing <- blocking pr =  do
                ll <- f pl
                lr <- f pr
                return $ combine ([1]  <..>  ll) ([2] <..>  lr)
    | (ProcessComb Parallel  _ pl pr) <- p =  do
                ll <- f pl
                lr <- f pr
                return $ S.union ([1] <..>  ll) ([2] <..>  lr) 
    | (ProcessAction _ _ p')  <- p = do l' <- f p'
                                        return $ [1] <..> l'
    where ss x = S.singleton ( S.singleton x) -- shortcut for singleton set of singleton set
          f  =  defPi  -- shortcut for recursive call
          isExclusive  (Cond _) = True
          isExclusive  (CondEq _ _) = True
          isExclusive  (Lookup _ _) = True
          isExclusive  _ = False
          combineWithRecursive  pss pos = do -- combine pss with positions from recursive call (case of nested NDCs)
                        p'   <- (processAt p pos)
                        lpos <- f p'
                        return $ combine (pos <..> lpos) pss 
