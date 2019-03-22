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
(<.>) :: Ord a => S.Set [a] -> [a] -> S.Set [a]
(<.>) set pos = S.map (\pos' -> pos' ++ pos) set 

-- | suffix list p to each element in a set of set of sets *)
(<..>) :: Ord a => S.Set (S.Set [a]) -> [a] -> S.Set (S.Set [a])
(<..>) setset pos = S.map (\set' -> set' <.> pos) setset

blocking :: (Num a, Ord a) => AnProcess ann -> Maybe (S.Set [a])
blocking (ProcessNull _) = Just (S.singleton [1])
blocking (ProcessAction Rep _ _ ) = Just (S.singleton [1])
blocking (ProcessAction (ChIn _ _) _ _) = Just (S.singleton [1])
blocking (ProcessComb NDC _ pl pr) 
    | (Just sl) <- blocking pl, (Just sr) <- blocking pr = Just (sl<.>[1] `S.union` sr<.>[2])
    | otherwise = Nothing
blocking _ =  Nothing

combine_with y x_i set1 = S.fold (\y_i set2 -> (x_i `S.union` y_i) `S.insert` set2)

combine x y = S.fold (combine_with y) x S.empty

progressTo  p -- f within generate progressfunction.ml
    | (ProcessNull _) <- p = ss [1]
    | (ProcessAction Rep _ _ ) <-p = ss [1]
    | (ProcessAction (ChIn _ _) _ _) <-p = ss [1]
    -- | (ProcessComb (Cond _) _ pl pr) <- p = combine (f pl  <.> [1]) (f pr <.> [2])  
    -- | (ProcessComb (CondEq _ _) _ pl pr) <- p = combine (f pl  <.> [1]) (f pr <.> [2])  
    -- | (ProcessComb (Lookup _ _) _ pl pr) <- p = combine (f pl  <.> [1]) (f pr <.> [2])  
    -- | (ProcessComb NDC _ pl pr) <- p
    -- , Just psl <- blocking pl, Just psr <- blocking pr = ss [] 
    -- | (ProcessComb NDC _ pl pr) <- p
    -- , Just psl <- blocking pl, Nothing <- blocking pr =  
    --           S.foldr 
	      -- (\ pos pss -> combine (f (processAt p pos) <..> pos) pss )
    --           (psl <.> [1])
	      -- (f pr <..> [2]) 
    -- | (ProcessComb NDC _ pl pr) <- p
    -- , Nothing <- blocking pl, Just psr <- blocking pr = 
	      -- S.foldr
    --           (\ pos pss -> combine (f (processAt p pos) <..> pos) pss )
	      -- (psr <.> [2])
	      -- (f pl <..> [1])
    -- | (ProcessComb NDC _ pl pr) <- p
    -- , Nothing <- blocking pl, Nothing <- blocking pr = 
    --         combine (f pl <..> [1] ) (f pr <..> [2])
    -- | (ProcessComb _  _ pl pr) <- p =  S.union (f pl <..> [1]) (f pr <..> [2]) 
    | (ProcessAction _ _ p')  <- p = f p' <..> [1]
    where ss x = S.singleton ( S.singleton x)
          f  =  progressTo  -- shortcut for recursive call
