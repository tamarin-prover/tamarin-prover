-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- Functions that could/should have made it into the Prelude or one of the
-- base libraries
module Extension.Prelude where

import Data.Maybe
--import Data.List --hiding (sortOn)
import Data.List (groupBy,inits,nubBy,sortBy,tails,unfoldr)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Ord (comparing)
import Data.Function (on)
import Data.Foldable (asum)

import Control.Basics

import System.IO


-- Bool --
----------

implies :: Bool -> Bool -> Bool
implies True p  = p
implies False _ = True


-- Lists --
-----------

singleton :: a -> [a]
singleton x = [x]

-- | check whether the given list contains no duplicates
{-# INLINABLE unique #-}
unique :: Eq a => [a] -> Bool
unique [] = True
unique (x:xs) = x `notElem` xs && unique xs

-- | Sort list and remove duplicates. O(n*log n)
{-# INLINE sortednub #-}
sortednub :: Ord a => [a] -> [a]
sortednub = sortednubBy compare

-- | Sort a list according to a user-defined comparison function and remove
-- duplicates.
{-# INLINABLE sortednubBy #-}
sortednubBy :: (a -> a -> Ordering) -> [a] -> [a]
sortednubBy cmp =
    -- Adapted from GHC's Data.List module
    -- Copyright:  (c) The University of Glasgow 2001
    mergeAll . sequences
  where
    sequences (a:xs@(b:xs')) = case a `cmp` b of
      GT -> descending b [a] xs'
      EQ -> sequences xs
      LT -> ascending b (a:) xs
    sequences xs = [xs]

    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | a `cmp` b == LT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = as [a] : sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge []         bs         = bs
    merge as         []         = as
    merge as@(a:as') bs@(b:bs') = case a `cmp` b of
      GT -> b : merge as  bs'
      EQ ->     merge as bs'  -- equal elements are dropped
      LT -> a : merge as' bs

-- | //O(n*log n).// Sort list and remove duplicates with respect to a
-- projection.
{-# INLINE sortednubOn #-}
sortednubOn :: Ord b => (a -> b) -> [a] -> [a]
sortednubOn proj = sortednubBy (comparing proj)

-- | Keep only the first element of elements having the same projected value
nubOn :: Eq b => (a -> b) -> [a] -> [a]
nubOn proj = nubBy ((==) `on` proj)

-- | //O(n).// Group on a projection of the data to group
groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn proj = groupBy ((==) `on` proj)

-- | sort on a projection of the data to sort
sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn proj = sortBy (comparing proj)

-- | sort on a projection of the data to sort, memorizing the results of the
-- projection in order to avoid recomputation.
sortOnMemo :: Ord b => (a -> b) -> [a] -> [a]
sortOnMemo proj = map fst . sortOn snd . map (id &&& proj)

-- | sort and group on a projection
groupSortOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupSortOn proj = groupOn proj . sortOn proj

-- | partition the given set into equality classes with respect
-- to the representative given by the projection function
eqClasses :: Ord b => (a -> b) -> [a] -> [[a]]
eqClasses = eqClassesBy ord
  where ord x y | x == y = EQ | x < y = LT | otherwise = GT

eqClassesBy :: (b -> b -> Ordering) -> (a -> b) -> [a] -> [[a]]
eqClassesBy ord proj = groupBy eq . sortBy ord'
  where ord' x y = ord (proj x) (proj y)
        eq x y = ord' x y == EQ

-- | split a list into sublists whenever the predicate identifies an element as
-- a separator. Note that the separator is not retained and a separator at the
-- very end is ignored.
splitBy :: (a -> Bool) -> [a] -> [[a]]
splitBy p = unfoldr split
  where split [] = Nothing
        split xs = let ~(w,r) = break p xs in case r of
          []       -> Just $ (w,[])
          (_:rest) -> Just $ (w,rest)


-- | the list of all permutations of a given list
-- permutations :: [a] -> [[a]]
-- permutations [] = [[]]
-- permutations zs = aux zs []
  -- where aux [] _ = []
        -- aux (x:xs) ys = [x:p | p <- permutations (xs++ys)] ++ aux xs (x:ys)

-- | the list of all combinations of n elements of a list.
-- E.g. choose 2 [1,2,3] = [[1,2],[1,3],[2,3]]
choose :: Int -> [a] -> [[a]]
choose 0 _      = [[]]
choose _ []     = []
choose n (x:xs) = [x:xs' | xs' <- choose (n-1) xs] ++ choose n xs

-- | build the list of lists each leaving another element out.
-- (From left to right)
leaveOneOut :: [a] -> [[a]]
leaveOneOut xs =
  zipWith (++) (map init . tail . inits $ xs) (map tail . init . tails $ xs)


-- | An element masks another element if the predicate is true. This function
-- keeps only the elements not masked by a previous element in the list.
keepFirst :: (a -> a -> Bool) -> [a] -> [a]
keepFirst _    []     = []
keepFirst mask (x:xs) = x : keepFirst mask (filter (not . mask x) xs)

-- Pairs --
-----------

-- | These functions were inspired by the ML library accompanying the
--   Isabelle theorem prover (<http://isabelle.in.tum.de/>)

-- | swap the elements of a pair
swap :: (a, b) -> (b, a)
swap (x, y)      = (y, x)

-- | sort the elements of a pair
sortPair :: Ord a => (a,a) -> (a,a)
sortPair p@(x,y) | x <= y = p | otherwise = swap p


-- Either --
------------

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _         = False

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False

-- Strings --
-------------

-- | Name values of a given type
type Named a = (String, a)

-- | Extend a list with the given separators to be flushed right.
flushRightBy :: [a] -> Int -> [a] -> [a]
flushRightBy sep n str = take (max 0 (n - length str)) (cycle sep) ++ str

-- | Extend a string with spaces to be flushed right.
flushRight :: Int -> String -> String
flushRight = flushRightBy " "

-- | Extend a list with the given separators to be flushed left.
flushLeftBy :: [a] -> Int -> [a] -> [a]
flushLeftBy sep n str = str ++ take (max 0 (n - length str)) (cycle sep)

-- | Extend a string with spaces to be flushed left.
flushLeft :: Int -> String -> String
flushLeft = flushLeftBy " "


-- IO --
--------


-- | marks a string as being a warning
warning :: String -> String
warning s = "warning: "++s

-- | abbreviation to print to stderr
putErr :: String -> IO ()
putErr = hPutStr stderr

-- | abbreviation to println to stderr
putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

-- Applicative --
-----------------

-- | Inject the elements of a list as alternatives.
oneOfList :: Alternative f => [a] -> f a
oneOfList = asum . map pure

-- | Inject the elements of a set as alternatives.
oneOfSet :: Alternative f => S.Set a -> f a
oneOfSet = oneOfList . S.toList

-- | Inject the elements of a map as alternatives.
oneOfMap :: Alternative f => M.Map k v -> f (k, v)
oneOfMap = oneOfList . M.toList


-- Monads --
------------

-- | A monadic if statement
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM p pos neg = do
  b <- p
  if b then pos else neg

-- | Gather all error free computations.
errorFree :: MonadPlus m => [m a] -> m [a]
errorFree ms =
  catMaybes `liftM` sequence [(Just `liftM` m) `mplus` return Nothing | m <- ms]

-- | Gather all error free computations and ensure that at least one was error
-- free.
errorFree1 :: MonadPlus m => [m a] -> m [a]
errorFree1 ms = do
    ms' <- errorFree ms
    if null ms' then mzero else return ms'

-- Error reporting
------------------

-- | Mark a part of the code as unreachable.
unreachable :: String -> a
unreachable location =
    error $ "reached the 'unreachable' code in " ++ location

