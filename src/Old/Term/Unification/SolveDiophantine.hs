module Term.Unification.SolveDiophantine where

-- The implementation is based on:
--   Contejean and Devie,
--   An Efficient Incremental Algorithm for Solving Systems of Linear Diophantine Equations
--   Information & Computation, 1994

import qualified Data.Vector.Unboxed as V
import Data.Vector.Unboxed ( (!), Vector, (//) )
import qualified Data.Set as S
import Data.Set ( Set )

-- | return the standard basis vector e_i of dimension @n@
ev :: Int -> Int -> Vector Int
ev n i = V.generate n (\k -> if k == i then 1 else 0)

-- | @basis n@ returns the standard basis for the n dimensional vector space
basis :: Int -> [Vector Int]
basis n = [ev n i | i <- [0..(n-1)]]

-- | @skp a b@ computes the scalar product of @a@ and @b@
skp :: Vector Int -> Vector Int -> Int
skp a b = V.sum $ V.zipWith (*) a b

-- | @mmult a b@ returns the result of multiplying the matrix @a@ with the column vector @b@
mmult :: [Vector Int] -> Vector Int -> Vector Int
mmult a b = V.fromList (map (\rowa -> skp rowa b) a)

-- | @isLeq a b@ returns @True@ forall i. a_i <= b_i
isLeq :: Vector Int -> Vector Int -> Bool
isLeq a b = V.foldl (&&) True (V.zipWith (\x y -> x <= y) a b)

-- | @vinc v i@ increases the vector @v@ by one at position @i@
vinc :: Vector Int -> Int -> Vector Int
vinc v i = v // [(i,v!i+1)]

-- | @minsolutions a@ returns the set of minimal solutions x to @a * x = 0@
--   This function implements the unoptimized algorithm from p. 149.
minSolutions :: [Vector Int] -> Set (Vector Int)
minSolutions [] = S.empty
minSolutions a@(r:_) = loop (S.fromList $ basis cols) S.empty
 where
  cols = V.length r
  -- | @loop cands sols@ returns all minimal solutions @x@ for @a(x) = 0@ that are either already in
  --   sols or can be reached from @cands@ by adding vectors e_i
  loop cands sols | S.null cands = sols
                  | otherwise = loop cands' sols'
   where
    (solved,nsolved) = S.partition (\v -> all (\rowa -> (skp rowa v) == 0) a) cands
    sols'   = S.union sols solved
    fcands  = S.filter (\v -> not $ any (\sv -> sv `isLeq` v) (S.toList sols')) nsolved
    cands'  = S.fromList [vinc x i | x <- S.toList fcands,
                                     i <- [0..(cols-1)],
                                     skp (a `mmult` x) (a `mmult` ev cols i) < 0]
                                     -- Contejean Devie criterion

-- *****************************************************************************
-- Tests
-- *****************************************************************************

-- | This is the example from the paper
t1 :: Bool
t1 = (minSolutions [V.fromList [-1, 1,2,-3], V.fromList [-1,3,-2,-1]])
    == (S.fromList [V.fromList [0,1,1,1], V.fromList [4,2,1,0]])