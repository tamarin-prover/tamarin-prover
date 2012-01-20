module Term.Unification.UnifyACElem where

-- This module implements elementary AC unification, i.e., for terms built from variables and
-- the function symbol *

import Term
import SolveDiophantine
import qualified Data.Vector.Unboxed as V
import Data.Vector.Unboxed ( Vector )
import qualified Data.Set as S
import Data.Set ( Set )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Maybe
import Utils
import Substitution
import Data.List

data MTerm a = MAtom a
             | MMult (MTerm a) (MTerm a) -- ^ multiplication in the multiplicative group of exponents G
 deriving (Eq, Show,Ord)

type MSubst = [(Int,MTerm Int)]

-- | @vrangeM subst@ returns all variables in the range of @subst@
vrangeM :: MSubst -> [Int]
vrangeM subst = snub [ v | (_,t) <- subst, v <- varsM t ]

-- | @domM subst@ returns all variables in the domain of @subst@
domM :: MSubst -> [Int]
domM subst = map fst subst

-- | @mapAtomM f t@ applies f to all variables in @t@
mapAtomM :: (a -> b) -> MTerm a -> MTerm b
mapAtomM f (MMult a b) = MMult (mapAtomM f a) (mapAtomM f b)
mapAtomM f (MAtom v) = MAtom (f v)

-- | @mapAtomMS f subst@ applies f to all variables in @subst@
mapAtomMS :: (Int -> Int) -> MSubst -> MSubst
mapAtomMS f msubst = [ (f i,mapAtomM f t) | (i,t) <- msubst ]


-- | @isVarM t@ returns @True@ if @t@ is a variables
isVarM :: MTerm a -> Bool
isVarM (MAtom _) = True
isVarM _         = False

-- | @mterm2term t@ convert @t@ from mterm to term
mterm2term :: MTerm Int -> Term Atom
mterm2term t = go t
 where
  go (MAtom x)   = Atom (Var x)
  go (MMult a b) = Mult (go a) (go b)

-- | @mvars t@ returns a sorted and duplicate-free of variables in @t@
varsM :: MTerm Int -> [Int]
varsM (MAtom a) = [a]
varsM (MMult a b) = snub (varsM a ++ varsM b)

-- | @mvarsEqual eq@ returns a sorted and duplicate-free of variables in @eq@
varsEqualM :: Equal (MTerm Int) -> [Int]
varsEqualM (Equal a b) = snub (varsM a ++ varsM b)

-- | @flatten t@ flattens the binary operator MMult to a list of arguments
flatten :: MTerm Int -> [Int]
flatten (MAtom a) = [a]
flatten (MMult a b) = flatten a++flatten b

-- | @term2Map t@ converts the term t to map that map v to |t|_v
term2Map :: MTerm Int -> Map Int Int
term2Map t = M.fromList . map (\x -> (head x, length x)) . group . sort . flatten $ t


-- | @term2Map m@ converts the map @m@ that maps v to |t|_v to the corresponding term
map2Term :: Map Int Int -> Maybe (MTerm Int)
map2Term m = go $ filter (\(_,c) -> c /= 0) $ M.toList m
 where go [] = Nothing
       go ((v0,c0):xs) = Just $ foldl (\t (v,c) -> MMult t (toPow v c)) (toPow v0 c0) xs
       toPow _ 0 = error "invalid argument"
       toPow v 1 = MAtom v
       toPow v k = MMult (MAtom v) (toPow v (k-1))

-- | @unifiy eqs@ returns a complete set of unifiers modulo AC for @eqs@
unifyM :: [Equal (MTerm Int)] -> [MSubst]
unifyM eqs = map (makeDagSolved vs) $ sols2SubstsAC vs sols
 where dioEQS = map (equal2DioEQ vs) (simpEqs eqs)
       sols = minSolutions dioEQS
       vs = snub $ concatMap varsEqualM eqs

-- | @makeDagSolved subst@ transforms a substitution to DAG solved form.
--   This is required for the combination algorithm since it cannot
--   with freshly introduced variables that are not necessary.
--   So we have to replace {y/x1,y/x2} by {x/y} or {y/x}.
makeDagSolved :: [Int] -> MSubst -> MSubst
makeDagSolved origvs subst =
   case findRepl subst of
     Just (i,v) ->
       makeDagSolved origvs [ (k,mapAtomM (\j -> if j==v then i else j) t) | (k,t) <- subst \\ [(i,MAtom v)]]
     Nothing -> subst
  where findRepl [] = Nothing
        findRepl ((i,MAtom j):eqs)
          | j `notElem` origvs = Just (i,j)
          | otherwise = findRepl eqs
        findRepl (_:eqs) = findRepl eqs

--  where varIdents = undefined 


-- | simplify equations using rule E-Rep and E-Cancel
simpEqs :: [Equal (MTerm Int)] -> [Equal (MTerm Int)]
simpEqs eqs = eqs

-- | @equal2DioEQS vars eq@ returns the diophantine equation corresponding
--   to @eq@ where the exponent at index 0 corresponds to the exponent of
--   the first variable in @vars@ 
equal2DioEQ :: [Int] -> Equal (MTerm Int) -> Vector Int
equal2DioEQ vs (Equal a b) = V.fromList $ map getEntry vs
 where -- |a|_v - |b|_v
       getEntry v = M.findWithDefault 0 v (term2Map a) -
                    M.findWithDefault 0 v (term2Map b)

-- | @sols2SubstAC vs sols@ converts a basis of the solutions modulo ACI
--   to a substitution. The result is the mgu modulo ACI for the original
--   AC unification problem if there is a unifier that does not contain
--   a 1 in its range.
sols2SubstAC :: [Int] -> Set (Vector Int) -> Maybe (MSubst)
sols2SubstAC vs sols = msubst
 where -- the matrix corresponding to the mgu
       -- the value in the ith row is s(vars!!i)
       substMatrix = transpose $ map V.toList (S.toList sols)
       newVars = [1..] \\ vs
       row2Term row = map2Term $ M.fromList $ zip newVars row
       msubst = mapM (\(v,row) -> case row2Term row of { Just t -> Just (v,t); Nothing -> Nothing})
                  $ zip vs substMatrix

-- | @sols2SubstsAC vs sols@ converts a basis of the solutions modulo ACI
--   to a list of substitutions. This list contains a complete set of AC-unifiers
--   for the original AC unification problem. The function uses the ACI unifier
--   combined with all admitted erasing substitutions
sols2SubstsAC :: [Int] -> Set (Vector Int) -> [MSubst]
sols2SubstsAC vs sols0 = catMaybes $ map (\dr -> let sols' = S.fromList $ dropByIndex dr (zip [0..] sols) in
                                                 sols2SubstAC vs sols') delrows
 where sols = S.toList sols0
       rows = length sols
       delrows = subLists (rows - 1) [0 .. (rows - 1)]

dropByIndex :: [Int] -> [(Int,b)] -> [b]
dropByIndex [] [] = []
dropByIndex [] xs = map snd xs
dropByIndex (i:is) ((j,x):xs) | j == i = dropByIndex is xs
                              | otherwise = x : dropByIndex (i:is) xs
dropByIndex (_:_) [] = error "dropByIndex: impossible"

-- | @occGraphM subst@ returns the edges of the occurence graph for @subst@
occGraphM :: MSubst -> Set (Int,Int)
occGraphM = occGraphBy varsM

-- *****************************************************************************
-- Tests
-- *****************************************************************************

t1:: Bool
t1 = (term2Map (MMult (MMult (MAtom 1) (MAtom 2)) (MMult (MAtom 3) (MAtom 1))))
     == M.fromList [(1,2),(2,1),(3,1)]

teq1 :: Equal (MTerm Int)
teq1 = Equal (MAtom 1 `MMult` MAtom 2 `MMult` MAtom 1) (MAtom 3 `MMult` MAtom 2)
t2 :: Bool
t2 = (equal2DioEQ (varsEqualM teq1) teq1) == V.fromList [2,0,-1]

teq2, teq3 :: Equal (MTerm Int)
teq2 = Equal (MAtom 1 `MMult` MAtom 2) (MAtom (3::Int))
teq3 = Equal (MAtom 1 `MMult` MAtom 2) (MAtom (3::Int) `MMult` MAtom 4)

t3 :: Bool
t3 = 7 == (length $ unifyM [teq3])