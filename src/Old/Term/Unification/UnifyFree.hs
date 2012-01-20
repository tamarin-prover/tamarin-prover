module Term.Unification.UnifyFree where

import Term
import Utils
import Data.Set ( Set )
import Substitution

-- | A term in T(Sigma_Free,a).
data FTerm a = FAtom a                   -- ^ atomic terms (constants, variables, ..)
             | FUnit                     -- ^ the unit in G
             | FOp1 Int (FTerm a)            -- ^ a countable number of free unary functions
                                             --   we use 0 for Inv
             | FOp2 Int (FTerm a) (FTerm a)  -- ^ a countable number of free binary functions
                                             --   we use 0 for Exp
  deriving (Eq, Ord, Show)

type FSubst = [(Int,FTerm Atom)]

-- | @vrangeF subst@ returns all variables in the range of @subst@
vrangeF :: FSubst -> [Int]
vrangeF subst = snub [ v | (_,t) <- subst, v <- varsF t ]

-- | @domF subst@ returns all variables in the domain of @subst@
domF :: FSubst -> [Int]
domF subst = map fst subst

-- | @mapVarF f t@ applies f to all variables in @t@
mapVarF :: (Int -> Int) -> FTerm Atom -> FTerm Atom
mapVarF f (FAtom (Var i))   = FAtom (Var (f i))
mapVarF _ (FAtom (Const c)) = FAtom (Const c)
mapVarF _ FUnit             = FUnit
mapVarF f (FOp1 i a)        = FOp1 i (mapVarF f a)
mapVarF f (FOp2 i a b)      = FOp2 i (mapVarF f a) (mapVarF f b)

-- | @mapVarFS f subst@ applies f to all variables in @subst@
mapVarFS :: (Int -> Int) -> FSubst -> FSubst
mapVarFS f fsubst = [ (f i,mapVarF f t) | (i,t) <- fsubst ]

-- | @isVarF t@ return @True@ if @t@ is a variable
isVarF :: FTerm Atom -> Bool
isVarF (FAtom (Var _)) = True
isVarF _ = False

-- | @mterm2term t@ convert @t@ from mterm to term
fterm2term :: FTerm a -> Term a
fterm2term t = go t
 where
  go (FAtom x)    = Atom x
  go FUnit        = Unit
  go (FOp1 0 a)   = Inv (go a)
  go (FOp1 i a)   = Op1 (i-1) (go a)
  go (FOp2 0 a b) = Exp (go a) (go b)
  go (FOp2 i a b) = Op2 (i-1) (go a) (go b)

-- | @varsF t@ return an ordered, duplicate-free list of the variables that occur in @t@
varsF :: FTerm Atom -> [Int]
varsF t = snub $ go t
 where
  go (FAtom (Var i))   = [i]
  go (FAtom (Const _)) = []
  go FUnit             = []
  go (FOp1 _ a)        = go a
  go (FOp2 _ a b)      = go a ++ go b

-- | @applyS2FTerm t subst@ applies the substitution @subst@ to @t@
applyS2FTerm :: FTerm Atom  -> FSubst -> FTerm Atom
applyS2FTerm t0 subst = go t0
 where
  go t@(FAtom (Var i))   =
    case lookup i subst of
      Just t' -> t'
      Nothing -> t
  go t@(FAtom (Const _)) = t
  go t@FUnit             = t
  go (FOp1 i a)        = FOp1 i (go a)
  go (FOp2 i a b)      = FOp2 i (go a) (go b)

-- | @occGraphF subst@ returns the edges of the occurence graph for @subst@
occGraphF :: FSubst -> Set (Int,Int)
occGraphF = occGraphBy varsF

-- | @unify eqs@ tries to solve the unification problem eqs and returns
--   @Nothing@ if there is no solution and @Just subst@ where @subst@ 
--   is the mgu otherwise.
unifyF :: [Equal (FTerm Atom)] -> Maybe FSubst
unifyF eqs0 = solve eqs0 []
 where
  solve [] sol = return $ sol
  solve ((Equal (FAtom (Var v))   t)                :eqs) sol
    | t == FAtom (Var v) = solve eqs sol
    | otherwise = elim v t eqs sol
  solve ((Equal t                 (FAtom (Var v)))  :eqs) sol = elim v t eqs sol
  solve ((Equal FUnit             FUnit)            :eqs) sol = solve eqs sol
  solve ((Equal (FAtom (Const i)) (FAtom (Const j))):eqs) sol
    | i == j = solve eqs sol
    | otherwise = fail "no unifier"
  solve ((Equal (FOp1 i s)        (FOp1 k t))       :eqs) sol
    | i == k = solve ((Equal s t):eqs) sol
    | otherwise = fail "no unifier"
  solve ((Equal (FOp2 i u1 u2)    (FOp2 k v1 v2))   :eqs) sol
    | i == k = solve ((Equal u1 v1):(Equal u2 v2):eqs) sol
    | otherwise = fail "no unifier"
  solve _                         _ = fail "no unifier"

  elim v t eqs sol
    | v `elem` varsF t = fail "no unifier: occurs check"
    | otherwise = solve eqs' sol'
   where subst x = x `applyS2FTerm` [(v,t)]
         eqs' = [ Equal (subst a) (subst b) | (Equal a b) <- eqs]
         sol' = (v,t):[(vv,subst tt) | (vv,tt) <- sol]

-- *****************************************************************************
-- Tests
-- *****************************************************************************

t1 :: Bool
t1 = (unifyF [Equal (FOp2 1 (FAtom (Var 2)) FUnit) (FOp2 1 (FOp1 1 (FAtom (Const 2))) (FAtom (Var 3)))])
     == (Just $ [(3,FUnit),(2,FOp1 1 (FAtom (Const 2)))])