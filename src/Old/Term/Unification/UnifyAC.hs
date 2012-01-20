module Term.Unification.UnifyAC where

import UnifyACElem
import Term
import UnifyFree
import Utils

import qualified Data.Map as M
import Data.Map ( Map )
import qualified Data.Set as S
import Data.Set ( Set )
import Data.Either
import Data.Maybe
import Data.Ord
import Data.List
import Control.Monad.State
import Control.Applicative hiding ( Const )
import Control.Arrow
import Substitution
import Debug.Trace

-- PurifyMonad type constructor
type PM b = StateT (Map VTerm Int,Int) Maybe b

-- | @purify eqs@ returns @Nothing@ if the topmost function symbols in an
--   equation belong to different theories and @Just@ two lists with the
--   pure equations in the AC-theory and the free theory.
-- 
--   Applies VA and Clash and keeps the unification problems smaller by
--   abstracting away the same term always with the same variable. It is
--   more complicated than the rule based version, wo we have to see if
--   it's worth it.
purify :: [Int] -> [Equal VTerm] -> Maybe ([Equal (MTerm Int)],[Equal (FTerm Atom)])
purify vs eqs = case evalStateT (concat <$> mapM purifyEqual eqs) (M.empty,maximum (0:vs) + 1) of
               Just res -> Just (lefts res, rights res)
               Nothing -> Nothing
 where
  purifyEqual :: (Equal VTerm) -> PM [Either (Equal (MTerm Int)) (Equal (FTerm Atom))]
  -- first handle the cases where either the RHS or LHS is a variable
  purifyEqual (Equal a b@(Atom (Var _))) = purifyEqual (Equal b a)
  purifyEqual (Equal (Atom (Var i)) b) = do
    (pb,eqsb) <- purifyTerm b
    case pb of
      Left  t -> return $ (Left  (Equal t (MAtom i))):eqsb
      Right t -> return $ (Right (Equal t (FAtom (Var i)))):eqsb
  purifyEqual (Equal a b) = do
    (pa,eqsa) <- purifyTerm a
    (pb,eqsb) <- purifyTerm b
    case (pa,pb) of
      (Left s, Left t)   -> return $ (Left (Equal s t)):(eqsa++eqsb)
      (Right s, Right t) -> return $ (Right (Equal s t)):(eqsa++eqsb)
      _ -> fail "no unifier: toplevel function symbol clash"

  purifyTerm :: VTerm -> PM (Either (MTerm Int) (FTerm Atom), [Either (Equal (MTerm Int)) (Equal (FTerm Atom))])
  purifyTerm (Atom (Const i)) = return $ (Right (FAtom (Const i)),[])
  purifyTerm (Atom (Var i))   = return $ (Right (FAtom (Var i)),[])
    -- we put variables in the free equations by default,
    -- so if we have x1 = x2 in the original problem, this is a free equation
    -- the free unification algorithm scales better with the number of variables
  purifyTerm (Unit)           = return $ (Right FUnit, [])
  purifyTerm t@(Inv _)     = (Right *** id) <$> purifyTermF t
  purifyTerm t@(Op1 _ _)   = (Right *** id) <$> purifyTermF t
  purifyTerm t@(Op2 _ _ _) = (Right *** id) <$> purifyTermF t
  purifyTerm t@(Exp _ _)   = (Right *** id) <$> purifyTermF t
  purifyTerm t@(Mult _ _)  = (Left  *** id)  <$> purifyTermM t

  purifyTermF :: VTerm -> PM ((FTerm Atom), [Either (Equal (MTerm Int)) (Equal (FTerm Atom))])
  purifyTermF (Atom (Const i)) = return $ (FAtom (Const i),[])
  purifyTermF (Atom (Var i))   = return $ (FAtom (Var i),[])
  purifyTermF (Unit)           = return $ (FUnit,[])
  purifyTermF (Op1 i a)   =  (FOp1 (i+1) *** id) <$> purifyTermF a
  purifyTermF (Inv a)     =  (FOp1 0     *** id) <$> purifyTermF a
  purifyTermF (Op2 i a b) = ((\(pa,eqsa) (pb,eqsb) -> (FOp2 (i+1) pa pb, eqsa ++ eqsb)) <$>
                              purifyTermF a) `ap` purifyTermF b
  purifyTermF (Exp a b)   = ((\(pa,eqsa) (pb,eqsb) -> (FOp2 0 pa pb, eqsa ++ eqsb)) <$>
                              purifyTermF a) `ap` purifyTermF b
    -- no  <*> because there is no Applicative instance for StateT
    -- (compare http://hackage.haskell.org/trac/ghc/ticket/2316)
  purifyTermF t@(Mult _ _)  = do
    (m,i) <- get
    case M.lookup t m of
      Just k -> -- this term has already been abstracted by variable k
        return $ (FAtom (Var k), [])
      Nothing -> do
            put (M.insert t i m,i+1)
            (pt,eqst) <- purifyTermM t
            return $ (FAtom (Var i), Left (Equal (MAtom i) pt):eqst)

  purifyTermM :: VTerm -> PM ((MTerm Int), [Either (Equal (MTerm Int)) (Equal (FTerm Atom))])
  purifyTermM (Atom (Var i)) = return $ (MAtom i,[])
  purifyTermM (Mult a b)   = ((\(pa,eqsa) (pb,eqsb) -> (MMult pa pb, eqsa ++ eqsb)) <$>
                               purifyTermM a) `ap` purifyTermM b
  purifyTermM t = do
    (m,i) <- get
    case M.lookup t m of
      Just k -> -- this term has already been abstracted by variable k
        return $ (MAtom k, [])
      Nothing -> do
            put (M.insert t i m,i+1)
            (pt,eqst) <- purifyTermF t
            return $ (MAtom i, Right (Equal (FAtom (Var i)) pt):eqst)

-- | @unifyPure vs meqs feqs@ takes the set of variables in the
--   original problem (before purification) and a list of equations
--   in M
unifyPure :: [Int] -> [Equal (MTerm Int)] -> [Equal (FTerm Atom)] -> [Subst]
unifyPure origvs meqs0 feqs0 = go meqs0 feqs0 []
 where
  go meqs feqs veqs = do
    (msubst,fsubst,vsubst) <- resolve origvs  meqs feqs veqs
    (msubst',fsubst',vsubst') <- absRemove origvs msubst fsubst vsubst
    let edges = occGraphAll msubst' fsubst' vsubst'
        morder = topoSort edges
    if (isJust morder) && (isNothing (isDagSolved origvs msubst' fsubst' vsubst'))
      then
        let subst0 = ([(i,mterm2term t) | (i,t) <- msubst']++
                     [(i,fterm2term t) | (i,t) <- fsubst']++
                     [(i,Atom (Var v)) | (i,v) <- vsubst'])
            SC subst1 = sortOccS (SC subst0)
            subst2 = foldl (\s eq -> composeS (SC [eq]) s) emptySubst subst1
            subst3 = restrictS origvs subst2
            subst4 = SC $
                       sortBy (comparing fst) $
                          getSubst subst3 ++
                          (map (\x -> (x,Atom (Var x))) $
                           filter (\v -> v `notElem` domS subst3) origvs)
            subst5 = renameSubstAwayFrom subst4 origvs
        in 
        return $ subst5
      else
--        trace (show (isDagSolved origvs msubst' fsubst' vsubst')) $
        go [(Equal (MAtom i) t) | (i,t) <- msubst']
           [(Equal (FAtom (Var i)) t) | (i,t) <- fsubst']
           vsubst'

-- | @absRemove origvs  meqs feqs veqs@ transform the system by applying the
--   Var-Rep and Remove rules until a fixpoint is reached
absRemove :: [Int] -> MSubst -> FSubst -> VSubst -> [(MSubst,FSubst,VSubst)]
absRemove origvs msubst0 fsubst0 vsubst0 =
  let (msubst1,fsubst1,vsubst1) = simpVarRep origvs msubst0 fsubst0 vsubst0
      edges = occGraphAll msubst1 fsubst1 vsubst1
  in
  if isCyclic edges
  then fail "occurs check failed"
  else
    let (msubst2,fsubst2,vsubst2) = simpRemove origvs msubst1 fsubst1 vsubst1 in
    if (msubst0==msubst2 && fsubst0==fsubst2 && vsubst0==vsubst2)
    then
      return $
--        trace ("absRemove: "++show msubst0++show fsubst0++ show vsubst0) $
          (msubst0,fsubst0,vsubst0) -- fixpoint
    else
--      trace ("absRemove loop: "++show msubst2++show fsubst2++ show vsubst2) $
      absRemove origvs msubst2 fsubst2 vsubst2

-- Apply Var-Rep rule
simpVarRep :: [Int] -> MSubst -> FSubst -> VSubst -> (MSubst,FSubst,VSubst)
simpVarRep origvs msubst fsubst vsubst =
  case findVarRep vsubst of
    Just (repl,eqold,eqsnew) ->
        (snub $ mapAtomMS repl msubst,
         snub $ mapVarFS repl fsubst,
         snub $ (mapVarVS repl (vsubst \\ [eqold]))++eqsnew)
      -- always keep the original variable! if neither is original or both are original
      -- it does not matter which we keep (for correctness).
    Nothing -> (msubst,fsubst,vsubst)
 where
  replace i j x = if x == i then j else x
  findVarRep [] = Nothing
  -- We have to make sure that we find every place where Var-Rep is applicable, but do not loop
  findVarRep (eqold@(i,j):eqs)
    -- if both are orig, then we keep the equation and replace only if both occur in the other equations,
    -- otherwise we could get into a loop where we replace i |-> j and then j |-> i
    | (j `elem` origvs && i `elem` origvs &&
       (i `elem` varsAll msubst fsubst (vsubst \\ [eqold])) &&
       (j `elem` varsAll msubst fsubst (vsubst \\ [eqold])))
      = Just (replace i j, eqold, [(i,j)])
    -- If only one is orig, we replace the fresh var with the original one.
    -- There is no way for this to loop since we never replace an orig variable with a fresh one.
    -- But we drop the equation anyways instead of waiting for simpRemove.
    | ((i `elem` varsAll msubst fsubst (vsubst \\ [eqold])) && j `elem` origvs && i `notElem` origvs)
      = Just (replace i j, eqold, [])
    -- see above
    | ((j `elem` varsAll msubst fsubst (vsubst \\ [eqold])) && i `elem` origvs && j `notElem` origvs)
      = Just (replace j i, eqold, [])
    -- If neither is orig, we cannot loop since for one of the vars, we remove all occurences.
    -- we drop the equation anyways instead of waiting for simpRemove.
    | ((j `elem` varsAll msubst fsubst (vsubst \\ [eqold])) &&
       (i `elem` varsAll msubst fsubst (vsubst \\ [eqold])))
      = Just (replace i j, eqold, [])
    -- see above
    | ((j `elem` varsAll msubst fsubst (vsubst \\ [eqold])) &&
       (i `elem` varsAll msubst fsubst (vsubst \\ [eqold])))
      = Just (replace i j, eqold, [])
    | otherwise = findVarRep eqs
      -- both are not orig and one of them does not occur somewhere else


-- Apply Remove rule eagerly. Remove all equations where the
-- RHS (or LHS for v1=v2) is not reachable from the original
-- variables in the occurence graph without the equation
simpRemove :: [Int] -> MSubst -> FSubst -> VSubst -> (MSubst,FSubst,VSubst)
simpRemove origvs msubst fsubst vsubst = (msubst',fsubst',vsubst')
 where msubst' = filter f msubst
        where f (i,t) =
                i `elem` (origvs ++ varsAll (msubst \\ [(i,t)]) fsubst vsubst)
       fsubst' = filter f fsubst
        where f (i,t) =
                i `elem` (origvs ++ varsAll msubst (fsubst \\ [(i,t)]) vsubst)
       vsubst' = filter f vsubst
        where f (x,y) =
                (x `elem` (origvs ++ varsAll msubst fsubst (vsubst \\ [(x,y)])) &&
                 y `elem` (origvs ++ varsAll msubst fsubst (vsubst \\ [(x,y)])))

-- | @resolve meqs feqs veqs@ transform the system by applying the
--   E-Resolve rule, i.e., apply the unification algorithm to the
--   pure subproblems, combine the solutions
resolve :: [Int] -> [Equal (MTerm Int)] -> [Equal (FTerm Atom)] -> VSubst -> [(MSubst,FSubst,VSubst)]
resolve origvs meqs feqs veqs = do
  msubst0 <- unifyM meqs
  fsubst0 <- maybeToList $ unifyF feqs
--  when (isJust $ isDagSolved origvs msubst0 [] []) $
--    error (show (isDagSolved origvs msubst0 [] [],msubst0))
  let -- TODO: Is renaming fsubst0 away from vrange(veqs) required?
      -- I don't think so since free unification does not introduce fresh variables,
      -- so there can be no clashes.
      msubst1 = renameSubstAwayFromMFV msubst0 origvs fsubst0 veqs
      msubst = snub $ filter (not.isVarM.snd) msubst1
      fsubst = snub $ filter (not.isVarF.snd) fsubst0
      vsubst = snub $ veqs ++ [(i,v) | (i,MAtom v) <- msubst1] ++ [(i,v) | (i,FAtom (Var v)) <- fsubst0]
      edges = occGraphAll msubst fsubst vsubst
  guard $ checkOccur edges
  guard $ null (domM msubst `intersect` domF fsubst) -- top function symbols clash
  return (msubst,fsubst,vsubst)


-- | @isDagSolved origvs msubst fsubst vsubst@ returns @True@ if the given
--   solution is in DAG solved form
isDagSolved :: [Int] -> MSubst -> FSubst -> VSubst -> Maybe String
isDagSolved origvs msubst fsubst vsubst =
  if noDuplicates dom
  then
    if varsIdentOK
    then
      if varsRequired
      then Nothing
      else Just "varsRequired"
    else Just "varsIdentOK"
  else Just "noDuplicates"
 where
  -- domAll uses snub - so we have to use the map fst version here
  dom = map fst msubst ++ map fst fsubst ++ map fst vsubst
  edges = occGraphAll msubst fsubst vsubst
  varsIdentOK =
    all (\(i,j) ->
           i `elem` origvs && j `elem` origvs &&
           -- Only have equalities between original variables
           ((i `notElem` (varsAll msubst fsubst (vsubst \\ [(i,j)]))) ||
            (j `notElem` (varsAll msubst fsubst (vsubst \\ [(i,j)]))))) vsubst
           -- i must have been replaced with j everywhere else
           -- in the substitution. noDuplicates ensures that
           --  it appears nowhere else in the domain

  -- every variable must be required, i.e., reachable in the occurence graph
  -- from the original variables
  varsRequired = S.null (S.fromList (varsAll msubst fsubst vsubst)
                         `S.difference` reachableFrom (S.fromList origvs) edges)

unify :: VTerm -> VTerm -> IO [Subst]
unify s t = return $ unify' s t

-- | @reachableFrom start edges@ returns all nodes that are reachable from
--   @start@ via @edges@
reachableFrom :: Set Int -> Set (Int,Int) -> Set Int
reachableFrom start edges = if isCyclic edges then error "reachable: cyclic graph" else go S.empty start
 where
  go visited new
    | S.null new = visited
    | otherwise = go (S.union visited new)
                     (S.unions [ S.map snd (S.filter ((==n).fst) edges) | n <- S.toList new])

-- | @unify s t@ returns a complete set of unifiers modulo AC for s and t
unify' :: VTerm -> VTerm -> [Subst]
unify' s t = trace (show (s,t)) $
  case purify vs (simpPair eqs) of
    Nothing -> []
    Just (meqs,feqs) -> unifyPure vs meqs feqs
  where eqs = [Equal s t]
        vs = concatMap varsEqual eqs

simpPair :: [Equal VTerm] -> [Equal VTerm]
simpPair ((Equal (Op2 0 u1 u2) (Op2 0 v1 v2)):eqs) = simpPair ((Equal u1 v1):(Equal u2 v2):eqs)
simpPair (eq:eqs) = eq:simpPair eqs
simpPair [] = []


-- | @occGraph meqs feqs@ returns the occurence graph for the given equations.
--   This is used for the combined occurs check.
occGraphAll :: MSubst -> FSubst -> VSubst -> Set (Int,Int)
occGraphAll msubst fsubst vsubst =
  occGraphM msubst `S.union` occGraphF fsubst `S.union` occGraphV  vsubst

-- | @checkOccur edges@ returns @True@ if there is a combined occurence cycle
checkOccur :: Set (Int,Int) -> Bool
checkOccur edges = not $ isCyclic edges


-- | @renameSubstAwayFromMFV msubst fsubst vsubst@ renames the variables in the
--   range of msubst away from variables in the range of the other substitutions
renameSubstAwayFromMFV :: MSubst -> [Int] -> FSubst -> VSubst -> MSubst
renameSubstAwayFromMFV msubst origvs fsubst vsubst = [(i,f t) | (i,t) <- msubst]
 where replace = mappingId (vrangeM msubst \\ domM msubst)
                           (snub $ domF fsubst++vrangeF fsubst++domM msubst++domV vsubst++origvs)
       f = mapAtomM replace

type VSubst = [(Int,Int)]

-- | @domV subst@ returns all variables in the domain of @subst@
domV :: VSubst -> [Int]
domV = map fst

-- | @vrangeV subst@ returns all variables in the range of @subst@
vrangeV :: VSubst -> [Int]
vrangeV = map snd

-- | @mapVarVS f subst@ applies f to all variables in @subst@
mapVarVS :: (Int -> Int) -> VSubst -> VSubst
mapVarVS f vsubst = [ (f i,f j) | (i,j) <- vsubst ]

-- TODO: replace all this by type classes
-- | @occGraphV subst@ returns the edges of the occurence graph
occGraphV :: VSubst -> Set (Int,Int)
occGraphV = S.fromList

-- | @domAll msubst fsubst vsubst@  returns all variables in the domain of the given substitutions
domAll :: MSubst -> FSubst -> VSubst -> [Int]
domAll msubst fsubst vsubst = snub $ domM msubst ++ domF fsubst ++ domV vsubst

-- | @vrangeAll msubst fsubst vsubst@  returns all variables in the range of the given substitutions
vrangeAll :: MSubst -> FSubst -> VSubst -> [Int]
vrangeAll msubst fsubst vsubst = snub $ vrangeM  msubst ++ vrangeF fsubst ++ vrangeV vsubst

-- | @varsAll msubst fsubst vsubst@  returns all variables in the domain and range of the given substitutions
varsAll :: MSubst -> FSubst -> VSubst -> [Int]
varsAll msubst fsubst vsubst = snub $ domAll msubst fsubst vsubst ++ vrangeAll msubst fsubst vsubst


-- *****************************************************************************
-- Tests
-- *****************************************************************************

eqs1 :: [Equal (VTerm)]
eqs1 = [Equal (x3 # (inv (x4 # x5))) x5]

t4 :: Maybe ([Equal (MTerm Int)], [Equal (FTerm Atom)])
t4 = purify (concatMap varsEqual eqs1) eqs1

t5,t6,t7,t8,t9,t10,t12,t13,t14,t15,t16,t17,t18 :: Bool
t5 = (isCyclic (S.fromList [(5,2),(1,2),(2,3),(3,4)])) == False
t6 = (isCyclic (S.fromList [(5,2),(1,2),(2,3),(3,1)])) == True

t7 = (topoSort (S.fromList [(5,2),(1,2),(2,3),(2,99),(3,4)])) == Just [1,5,2,3,99,4]
t8 = (topoSort (S.fromList [(5,2),(1,2),(2,3),(2,99),(3,1)])) == Nothing

t9 = isJust (isDagSolved [1] [(1,MMult (MAtom 5) (MAtom 4))] [] [(1,3)])
  -- duplicate variables

t10 = isNothing (isDagSolved [1,2,3,4] [(1,MMult (MAtom 2) (MAtom 5))] [(2,FUnit)] [(3,4)])

t12 = isJust (isDagSolved [1,2,3] [(1,MMult (MAtom 2) (MAtom 5))] [(2,FUnit)] [(3,4)])
  -- we do not allow this var ident

t13 = isNothing (isDagSolved [1,2,3,4] [(1,MMult (MAtom 2) (MAtom 3))] [(2,FUnit)] [(3,4)])

t14 = isJust (isDagSolved [1] [(1,MMult (MAtom 3) (MAtom 3))] [(2,FUnit)] [])
  -- equation where var on LHS is not required by earlier ones

t15 = (reachableFrom (S.fromList [1]) (S.fromList [(1,2),(1,3),(4,5),(5,7)])) == S.fromList [1,2,3]

t16 = isNothing (isDagSolved [1,2,3]
                             [(1,MMult (MAtom 5) (MAtom 9)),(3,MMult (MAtom 4) (MAtom 9))]
                             [(4,FOp1 0 (FAtom (Var 2)))]  [])

t17 = (simpVarRep [1,2,3] [] [] [(1,7),(3,7)]) == ([],[],[(3,1)])
  -- we differ here from the rules in the paper. I think they assume
  -- that something like this never occurs
  -- Note that simpRemove would remove the second equation later on

t18 = (unify' (x1 # (inv (x2))) (x3 # a1)) == [SC [(1,a1 # x5),(2,x4),(3,(inv x4) # x5)],
                                               SC [(1,a1),(2,x4),(3,inv x4)]]

t19 :: Bool
t19 = isJust (isDagSolved [1,3] [] [] [(1,7),(3,7)])

t20 :: Bool
t20 = (simpVarRep [1] [] [(2,FUnit)] [(2,1)]) == ([],[(1,FUnit)],[])

t21 :: Bool
t21 = (unify' (x2 # x1) (x3 # inv x3))
      == [SC [(1,inv x4),(2,x4),(3,x4)],SC [(1,x4),(2,inv x4),(3,x4)]]

t22 :: Bool
t22 = (unify' (x2 # x1) (inv (x3 # x4) # x4))
      == [SC [(1,inv (x6 # x5)),(2,x5),(3,x6),(4,x5)],
          SC [(1,x5),(2, inv (x6 # x5)),(3,x6),(4,x5)]]

all_t :: Bool
all_t = and [t5,t6,t7,t8,t9,t10,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22]

{-

This one is pretty slow:
op2_0(op2_0(a1,~a3*a4*a5),op2_0(op2_0(a2,~a5*a6*a3),1))
op2_0(op2_0(a1,~x3*x4*x5),op2_0(op2_0(a2,~x5*x3),1))

-}