{-# LANGUAGE DeriveDataTypeable, BangPatterns, StandaloneDeriving, TypeSynonymInstances #-}
-- |
-- Copyright   : (c) 2010, 2011 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Types and operations for handling sorted first-order logic
module Logic.FOL (
  -- * Formulas
    Connective(..)
  , Quantifier(..)
  , BVar(..)
  , Formula(..)

  , quantify
  , unquantify

  -- ** More convenient constructors
  , lfalse
  , ltrue
  , (.&&.)
  , (.||.)
  , (.==>.)
  , (.<=>.)
  , exists
  , forall
  , universalClosure
  , existentialClosure
  
  -- ** Taking them apart
  , toplevelConjs
  , toplevelDisjs
  , negative
  , positive
  , fromFree
  , freeIndices

  -- ** General Transformations
  , mapAtoms
  , foldBVar
  , foldFormula

  -- ** Logic Transformations
  , negate
  , pushquants
  , pullquants
  , simplifyFormula
  , nnf
  , dnf
  , pnf

  -- ** Pretty-Printing
  , prettyFormula

  -- ** Tests
  , tests

  ) where

import Prelude hiding (negate)

import qualified Data.DList as D
import Data.Monoid hiding (All)
import Data.Foldable (Foldable, foldMap)
import Data.Traversable
import Data.Generics

import Control.Basics
import Control.Monad.Writer hiding (All)
import Control.Monad.Reader
import Control.Monad.Disj

import Logic.Connectives

import Extension.Prelude

import Text.PrettyPrint.Highlight

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- | Logical connectives.
data Connective = And | Or | Imp | Iff
                deriving( Eq, Ord, Show, Enum, Bounded, Data, Typeable )

-- | Quantifiers.
data Quantifier = All | Ex
                deriving( Eq, Ord, Show, Enum, Bounded, Data, Typeable )


-- | Bound and free variables.
data BVar v = Bound Int  -- ^ A bound variable in De-Brujin notation.
            | Free  v    -- ^ A free variable.
            deriving( Eq, Ord, Show, Data, Typeable )

-- | First-order formulas in locally nameless representation with hints for the
-- names of quantified variables.
data Formula a s v = Ato (a (BVar v))
                   | TF !Bool
                   | Not (Formula a s v)
                   | Con !Connective (Formula a s v) (Formula a s v)
                   | Qua !Quantifier s (Formula a s v)

-- Folding
----------

-- | Fold a possibly bound variable.
{-# INLINE foldBVar #-}
foldBVar :: (Int -> a) -> (v -> a) -> BVar v -> a
foldBVar fBound fFree = go
  where
    go (Bound i) = fBound i
    go (Free v)  = fFree v

-- | Fold a formula.
{-# INLINE foldFormula #-}
foldFormula :: (a (BVar v) -> b) -> (Bool -> b) 
            -> (b -> b) -> (Connective -> b -> b -> b)
            -> (Quantifier -> s -> b -> b)
            -> Formula a s v
            -> b
foldFormula fAto fTF fNot fCon fQua = 
    go
  where
    go (Ato a)       = fAto a
    go (TF b)        = fTF b
    go (Not p)       = fNot (go p)
    go (Con c p q)   = fCon c (go p) (go q)
    go (Qua qua x p) = fQua qua x (go p)

-- | Fold a formula.
{-# INLINE foldFormulaScope #-}
foldFormulaScope :: (Int -> a (BVar v) -> b) -> (Bool -> b)
                 -> (b -> b) -> (Connective -> b -> b -> b)
                 -> (Quantifier -> s -> b -> b)
                 -> Formula a s v
                 -> b
foldFormulaScope fAto fTF fNot fCon fQua =
    go 0
  where
    go !i (Ato a)       = fAto i a
    go _  (TF b)        = fTF b
    go !i (Not p)       = fNot (go i p)
    go !i (Con c p q)   = fCon c (go i p) (go i q)
    go !i (Qua qua x p) = fQua qua x (go (succ i) p)


-- Instances
------------

instance Functor BVar where
    fmap f = foldBVar Bound (Free . f)

instance Foldable BVar where
    foldMap f = foldBVar mempty f

instance Traversable BVar where
    traverse f = foldBVar (pure . Bound) (fmap Free . f)

instance Applicative BVar where
   pure  = return
   (<*>) = ap

instance Monad BVar where
    return  = Free
    m >>= f = foldBVar Bound f m


instance Functor a => Functor (Formula a s) where
    fmap f = foldFormula (Ato . fmap (fmap f)) TF Not Con Qua

instance Foldable a => Foldable (Formula a s) where
    foldMap f = foldFormula (foldMap (foldMap f)) mempty id 
                            (const mappend) (const $ const id)

instance Traversable a => Traversable (Formula a s) where
    traverse f = foldFormula (liftA Ato . traverse (traverse f)) 
                             (pure . TF) (liftA Not)
                             (liftA2 . Con) ((liftA .) . Qua)




-- Abbreviations
----------------
 
infixl 3 .&&.
infixl 2 .||.
infixr 1 .==>.
infix  1 .<=>.

-- | Logically true.
ltrue :: Formula a s v
ltrue = TF True

-- | Logically false.
lfalse :: Formula a s v
lfalse = TF False

(.&&.), (.||.), (.==>.), (.<=>.) :: Formula a s v -> Formula a s v -> Formula a s v
(.&&.)  = Con And
(.||.)  = Con Or
(.==>.) = Con Imp
(.<=>.) = Con Iff

------------------------------------------------------------------------------
-- Dealing with bound variables
------------------------------------------------------------------------------

-- | Extract the name of free variable under the assumption the variable is
-- guaranteed to be of the form @Free a@.
fromFree :: BVar v -> v
fromFree (Free v)  = v
fromFree (Bound i) = error $ "fromFree: bound variable '" ++ show i ++ "'"

-- | The list of all free variables.
frees :: Foldable a => Formula a s v -> [v]
frees = D.toList . foldFormula (foldMap (foldBVar (const mempty) pure)) 
                               mempty id (const mappend) (const $ const id)

-- | Change the representation of atoms.
mapAtoms :: (Int -> a (BVar v) -> b (BVar w)) -> Formula a s v -> Formula b s w
mapAtoms f = foldFormulaScope (\i a -> Ato $ f i a) TF Not Con Qua

-- | The list of all free indices.
freeIndices :: Foldable a => Formula a s v -> [Int]
freeIndices =
    D.toList . foldFormulaScope
                   (\i a -> foldMap (foldBVar (extractFree i) (const mempty)) a) mempty id
                   (const mappend) (const $ const id)
  where extractFree i j | j < i     = mempty
                        | otherwise = pure $ j - i

-- | Increase the bound variables by the given amount. This has to be used when
-- moving a sub-formula inside an abstraction.
shiftFreeIndices :: Functor a => Int -> Formula a s v -> Formula a s v
shiftFreeIndices n =
    mapAtoms (\i a -> fmap (foldBVar (Bound . shift i) Free) a)
  where
     shift i j | j < i     = j
               | otherwise =  j + n

-- | Introduce a bound variable for a free variable.
quantify :: (Functor a, Eq v) => v -> Formula a s v -> Formula a s v
quantify x =
    mapAtoms (\i a -> fmap (>>= (subst i)) a)
  where
    subst i v | v == x    = Bound i
              | otherwise = Free v

-- | Introduce a free variable for the outermost bound variable.
unquantify :: (Functor a, Eq v) => v -> Formula a s v ->  Formula a s v
unquantify x = 
    mapAtoms (\i a -> fmap (subst i) a)
  where
    subst i (Bound i') | i == i' = Free x
    subst _ bv                   = bv

-- | Create a universal quantification with a sort hint for the bound variable.
forall :: (Eq v, Functor a) => s -> v -> Formula a s v -> Formula a s v
forall hint x = Qua All hint . quantify x

-- | Create a existential quantification with a sort hint for the bound variable.
exists :: (Eq v, Functor a) => s -> v -> Formula a s v -> Formula a s v
exists hint x = Qua Ex hint . quantify x

-- | Quantify all free variables after removing duplicates and sorting them.
quantifyFrees :: (Ord v, Functor a, Foldable a) 
              => (v -> Formula a s v -> Formula a s v) -- ^ Quantifier.
              -> Formula a s v -> Formula a s v
quantifyFrees qua fm = foldr qua fm (sortednub (frees fm))

-- | Universal closure.
universalClosure :: (Ord v, Functor a, Foldable a)
                 => (v -> s)             -- ^ Bound name hint from variable.
                 -> Formula a s v -> Formula a s v
universalClosure hint = quantifyFrees (\v -> forall (hint v) v)

-- | Universal closure.
existentialClosure :: (Ord v, Functor a, Foldable a)
                   => (v -> s)             -- ^ Bound name hint from variable.
                   -> Formula a s v -> Formula a s v
existentialClosure hint = quantifyFrees (\v -> exists (hint v) v)

{-

------------------------------------------------------------------------------
-- Traversing and Mapping that respect bound variables.
------------------------------------------------------------------------------

-- | General effectful traversal of a formula. Bound variables are collected in
-- the computational effect. Typically a reader monad with an appropriate
-- argument. We inline this function to allow its usages to be spezialized.
{-# INLINE traverseVarsAtoms #-}
traverseVarsAtoms :: Applicative f
                  => (v -> (w, f (Formula b w) -> f (Formula b w)))
                     -- ^ Effectful mapping of bound variables.
                  -> (a v -> f (b w))  
                     -- ^ Effectful mapping of atoms.
                  -> Formula a s v 
                  -> f (Formula b w)
traverseVarsAtoms vF aF = go
  where
    go (Ato a)       = Ato <$> aF a
    go (TF b) = pure $ TF b
    go (Not f)       = Not <$> go f
    go (Con c f1 f2) = Con c <$> go f1 <*> go f2
    go (Qua q v f)   = Qua q (fst $ vF v) <$> (snd $ vF v) (go f)

-- | General traversal of a formula without changing the representation of variables. 
-- See 'traverseVarsAtoms' for more usage examples.
{-# INLINE traverseAtoms #-}
traverseAtoms :: Applicative f
              => (v -> f (Formula b v) -> f (Formula b v))
                 -- ^ Effectful mapping of bound variables.
              -> (a v -> f (b v))  
                 -- ^ Effectful mapping of atoms.
              -> Formula a s v 
              -> f (Formula b v)
traverseAtoms vF = traverseVarsAtoms (\v -> (v, vF v))

-- | General mapping of a formula. Bound variables are collected automatically.
{-# INLINE mapVarsAtoms #-}
mapVarsAtoms :: Ord v
             => (v -> w)                     -- ^ Map for bound variables.
             -> ((v -> Bool) -> a v -> b w)  -- ^ Map for atoms with a
                                             -- predicate characterizing the bound variables.
             -> Formula a s v 
             -> Formula b w  
mapVarsAtoms vF aF f = 
    traverseVarsAtoms vF' aF' f S.empty
  where
    vF' v        = (vF v, (. S.insert v))
    aF' a bounds = aF (`S.member` bounds) a

-- | Traverse all atoms with a function that takes a predicate identifying the
-- bound variables.
{-# INLINE traverseAtomsWithBounds #-}
traverseAtomsWithBounds :: (Applicative f, Ord v)
                        => ((v -> Bool) -> a v -> f (b v))  
                           -- ^ Effectful mapping of atoms given a predicate characterizing the
                           -- bound variables.
                        -> Formula a s v 
                        -> f (Formula b v)
traverseAtomsWithBounds aF f =
    runReaderT (traverseAtoms vF' aF' f) S.empty
  where
    vF' v = withReaderT (S.insert v)
    aF' a = ReaderT $ \bounds -> aF (`S.member` bounds) a
  

-- | Gather all free variables of the formula in a monoid.
{-# INLINE foldFreeVars #-}
foldFreeVars :: (Monoid m, Ord v)
         => ((v -> Bool) -> a v -> m)  -- ^ Given a predicate classifying
                                       -- free variables, this function should
                                       -- return the free variables of an atom.
         -> Formula a s v 
         -> m
foldFreeVars freeAtoVars = 
    go S.empty
  where
    go bound (Ato a)       = freeAtoVars (`S.member` bound) a
    go _     (TF _)        = mempty
    go bound (Not f)       = go bound f
    go bound (Con _ f1 f2) = go bound f1 `mappend` go bound f2
    go bound (Qua _ v f)   = go (S.insert v bound) f



------------------------------------------------------------------------------
-- Normal forms
------------------------------------------------------------------------------

-- | Shared methods of structures that can be atoms of formulas.
class FormulaAtom a where
    -- | Occurs check
    occurs :: Ord v => v -> a v -> Bool

instance FormulaAtom a => FormulaAtom (Formula a) where
    {-# INLINE occurs #-}
    occurs v = 
        foldFormula (occurs v) (const False) id (const (||)) fQua
      where
        fQua _ v' occ | v == v'   = False
                      | otherwise = occ
   
-}
 

-- Partially based on John Harrison's book: Introduction to Logic Programming

-- | Propositional simplification.
psimplifyFormula :: Formula a s v -> Formula a s v
psimplifyFormula fm0 = case fm0 of
    Not p       -> psimplifyFormula1 $ Not (psimplifyFormula p)
    Con And p q -> psimplifyFormula1 $ psimplifyFormula p .&&.  psimplifyFormula q
    Con Or  p q -> psimplifyFormula1 $ psimplifyFormula p .||.  psimplifyFormula q
    Con Imp p q -> psimplifyFormula1 $ psimplifyFormula p .==>. psimplifyFormula q
    Con Iff p q -> psimplifyFormula1 $ psimplifyFormula p .<=>. psimplifyFormula q
    _           -> fm0
  where
    psimplifyFormula1 fm = case fm of
        Not (TF False)                 -> TF True
        Not (TF True)                  -> TF False
        Con And (TF False) _           -> TF False
        Con And _          (TF False)  -> TF False
        Con And (TF True)  q           -> q
        Con And p          (TF True)   -> p
        Con Or  (TF False) q           -> q
        Con Or  p          (TF False)  -> p
        Con Or  (TF True)  _           -> TF True
        Con Or  _          (TF True)   -> TF True
        Con Imp (TF False) _           -> TF True
        Con Imp (TF True)  q           -> q
        Con Imp _          (TF True)   -> TF True
        Con Imp p          (TF False)  -> Not p
        Con Iff (TF True)  q           -> q
        Con Iff p          (TF True)   -> p
        Con Iff (TF False) (TF False)  -> TF True
        Con Iff (TF False) q           -> Not q
        Con Iff p          (TF False)  -> Not p
        _                              -> fm

-- | First-order simplification.
simplifyFormula :: (Functor a, Foldable a) => Formula a s v -> Formula a s v
simplifyFormula fm0 = case fm0 of
    Not p       -> simplifyFormula1 $ Not (simplifyFormula p)
    Con And p q -> simplifyFormula1 $ Con And (simplifyFormula p) (simplifyFormula q)
    Con Or  p q -> simplifyFormula1 $ Con Or  (simplifyFormula p) (simplifyFormula q)
    Con Imp p q -> simplifyFormula1 $ Con Imp (simplifyFormula p) (simplifyFormula q)
    Con Iff p q -> simplifyFormula1 $ Con Iff (simplifyFormula p) (simplifyFormula q)
    Qua qua x p -> simplifyFormula1 $ Qua qua x (simplifyFormula p)
    _           -> fm0
  where
    simplifyFormula1 fm@(Qua _ _ p) | 0 `elem` freeIndices p = fm
                                    | otherwise         = shiftFreeIndices (-1) p
    simplifyFormula1 fm                                 = psimplifyFormula fm

-- | True iff there is an outermost 'Not'.
negative :: Formula a s v -> Bool
negative (Not _) = True
negative _       = False

-- | True iff there is no outermost 'Not'.
positive :: Formula a s v -> Bool
positive = not . negative

-- | Negate a formula without introducing outermost direct negations.
negate :: Formula a s v -> Formula a s v
negate (Not fm) = fm
negate fm       = Not fm

-- | Split off all top-level disjunctions.
toplevelDisjs :: Formula a s v -> Disj (Formula a s v)
toplevelDisjs (Con Or p q) = toplevelDisjs p `disjunction` toplevelDisjs q
toplevelDisjs fm           = return fm

-- | Split off all top-level conjunctions.
toplevelConjs :: Formula a s v -> Conj (Formula a s v)
toplevelConjs (Con And p q) = toplevelConjs p `mappend` toplevelConjs q
toplevelConjs fm            = pure fm

-- | Conjoin all conjunctions in a right-associative nesting.
flattenConjs :: Conj (Formula a s v) -> Formula a s v
flattenConjs conj = case getConj conj of
   [] -> ltrue
   cs -> foldr1 (.&&.) cs

-- | Conjoin all disjunctions in a right-associative nesting.
flattenDisjs :: Disj (Formula a s v) -> Formula a s v
flattenDisjs disj = case getDisj disj of
   [] -> lfalse
   cs -> foldr1 (.||.) cs

-- | Direct conversion to disjunctive normal form under the assumption that the
-- formula is already in NNF and that there are no quantifiers.
pdnf :: Formula a s v -> Disj (Conj (Formula a s v))
pdnf (Con Or  p q) =         mappend  (pdnf p) (pdnf q)
pdnf (Con And p q) = (liftA2 mappend) (pdnf p) (pdnf q)
pdnf fm            = pure (pure fm)

-- | Apply a formula transformation inside an outer level of quantifiers
-- without actually unquantifying and quantifying them again.
insideQuants :: (Formula a s v -> Formula a s v) -> Formula a s v -> Formula a s v
insideQuants f = 
    go
  where
    go (Qua qua x p) = Qua qua x $ go p
    go fm            = f fm

-- | Direct conversion to disjunctive normal form under the assumption that the
-- formula is in NNF prenex normal form.
dnf :: Formula a s v -> Formula a s v
dnf = insideQuants (flattenDisjs . fmap flattenConjs . pdnf)

-- | Negation normal form.
nnf :: Formula a s v -> Formula a s v
nnf fm = case fm of 
    Con And p q        -> nnf p       .&&. nnf q
    Con Or  p q        -> nnf p       .||. nnf q
    Con Imp p q        -> nnf (Not p) .||. nnf q
    Con Iff p q        -> (nnf p .&&. nnf q) .||. (nnf (Not p) .&&. nnf (Not q))
    Not (Not p)        -> nnf p
    Not (Con And p q ) -> nnf (Not p) .||. nnf (Not q)
    Not (Con Or  p q ) -> nnf (Not p) .&&. nnf (Not q)
    Not (Con Imp p q ) -> nnf p       .&&. nnf (Not q)
    Not (Con Iff p q ) -> (nnf p .&&. nnf (Not q)) .||. (nnf(Not p) .&&. nnf q)
    Qua qua x p        -> Qua qua     x $ nnf p
    Not (Qua All x p)  -> Qua Ex  x $ nnf (Not p)
    Not (Qua Ex  x p)  -> Qua All x $ nnf (Not p)
    _                  -> fm


-- | Pushing in quantifiers for formulas in prenex normal form. Currently we
-- exploit only the following two identities.
--
--    1. @(All x. p & q) <=> (All x. p) & (All x. q)@
--    2. @(Ex x.  p | q) <=> (Ex x.  p) | (Ex x. q )@
--
-- TODO: Check if Horbach's PhD thesis provides some more tricks.
--
pushquants :: Functor a => Formula a s v -> Formula a s v
pushquants fm0@(Qua qua0 _ _) = case gatherQuants mempty fm0 of
    (hints, Con And p q) | qua0 == All -> push (.&&.) hints p q
    (hints, Con Or  p q) | qua0 == Ex  -> push (.||.) hints p q
    (hints, fm)                        -> addQuants fm hints
  where
    gatherQuants hints (Qua qua hint p)
      | qua == qua0      = gatherQuants (hints `mappend` pure hint) p
    gatherQuants hints p = (D.toList hints, pushquants p)

    addQuants = foldr (Qua qua0)
     
    push op hints p q = 
        pushquants (addQuants p hints) `op` pushquants (addQuants q hints)

pushquants fm0 = fm0

-- | Pulling out quantifiers.
pullquants :: (Functor a, Eq s) => Formula a s v -> Formula a s v
pullquants fm = case fm of
    Con And (Qua All x p) (Qua All x' q) | x == x' -> pull_2 All (.&&.) x p q
    Con Or  (Qua Ex  x p) (Qua Ex  x' q) | x == x' -> pull_2 Ex  (.||.) x p q
    Con And (Qua qua x p) q             -> pull_l qua (.&&.) x p q
    Con And p             (Qua qua x q) -> pull_r qua (.&&.) x p q
    Con Or  (Qua qua x p) q             -> pull_l qua (.||.) x p q
    Con Or  p             (Qua qua x q) -> pull_r qua (.||.) x p q
    _                                   -> fm
  where
    pull_l qua op x p q = Qua qua x (pullquants (p `op` shiftFreeIndices 1 q))
    pull_r qua op x p q = Qua qua x (pullquants (shiftFreeIndices 1 p `op` q))
    pull_2 qua op x p q = Qua qua x (pullquants (p `op` q))

-- | Conversion to prenex normal form under the assumption that the formula is
-- already in NNF.
prenex :: (Functor a, Eq s) => Formula a s v -> Formula a s v
prenex fm = case fm of
    Qua qua x p -> Qua qua x (prenex p)
    Con And p q -> pullquants $ prenex p .&&. prenex q
    Con Or  p q -> pullquants $ prenex p .||. prenex q
    _           -> fm

-- | Conversion to prenex normal form.
pnf :: (Functor a, Foldable a, Eq s) => Formula a s v -> Formula a s v
pnf = prenex . nnf . simplifyFormula


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------


-- | Pretty print a formula.
prettyFormula :: (Eq v, Show v, HighlightDocument d, Functor a, Monad m) 
              => (s -> m v)       -- ^ Name generation action for bound variables.
              -> (a v -> m d)     -- ^ Pretty printing of atoms.
              -> Formula a s v    -- ^ Formula to pretty print.
              -> m d              -- ^ Pretty printed formula.
prettyFormula freshVar ppAto = 
    pp
  where
    extractFree (Free v)  = v
    extractFree (Bound i) = error $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

    pp (Ato a)    = ppAto $ fmap extractFree a
    pp (TF True)  = return $ operator_ "T"                    -- "⊤" 
    pp (TF False) = return $ operator_ "F"                    -- "⊥" 
    pp (Not p)    = do
      p' <- pp p
      return $ operator_ "not" <> opParens p' -- text "¬" <> parens (pp a)

    pp (Con op p q) = do
        p' <- pp p
        q' <- pp q
        return $ sep [opParens p' <-> operator_ (ppOp op), opParens q']
      where
        ppOp And = "&"   -- "∧"
        ppOp Or  = "|"   -- "∨"
        ppOp Imp = "==>" -- "⇒"
        ppOp Iff = "<=>" -- "⇔"

    pp fm@(Qua qua0 _ _) = 
        ppQua [] fm
      where
        ppQua vs (Qua qua hint fm') | qua == qua0 = do
          v <- freshVar hint
          let fm'' = unquantify v fm'
          ppQua (v:vs) fm''

        ppQua vs fm' = do
          fm'' <- pp fm'
          return $ sep 
              [ operator_ (ppQuant qua0) <> ppVars (reverse vs) <> operator_ "."
              , nest 1 fm'']

        ppVars       = fsep . map (text . show)

        ppQuant All = "All " -- "∀"
        ppQuant Ex  = "Ex "  -- "∃"

------------------------------------------------------------------------------
-- Testing
------------------------------------------------------------------------------

type TFormula = Formula Maybe String String

deriving instance Show TFormula
deriving instance Eq   TFormula

t1, t2, t3, t4, t5 :: Bool
t1 = f == (shiftFreeIndices 1 f)
  where
    f :: TFormula
    f = Qua All "s" (Ato $ Just $ Bound 0)

t2 = f == (shiftFreeIndices 1 f)
  where
    f :: TFormula
    f = Qua All "s" $ Qua All "s" (Ato $ Just $ Bound 1)

t3 = f' == (shiftFreeIndices 1 f)
  where
    f :: TFormula
    f = Qua All "s" $ Qua All "s" (Ato $ Just $ Bound 2)
    f' = Qua All "s" $ Qua All "s" (Ato $ Just $ Bound 3)

t4 = "foo" `elem` frees (unquantify "foo" f)
  where
    f :: TFormula
    f = Qua All "s" $ Qua All "s" (Ato $ Just $ Bound 2)

t5 = f == (quantify "foo" $ unquantify "foo" f)
  where
    f :: TFormula
    f = Qua All "s" $ Qua All "s" (Ato $ Just $ Bound 2)

t6 :: Bool
t6 = freeIndices f == [1,0]
  where
    f :: TFormula
    f = Qua All "s" $
            Con And (Ato $ Just $ Bound 2)
                    (Qua All "s" $
                         Con And (Ato $ Just $ Bound 2) (Ato $ Just $ Bound 1))

tests :: [Bool]
tests = [t1,t2,t3,t4,t5,t6]
