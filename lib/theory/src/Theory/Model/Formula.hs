{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier & Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Types and operations for handling sorted first-order logic
module Theory.Model.Formula (

   -- * Formulas
    Connective(..)
  , Quantifier(..)
  , Formula(..)
  , LNFormula
  , LFormula

  , quantify
  , openFormula
  , openFormulaPrefix
--  , unquantify

  -- ** More convenient constructors
  , lfalse
  , ltrue
  , (.&&.)
  , (.||.)
  , (.==>.)
  , (.<=>.)
  , exists
  , forall
  , hinted

  -- ** General Transformations
  , mapAtoms
  , foldFormula

  -- ** Normal forms / simplification
  , simplifyFormula
  -- , nnf
  -- , pullquants
  -- , prenex
  -- , pnf
  , shiftFreeIndices

  -- ** Pretty-Printing
  , prettyLNFormula

  ) where

import           Prelude                          hiding (negate)

import           GHC.Generics (Generic)
import           Data.Binary
-- import           Data.Foldable                    (Foldable, foldMap)
import           Data.Data
-- import           Data.Monoid                      hiding (All)
-- import           Data.Traversable

import           Control.Basics
import           Control.DeepSeq
import           Control.Monad.Fresh
import qualified Control.Monad.Trans.PreciseFresh as Precise

import           Theory.Model.Atom

import           Text.PrettyPrint.Highlight
import           Theory.Text.Pretty

import           Term.LTerm
import           Term.Substitution

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- | Logical connectives.
data Connective = And | Or | Imp | Iff
                deriving( Eq, Ord, Show, Enum, Bounded, Data, Typeable, Generic, NFData, Binary )

-- | Quantifiers.
data Quantifier = All | Ex
                deriving( Eq, Ord, Show, Enum, Bounded, Data, Typeable, Generic, NFData, Binary )


-- | First-order formulas in locally nameless representation with hints for the
-- names/sorts of quantified variables.
data Formula s c v = Ato (Atom (VTerm c (BVar v)))
                   | TF !Bool
                   | Not (Formula s c v)
                   | Conn !Connective (Formula s c v) (Formula s c v)
                   | Qua !Quantifier s (Formula s c v)
                   deriving ( Generic, NFData, Binary )

-- Folding
----------

-- | Fold a formula.
{-# INLINE foldFormula #-}
foldFormula :: (Atom (VTerm c (BVar v)) -> b) -> (Bool -> b)
            -> (b -> b) -> (Connective -> b -> b -> b)
            -> (Quantifier -> s -> b -> b)
            -> Formula s c v
            -> b
foldFormula fAto fTF fNot fConn fQua =
    go
  where
    go (Ato a)       = fAto a
    go (TF b)        = fTF b
    go (Not p)       = fNot (go p)
    go (Conn c p q)  = fConn c (go p) (go q)
    go (Qua qua x p) = fQua qua x (go p)

-- | Fold a formula.
{-# INLINE foldFormulaScope #-}
foldFormulaScope :: (Integer -> Atom (VTerm c (BVar v)) -> b) -> (Bool -> b)
                 -> (b -> b) -> (Connective -> b -> b -> b)
                 -> (Quantifier -> s -> b -> b)
                 -> Formula s c v
                 -> b
foldFormulaScope fAto fTF fNot fConn fQua =
    go 0
  where
    go !i (Ato a)       = fAto i a
    go _  (TF b)        = fTF b
    go !i (Not p)       = fNot (go i p)
    go !i (Conn c p q)  = fConn c (go i p) (go i q)
    go !i (Qua qua x p) = fQua qua x (go (succ i) p)


-- Instances
------------

{-
instance Functor (Formula s c) where
    fmap f = foldFormula (Ato . fmap (fmap (fmap (fmap f)))) TF Not Conn Qua
-}

instance Foldable (Formula s c) where
    foldMap f = foldFormula (foldMap (foldMap (foldMap (foldMap f)))) mempty id
                            (const mappend) (const $ const id)

traverseFormula :: (Ord v, Ord c, Ord v', Applicative f)
                => (v -> f v') -> Formula s c v -> f (Formula s c v')
traverseFormula f = foldFormula (liftA Ato . traverse (traverseTerm (traverse (traverse f))))
                                (pure . TF) (liftA Not)
                                (liftA2 . Conn) ((liftA .) . Qua)
{-
instance Traversable (Formula a s) where
    traverse f = foldFormula (liftA Ato . traverseAtom (traverseTerm  (traverseLit (traverseBVar f))))
                             (pure . TF) (liftA Not)
                             (liftA2 . Conn) ((liftA .) . Qua)
-}

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
(.&&.)  = Conn And
(.||.)  = Conn Or
(.==>.) = Conn Imp
(.<=>.) = Conn Iff

------------------------------------------------------------------------------
-- Dealing with bound variables
------------------------------------------------------------------------------

-- | @LFormula@ are FOL formulas with sorts abused to denote both a hint for
-- the name of the bound variable, as well as the variable's actual sort.
type LFormula c = Formula (String, LSort) c LVar

type LNFormula = Formula (String, LSort) Name LVar

-- | Change the representation of atoms.
mapAtoms :: (Integer -> Atom (VTerm c (BVar v))
         -> Atom (VTerm c1 (BVar v1)))
         -> Formula s c v -> Formula s c1 v1
mapAtoms f = foldFormulaScope (\i a -> Ato $ f i a) TF Not Conn Qua

-- | @openFormula f@ returns @Just (v,Q,f')@ if @f = Q v. f'@ modulo
-- alpha renaming and @Nothing otherwise@. @v@ is always chosen to be fresh.
openFormula :: (MonadFresh m, Ord c)
            => LFormula c -> Maybe (Quantifier, m (LVar, LFormula c))
openFormula (Qua qua (n,s) fm) =
    Just ( qua
         , do x <- freshLVar n s
              return $ (x, mapAtoms (\i a -> fmap (mapLits (subst x i)) a) fm)
         )
  where
    subst x i (Var (Bound i')) | i == i' = Var $ Free x
    subst _ _ l                          = l

openFormula _ = Nothing

mapLits :: (Ord a, Ord b) => (a -> b) -> Term a -> Term b
mapLits f t = case viewTerm t of
    Lit l     -> lit . f $ l
    FApp o as -> fApp o (map (mapLits f) as)

-- | @openFormulaPrefix f@ returns @Just (vs,Q,f')@ if @f = Q v_1 .. v_k. f'@
-- modulo alpha renaming and @Nothing otherwise@. @vs@ is always chosen to be
-- fresh.
openFormulaPrefix :: (MonadFresh m, Ord c)
                  => LFormula c -> m ([LVar], Quantifier, LFormula c)
openFormulaPrefix f0 = case openFormula f0 of
    Nothing        -> error $ "openFormulaPrefix: no outermost quantifier"
    Just (q, open) -> do
      (x, f) <- open
      go q [x] f
  where
    go q xs f = case openFormula f of
        Just (q', open') | q' == q -> do (x', f') <- open'
                                         go q (x' : xs) f'
        -- no further quantifier of the same kind => return result
        _ -> return (reverse xs, q, f)


-- Instances
------------

deriving instance Eq       LNFormula
deriving instance Show     LNFormula
deriving instance Ord      LNFormula

instance HasFrees LNFormula where
    foldFrees  f = foldMap  (foldFrees  f)
    foldFreesOcc _ _ = const mempty -- we ignore occurences in Formulas for now
    mapFrees   f = traverseFormula (mapFrees   f)

instance Apply LNFormula where
    apply subst = mapAtoms (const $ apply subst)

------------------------------------------------------------------------------
-- Formulas modulo E and modulo AC
------------------------------------------------------------------------------

-- | Introduce a bound variable for a free variable.
quantify :: (Ord c, Ord v) => v -> Formula s c v -> Formula s c v
quantify x =
    mapAtoms (\i a -> fmap (mapLits (fmap (>>= subst i))) a)
  where
    subst i v | v == x    = Bound i
              | otherwise = Free v

-- | Create a universal quantification with a sort hint for the bound variable.
forall :: (Ord c, Ord v) => s -> v -> Formula s c v -> Formula s c v
forall hint x = Qua All hint . quantify x

-- | Create a existential quantification with a sort hint for the bound variable.
exists :: (Ord c, Ord v) => s -> v -> Formula s c v -> Formula s c v
exists hint x = Qua Ex hint . quantify x

-- | Transform @forall@ and @exists@ into functions that operate on logical variables
hinted :: ((String, LSort) -> LVar -> a) -> LVar -> a
hinted f v@(LVar n s _) = f (n,s) v



------------------------------------------------------------------------------
-- Normal forms / simplification (adopted from FOL.hs)
------------------------------------------------------------------------------

-- | First-order simplification
simplifyFormula :: (Eq c, Eq v) => Formula s c v -> Formula s c v
simplifyFormula fm0 = case fm0 of
    Ato a        -> simplifyFormula1 $ Ato a
    Not p        -> simplifyFormula1 $ Not (simplifyFormula p)
    Conn And p q -> simplifyFormula1 $ simplifyFormula p .&&.  simplifyFormula q
    Conn Or  p q -> simplifyFormula1 $ simplifyFormula p .||.  simplifyFormula q
    Conn Imp p q -> simplifyFormula1 $ simplifyFormula p .==>. simplifyFormula q
    Conn Iff p q -> simplifyFormula1 $ simplifyFormula p .<=>. simplifyFormula q
    Qua qua x p  -> simplifyFormula1 $ Qua qua x (simplifyFormula p)
    _            -> fm0
  where
    simplifyFormula1 fm = case fm of
        a@(Ato (EqE l r))               -> if l == r then TF True else a
        Not (TF b)                      -> TF (not b)
        Conn And (TF False) _           -> TF False
        Conn And _          (TF False)  -> TF False
        Conn And (TF True)  q           -> q
        Conn And p          (TF True)   -> p
        Conn Or  (TF False) q           -> q
        Conn Or  p          (TF False)  -> p
        Conn Or  (TF True)  _           -> TF True
        Conn Or  _          (TF True)   -> TF True
        Conn Imp (TF False) _           -> TF True
        Conn Imp (TF True)  q           -> q
        Conn Imp _          (TF True)   -> TF True
        Conn Imp p          (TF False)  -> Not p
        Conn Iff (TF True)  q           -> q
        Conn Iff p          (TF True)   -> p
        Conn Iff (TF False) (TF False)  -> TF True
        Conn Iff (TF False) q           -> Not q
        Conn Iff p          (TF False)  -> Not p
        Qua  _   _          (TF b)      -> TF b
        _                               -> fm

-- | Negation normal form.
nnf :: Formula s c v -> Formula s c v
nnf fm = case fm of 
    Conn And p q        -> nnf p       .&&. nnf q
    Conn Or  p q        -> nnf p       .||. nnf q
    Conn Imp p q        -> nnf (Not p) .||. nnf q
    Conn Iff p q        -> (nnf p .&&. nnf q) .||. (nnf (Not p) .&&. nnf (Not q))
    Not (Not p)         -> nnf p
    Not (Conn And p q ) -> nnf (Not p) .||. nnf (Not q)
    Not (Conn Or  p q ) -> nnf (Not p) .&&. nnf (Not q)
    Not (Conn Imp p q ) -> nnf p       .&&. nnf (Not q)
    Not (Conn Iff p q ) -> (nnf p .&&. nnf (Not q)) .||. (nnf(Not p) .&&. nnf q)
    Qua qua x p         -> Qua qua     x $ nnf p
    Not (Qua All x p)   -> Qua Ex  x $ nnf (Not p)
    Not (Qua Ex  x p)   -> Qua All x $ nnf (Not p)
    _                   -> fm

-- | Pulling out quantifiers.
pullquants :: (Ord c, Ord v, Eq s) => Formula s c v -> Formula s c v
pullquants fm = case fm of
    Conn And (Qua All x p) (Qua All x' q) | x == x' -> pull_2 All (.&&.) x p q
    Conn Or  (Qua Ex  x p) (Qua Ex  x' q) | x == x' -> pull_2 Ex  (.||.) x p q
    Conn And (Qua qua x p) q             -> pull_l qua (.&&.) x p q
    Conn And p             (Qua qua x q) -> pull_r qua (.&&.) x p q
    Conn Or  (Qua qua x p) q             -> pull_l qua (.||.) x p q
    Conn Or  p             (Qua qua x q) -> pull_r qua (.||.) x p q
    _                                    -> fm
  where
    pull_l qua op x p q = Qua qua x (pullquants (p `op` shiftFreeIndices 1 q))
    pull_r qua op x p q = Qua qua x (pullquants (shiftFreeIndices 1 p `op` q))
    pull_2 qua op x p q = Qua qua x (pullquants (p `op` q))

-- | Conversion to prenex normal form under the assumption that the formula is already in NNF.
prenex :: (Ord c, Ord v, Eq s) => Formula s c v -> Formula s c v
prenex fm = case fm of
    Qua qua x p  -> Qua qua x (prenex p)
    Conn And p q -> pullquants $ prenex p .&&. prenex q
    Conn Or  p q -> pullquants $ prenex p .||. prenex q
    _            -> fm

-- | Conversion to prenex normal form.
pnf :: (Ord c, Ord v, Eq s) => Formula s c v -> Formula s c v
pnf = simplifyFormula . prenex . nnf . simplifyFormula

-- | Increase the bound variables by the given amount. This has to be used when
-- moving a sub-formula inside an abstraction.
shiftFreeIndices :: (Ord c, Ord v) => Integer -> Formula s c v -> Formula s c v
shiftFreeIndices n =
    mapAtoms (\i a -> fmap (mapLits (fmap (foldBVar (Bound . shift i) Free))) a)
  where
     shift i j | j < i     = j
               | otherwise = j + n



------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print a formula.
prettyLFormula :: (HighlightDocument d, MonadFresh m, Ord c)
              => (Atom (VTerm c LVar) -> d)  -- ^ Function for pretty printing atoms
              -> LFormula c                      -- ^ Formula to pretty print.
              -> m d                             -- ^ Pretty printed formula.
prettyLFormula ppAtom =
    pp
  where
    extractFree (Free v)  = v
    extractFree (Bound i) = error $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

    pp (Ato a)    = return $ ppAtom (fmap (mapLits (fmap extractFree)) a)
    pp (TF True)  = return $ operator_ "⊤"    -- "T"
    pp (TF False) = return $ operator_ "⊥"    -- "F"

    pp (Not p)    = do
      p' <- pp p
      return $ operator_ "¬" <> opParens p' -- text "¬" <> parens (pp a)
      -- return $ operator_ "not" <> opParens p' -- text "¬" <> parens (pp a)

    pp (Conn op p q) = do
        p' <- pp p
        q' <- pp q
        return $ sep [opParens p' <-> ppOp op, opParens q']
      where
        ppOp And = opLAnd
        ppOp Or  = opLOr
        ppOp Imp = opImp
        ppOp Iff = opIff

    pp fm@(Qua _ _ _) =
        scopeFreshness $ do
            (vs,qua,fm') <- openFormulaPrefix fm
            d' <- pp fm'
            return $ sep
                     [ ppQuant qua <> ppVars vs <> operator_ "."
                     , nest 1 d']
      where
        ppVars       = fsep . map (text . show)

        ppQuant All = opForall
        ppQuant Ex  = opExists


-- | Pretty print a logical formula
prettyLNFormula :: HighlightDocument d => LNFormula -> d
prettyLNFormula fm =
    Precise.evalFresh (prettyLFormula prettyNAtom fm) (avoidPrecise fm)
