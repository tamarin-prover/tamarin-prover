{-# LANGUAGE TypeOperators, TemplateHaskell, DeriveDataTypeable, ScopedTypeVariables, TupleSections
             , StandaloneDeriving, TypeSynonymInstances, BangPatterns, FlexibleInstances, FlexibleContexts #-}
-- |
-- Copyright   : (c) 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
-- Portability : GHC only
--
-- Guarded formulas.
module Theory.Constraint.System.Guarded (

  -- * Guarded formulas
    Guarded(..)
  , LGuarded
  , LNGuarded

  -- ** Smart constructors
  , gfalse
  , gtrue
  , gdisj
  , gconj
  , gex
  , gall
  , gnot
  , ginduct

  , formulaToGuarded

  -- ** Transformation
  , simplifyGuarded

  , mapGuardedAtoms

  -- ** Queries
  , isConjunction
  , isDisjunction
  , isAllGuarded
  , isExGuarded

  -- ** Conversions to non-bound representations
  , bvarToLVar
  , openGuarded

  -- ** Substitutions
  , substBound
  , substBoundAtom
  , substFree
  , substFreeAtom

  -- ** Pretty-printing
  , prettyGuarded

  ) where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad.Error

import           Debug.Trace

import           Data.Binary
import           Data.DeriveTH
import           Data.Either                (partitionEithers)
import           Data.Foldable              (Foldable(..), foldMap)
import           Data.List
import           Data.Monoid                (mappend, mconcat)
import           Data.Traversable           hiding ( mapM, sequence )

import           Logic.Connectives

import           Text.PrettyPrint.Highlight

import           Control.Arrow
import           Control.Monad.Fresh        hiding ( mapM )

import           Theory.Model


------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

data Guarded s c v = GAto  (Atom (VTerm c (BVar v)))
                   | GDisj (Disj (Guarded s c v))
                   | GConj (Conj (Guarded s c v))
                   | GGuarded Quantifier [s] [Atom (VTerm c (BVar v))] (Guarded s c v)
                    -- ^ Denotes @ALL xs. as => gf@ or @Ex xs. as & gf&
                    -- depending on the 'Quantifier'.
                    -- We assume that all bound variables xs occur in
                    -- f@i atoms in as.
                   deriving (Eq, Ord, Show)

isConjunction :: Guarded t t1 t2 -> Bool
isConjunction (GConj _)  = True
isConjunction _          = False

isDisjunction :: Guarded t t1 t2 -> Bool
isDisjunction (GDisj _)  = True
isDisjunction _          = False

isExGuarded :: Guarded t t1 t2 -> Bool
isExGuarded (GGuarded Ex _ _ _) = True
isExGuarded _                   = False

isAllGuarded :: Guarded t t1 t2 -> Bool
isAllGuarded (GGuarded All _ _ _) = True
isAllGuarded _                    = False

------------------------------------------------------------------------------
-- Folding
------------------------------------------------------------------------------

-- | Fold a guarded formula.
foldGuarded :: (Atom (VTerm c (BVar v)) -> b)
            -> (Disj b -> b)
            -> (Conj b -> b)
            -> (Quantifier -> [s] -> [Atom (VTerm c (BVar v))] -> b -> b)
            -> Guarded s c v
            -> b
foldGuarded fAto fDisj fConj fGuarded =
  go
 where
  go (GAto a)                = fAto a
  go (GDisj disj)            = fDisj $ fmap go disj
  go (GConj conj)            = fConj $ fmap go conj
  go (GGuarded qua ss as gf) = fGuarded qua ss as (go gf)

-- | Fold a guarded formula with scope info.
-- The Integer argument denotes the number of
-- quantifiers that have been encountered so far.
foldGuardedScope :: (Integer -> Atom (VTerm c (BVar v)) -> b)
                 -> (Disj b -> b)
                 -> (Conj b -> b)
                 -> (Quantifier -> [s] -> Integer -> [Atom (VTerm c (BVar v))] -> b -> b)
                 -> Guarded s c v
                 -> b
foldGuardedScope fAto fDisj fConj fGuarded =
  go 0
 where
  go !i (GAto a)            = fAto i a
  go !i (GDisj disj)        = fDisj $ fmap (go i) disj
  go !i (GConj conj)        = fConj $ fmap (go i) conj
  go !i (GGuarded qua ss as gf) =
    fGuarded qua ss i' as (go i' gf)
   where
    i' = i + fromIntegral (length ss)


-- | Map a guarded formula with scope info.
-- The Integer argument denotes the number of
-- quantifiers that have been encountered so far.
mapGuardedAtoms :: (Integer -> Atom (VTerm c (BVar v))
                -> Atom (VTerm d (BVar w)))
                -> Guarded s c v
                -> Guarded s d w
mapGuardedAtoms f =
    foldGuardedScope (\i a -> GAto $ f i a) GDisj GConj
                     (\qua ss i as gf -> GGuarded qua ss (map (f i) as) gf)

------------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------------

{-
instance Functor (Guarded s c) where
    fmap f = foldGuarded (GAto . fmap (fmapTerm (fmap (fmap f)))) GDisj GConj
                         (\qua ss as gf -> GGuarded qua ss (map (fmap (fmapTerm (fmap (fmap f)))) as) gf)
-}

instance Foldable (Guarded s c) where
    foldMap f = foldGuarded (foldMap (foldMap (foldMap (foldMap f))))
                            (mconcat . getDisj)
                            (mconcat . getConj)
                            (\_qua _ss as b -> foldMap (foldMap (foldMap (foldMap (foldMap f)))) as `mappend` b)

traverseGuarded :: (Applicative f, Ord c, Ord v, Ord a)
                => (a -> f v) -> Guarded s c a -> f (Guarded s c v)
traverseGuarded f = foldGuarded (liftA GAto . traverse (traverseTerm (traverse (traverse f))))
                                (liftA GDisj . sequenceA)
                                (liftA GConj . sequenceA)
                                (\qua ss as gf -> GGuarded qua ss <$> traverse (traverse (traverseTerm (traverse (traverse f)))) as <*> gf)

instance Ord c => HasFrees (Guarded (String, LSort) c LVar) where
    foldFrees f = foldMap  (foldFrees f)
    mapFrees  f = traverseGuarded (mapFrees f)


-- FIXME: remove name hints for variables for saturation?
type LGuarded c = Guarded (String, LSort) c LVar

------------------------------------------------------------------------------
-- Substitutions of bound for free and vice versa
------------------------------------------------------------------------------

-- | @substBoundAtom s a@ substitutes each occurence of a bound variables @i@
-- in @dom(s)@ with the corresponding free variable @x=s(i)@ in the atom @a@.
substBoundAtom :: Ord c => [(Integer,LVar)] -> Atom (VTerm c (BVar LVar)) -> Atom (VTerm c (BVar LVar))
substBoundAtom s = fmap (fmapTerm (fmap subst))
 where subst bv@(Bound i') = case lookup i' s of
                               Just x -> Free x
                               Nothing -> bv
       subst fv            = fv

-- | @substBound s gf@ substitutes each occurence of a bound
-- variable @i@ in @dom(s)@ with the corresponding free variable
-- @s(i)=x@ in all atoms in @gf@.
substBound :: Ord c => [(Integer,LVar)] -> LGuarded c -> LGuarded c
substBound s = mapGuardedAtoms (\j a -> substBoundAtom [(i+j,v) | (i,v) <- s] a)


-- | @substFreeAtom s a@ substitutes each occurence of a free variables @v@
-- in @dom(s)@ with the bound variables @i=s(v)@ in the atom @a@.
substFreeAtom :: Ord c
              => [(LVar,Integer)]
              -> Atom (VTerm c (BVar LVar)) -> Atom (VTerm c (BVar LVar))
substFreeAtom s = fmap (fmapTerm (fmap subst))
 where subst fv@(Free x) = case lookup x s of
                               Just i -> Bound i
                               Nothing -> fv
       subst bv          = bv

-- | @substFreeAtom s gf@ substitutes each occurence of a free variables
-- @v in dom(s)@ with the correpsonding bound variables @i=s(v)@
-- in all atoms in  @gf@.
substFree :: Ord c => [(LVar,Integer)] -> LGuarded c -> LGuarded c
substFree s = mapGuardedAtoms (\j a -> substFreeAtom [(v,i+j) | (v,i) <- s] a)

-- | Assuming that there are no more bound variables left in an atom of a
-- formula, convert it to an atom with free variables only.
bvarToLVar :: Ord c => Atom (VTerm c (BVar LVar)) -> Atom (VTerm c LVar)
bvarToLVar =
    fmap (fmapTerm (fmap (foldBVar boundError id)))
  where
    boundError v = error $ "bvarToLVar: left-over bound variable '"
                           ++ show v ++ "'"

-- | Provided an 'Atom' does not contain a bound variable, it is converted to
-- the type of atoms without bound varaibles.
unbindAtom :: (Ord c, Ord v) => Atom (VTerm c (BVar v)) -> Maybe (Atom (VTerm c v))
unbindAtom = traverse (traverseTerm (traverse (foldBVar (const Nothing) Just)))


------------------------------------------------------------------------------
-- Opening and Closing
------------------------------------------------------------------------------

-- | @openGuarded gf@ returns @Just (qua,vs,ats,gf')@ if @gf@ is a guarded
-- clause and @Nothing@ otherwise. In the first case, @quao@ is the quantifier,
-- @vs@ is a list of fresh variables, @ats@ is the antecedent, and @gf'@ is the
-- succedent. In both antecedent and succedent, the bound variables are
-- replaced by @vs@.
openGuarded :: (Ord c, MonadFresh m)
            => LGuarded c -> m (Maybe (Quantifier, [LVar], [Atom (VTerm c LVar)], LGuarded c))
openGuarded (GGuarded qua vs as gf) = do
    xs <- mapM (\(n,s) -> freshLVar n s) vs
    return $ Just (qua, xs, openas xs, opengf xs)
  where
    openas xs = map (bvarToLVar . substBoundAtom (subst xs)) as
    opengf xs = substBound (subst xs) gf
    subst xs  = zip [0..] (reverse xs)
openGuarded _ = return Nothing

-- | @closeGuarded vs ats gf@ is a smart constructor for @GGuarded@.
closeGuarded :: Ord c => Quantifier -> [LVar] -> [Atom (VTerm c LVar)]
             -> LGuarded c -> LGuarded c
closeGuarded qua vs as gf = GGuarded qua vs' as' gf'
 where as' = map (substFreeAtom s . fmap (fmapTerm (fmap Free))) as
       gf' = substFree s gf
       s   = zip (reverse vs) [0..]
       vs' = map (lvarName &&& lvarSort) vs


------------------------------------------------------------------------------
-- Conversion and negation
------------------------------------------------------------------------------

type LNGuarded = Guarded (String,LSort) Name LVar

-- | @gtf b@ returns the guarded formula f with @b <-> f@.
gtf :: Bool -> Guarded s c v
gtf False = GDisj (Disj [])
gtf True  = GConj (Conj [])

-- | @gfalse@ returns the guarded formula f with @False <-> f@.
gfalse :: Guarded s c v
gfalse = gtf False

-- | @gtrue@ returns the guarded formula f with @True <-> f@.
gtrue :: Guarded s c v
gtrue = gtf True

-- | @gnotAtom a@ returns the guarded formula f with @not a <-> f@.
gnotAtom :: Atom (VTerm c (BVar v)) -> Guarded s c v
gnotAtom a  = GGuarded All [] [a] gfalse

-- | @gconj gfs@ smart constructor for the conjunction of gfs.
gconj :: (Ord s, Ord c, Ord v) => [Guarded s c v] -> Guarded s c v
gconj gfs0 = case concatMap flatten gfs0 of
    [gf]                      -> gf
    gfs | any (gfalse ==) gfs -> gfalse
        -- FIXME: See 'sortednub' below.
        | otherwise           -> GConj $ Conj $ nub gfs
  where
    flatten (GConj conj) = concatMap flatten $ getConj conj
    flatten gf           = [gf]

-- | @gdisj gfs@ smart constructor for the disjunction of gfs.
gdisj :: (Ord s, Ord c, Ord v) => [Guarded s c v] -> Guarded s c v
gdisj gfs0 = case concatMap flatten gfs0 of
    [gf]                     -> gf
    gfs | any (gtrue ==) gfs -> gtrue
        -- FIXME: Consider using 'sortednub' here. This yields stronger
        -- normalizaton for formulas. However, it also means that we loose
        -- invariance under renaming free variables, as the order changes,
        -- when they are renamed.
        | otherwise          -> GDisj $ Disj $ nub gfs
  where
    flatten (GDisj disj) = concatMap flatten $ getDisj disj
    flatten gf           = [gf]

-- @ A smart constructor for @GGuarded Ex@ that removes empty quantifications.
gex :: (Ord s, Ord c, Ord v)
    => [s] -> [Atom (VTerm c (BVar v))] -> Guarded s c v -> Guarded s c v
gex [] as gf = gconj (map GAto as ++ [gf])
gex ss as gf = GGuarded Ex ss as gf

-- @ A smart constructor for @GGuarded All@ that drops implications to 'gtrue'
-- and removes empty premises.
gall :: (Eq s, Eq c, Eq v)
     => [s] -> [Atom (VTerm c (BVar v))] -> Guarded s c v -> Guarded s c v
gall _  []   gf               = gf
gall _  _    gf | gf == gtrue = gtrue
gall ss atos gf               = GGuarded All ss atos gf

-- | @formulaToGuarded fm@ returns a guarded formula @gf@ that is
-- equivalent to @fm@ if possible.
formulaToGuarded :: LNFormula  -> Either String LNGuarded
formulaToGuarded = convert False

-- | @convert neg f@ returns @Nothing@ if @f@ cannot be converted,
-- @Just gf@ such that @mneg f <-> gf@ with @mneg = id@ if @neg@ is @False@
-- and @mneg=not@ if @neg@ is true.
convert :: Bool -> LNFormula  -> Either String LNGuarded
convert True  (Ato a) = pure $ gnotAtom a
convert False (Ato a) = pure $ GAto a

convert polarity (Not f) = convert (not polarity) f

convert True  (Conn And f g) = gdisj <$> mapM (convert True)  [f, g]
convert False (Conn And f g) = gconj <$> mapM (convert False) [f, g]

convert True  (Conn Or f g)  = gconj <$> mapM (convert True)  [f, g]
convert False (Conn Or f g)  = gdisj <$> mapM (convert False) [f, g]

convert True  (Conn Imp f g         ) =
    gconj <$> sequence [convert False f, convert True  g]
convert False (Conn Imp f g         ) =
    gdisj <$> sequence [convert True  f, convert False g]

convert polarity    (TF b) = pure $ gtf (polarity /= b)

convert polarity f0@(Qua qua0 _ _) =
    -- The quantifier switch stems from our implicit negation of the formula.
    case (qua0, polarity) of
      (All, True ) -> convAll Ex
      (All, False) -> convAll All
      (Ex,  True ) -> convEx  All
      (Ex,  False) -> convEx  Ex
  where
    convEx qua = do
      (xs,_,f) <- openFormulaPrefix f0 `evalFreshT` avoid f0
      case partitionEithers $ partitionConj f of
        (as, fs) -> do
          let guardedvars = frees as
              -- all existentially quantified variables must be guarded
              unguarded = xs \\ guardedvars

          unless (null unguarded) $ throwError $
              "unguarded variables " ++ show unguarded ++ " in " ++ show f0

          gf <- (if polarity then gdisj else gconj)
                  <$> mapM (convert polarity) fs
          return $ closeGuarded qua xs as gf
      where
        partitionConj (Conn And f1 f2)     = partitionConj f1 ++ partitionConj f2
        partitionConj (Ato a@(Action _ _)) = [Left $ bvarToLVar a]
        partitionConj (Ato e@(EqE _ _))    = [Left $ bvarToLVar e]
        partitionConj f                    = [Right f]

    convAll qua = do
      (xs,_,f) <- openFormulaPrefix f0 `evalFreshT` avoid f0
      case f of
        Conn Imp ante suc -> do
          allowedAtoms <- collectAllowedAtoms ante

          let guardedvars = frees [ a | a@(Action _ _) <- allowedAtoms ]
              -- all universally quantified variables must be guarded
              unguarded = xs \\ guardedvars

          when (not $ null unguarded) $ throwError $
              "unguarded variables " ++ show unguarded ++ " in " ++ show f0

          g <- convert polarity suc
          return $ closeGuarded qua xs allowedAtoms g

        _ -> throwError $ show f ++ "outside guarded fragment"
     where
      collectAllowedAtoms (Conn And f1 f2)     =
        (++) <$> collectAllowedAtoms f1 <*> collectAllowedAtoms f2
      collectAllowedAtoms (Ato a@(Action _ _)) = return [bvarToLVar a]
      collectAllowedAtoms (Ato e@(EqE _ _))    = return [bvarToLVar e]
      collectAllowedAtoms na                   =
        throwError $ show na ++ " not allowed in antecedent"

convert _     (Conn Iff _ _) =
  Left $ "`iff' not supported (yet)"

instance Apply LNGuarded where
  apply subst = mapGuardedAtoms (const $ apply subst)


------------------------------------------------------------------------------
-- Induction over the trace
------------------------------------------------------------------------------

-- Note that we assume that the guarded formula describes the attack.
-- Hence, we want to show that it is false.

{-
-- | Checks if a doubly guarded formula is last-free; i.e., does not contain a 'Last'
-- atom.
lastFree :: Guarded s c v -> Bool
lastFree = error "lastFree: implement"

-- | Checks if a formula is doubly guarded; i.e., both universal and existential
-- quantifiers are guarded.
doublyGuarded :: Guarded s c v -> Bool
doublyGuarded = either (const False) (const True) . satisfiedByEmptyTrace
-}

-- | Negate a guarded formula.
gnot :: (Ord s, Ord c, Ord v)
              => Guarded s c v -> Guarded s c v
gnot =
    go
  where
    go (GGuarded All ss as gf) = gex  ss as $ go gf
    go (GGuarded Ex ss as gf)  = gall ss as $ go gf
    go (GAto ato)              = gnotAtom ato
    go (GDisj disj)            = gconj $ map go (getDisj disj)
    go (GConj conj)            = gdisj $ map go (getConj conj)


-- | Checks if a doubly guarded formula is satisfied by the empty trace;
-- returns @'Left' errMsg@ if the formula is not doubly guarded.
satisfiedByEmptyTrace :: Guarded s c v -> Either String Bool
satisfiedByEmptyTrace =
  foldGuarded
    (\_ato -> throwError "atom outside the scope of a quantifier")
    (liftM or  . sequence . getDisj)
    (liftM and . sequence . getConj)
    (\qua _ss _as _gf -> return $ qua == All)
    -- the empty trace always satisfies guarded all-quantification
    -- and always dissatisfies guarded ex-quantification

-- | Tries to convert a doubly guarded formula to an induction hypothesis.
-- Returns @'Left' errMsg@ if the formula is not last-free or not doubly
-- guarded.
toInductionHypothesis :: Ord c => LGuarded c -> Either String (LGuarded c)
toInductionHypothesis =
    go
  where
    go (GGuarded qua ss as gf) = do
        gf' <- go gf
        return $ case qua of
          All -> GGuarded Ex  ss as (gconj $ (gnotAtom <$> lastAtos) ++ [gf'])
          Ex  -> GGuarded All ss as (gdisj $ (GAto <$> lastAtos) ++ [gf'])

      where
        lastAtos :: [Atom (VTerm c (BVar LVar))]
        lastAtos = do
            (j, (_, LSortNode)) <- zip [0..] $ reverse ss
            return $ Last (varTerm (Bound j))

    go (GAto (Less i j)) = return $ gdisj [GAto (EqE i j), GAto (Less j i)]
    go (GAto (Last _))   = throwError "formula not last-free"
    go (GAto ato)        = return $ gnotAtom ato
    go (GDisj disj)      = gconj <$> traverse go (getDisj disj)
    go (GConj conj)      = gdisj <$> traverse go (getConj conj)

-- | Try to prove the formula by applying induction over the trace.
-- Returns @'Left' errMsg@ if this is not possible.
ginduct :: Ord c => LGuarded c -> Either String (LGuarded c)
ginduct gf = do
    baseCase <- satisfiedByEmptyTrace gf
    if baseCase
      then throwError "cannot apply induction: empty trace is an attack"
      else do
        gfIH <- toInductionHypothesis gf
        return (gconj [gf, gfIH])

------------------------------------------------------------------------------
-- Formula Simplification
------------------------------------------------------------------------------

-- | Simplify a 'Guarded' formula by replacing atoms with their truth value,
-- if it can be determined.
simplifyGuarded :: (LNAtom -> Maybe Bool)
                -- ^ Partial assignment for truth value of atoms.
                -> LNGuarded
                -- ^ Original formula
                -> Maybe LNGuarded
                -- ^ Simplified formula, provided some simplification was
                -- performed.
simplifyGuarded valuation fm0
    | fm1 /= fm0 = trace (render ppMsg) (Just fm1)
    | otherwise  = Nothing
  where
    ppFm  = nest 2 . doubleQuotes . prettyGuarded
    ppMsg = nest 2 $ text "simplified formula:" $-$
                     nest 2 (vcat [ ppFm fm0, text "to", ppFm fm1])

    fm1 = simp fm0

    simp fm@(GAto ato)         = maybe fm gtf (valuation =<< unbindAtom ato)
    simp (GDisj fms)           = gdisj $ map simp $ getDisj fms
    simp (GConj fms)           = gconj $ map simp $ getConj fms
    simp (GGuarded All [] atos gf)
      | any ((Just False ==) . snd) annAtos = gtrue
      | otherwise                           =
          -- keep all atoms that we cannot evaluate yet.
          -- NOTE: Here we are missing the opportunity to change the valuation
          -- for evaluating the body 'gf'. We could add all atoms that we have
          -- as a premise.
          gall [] (fst <$> filter ((Nothing ==) . snd) annAtos) (simp gf)
      where
        -- cache the possibly expensive evaluation of the valuation
        annAtos = (\x -> (x, valuation =<< unbindAtom x)) <$> atos

    -- Note that existentials without quantifiers are already eliminated by
    -- 'gex'. Moreover, we dealay simplification inside guarded all
    -- quantification and guarded existential quantifiers. Their body will be
    -- simplified once the quantifiers are gone.
    simp fm@(GGuarded _ _ _ _) = fm


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | Pretty print a formula.
prettyGuarded :: HighlightDocument d
              => LNGuarded      -- ^ Guarded Formula.
              -> d              -- ^ Pretty printed formula.
prettyGuarded f =
    pp f `evalFreshAvoiding` f
  where
    pp :: HighlightDocument d => LNGuarded -> Fresh d
    pp (GAto a) = return $ prettyNAtom $ bvarToLVar a

    pp (GDisj (Disj [])) = return $ operator_ "F"

    pp (GDisj (Disj xs)) = do
        ps <- mapM (\x -> opParens <$> pp x) xs
        return $ sep $ punctuate (operator_ " |") ps

    pp (GConj (Conj [])) = return $ operator_ "T"

    pp (GConj (Conj xs)) = do
        ps <- mapM (\x -> opParens <$> pp x) xs
        return $ sep $ punctuate (operator_ " &") ps

    pp gf0@(GGuarded _ _ _ _) = do
      Just (qua, vs, atoms, gf) <- openGuarded gf0
      dante <- pp (GConj (Conj (map (GAto . fmap (fmapTerm (fmap Free))) atoms)))
      dsucc <- pp gf
      return $ sep [ operator_ (show qua) <-> ppVars vs <> operator_ "."
                   , nest 1 dante
                   , operator_ (case qua of All -> "==>"; Ex -> "&")
                   , nest 1 dsucc]
      where
        ppVars       = fsep . map (text . show)


-- Derived instances
--------------------

$( derive makeBinary ''Guarded)
$( derive makeNFData ''Guarded)
