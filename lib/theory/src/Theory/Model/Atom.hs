{-# LANGUAGE DeriveDataTypeable   #-}
-- {-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
-- {-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
-- {-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE DeriveFunctor        #-}
-- {-# OPTIONS_GHC -fno-warn-orphans #-}
-- {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2011, 2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Formulas that represent security properties.
module Theory.Model.Atom(

  -- * Atoms
    ProtoAtom(..)
  , Atom
  , SyntacticSugar(..)
  , SyntacticAtom
  , NAtom
  , LNAtom
  , Unit2

  , isActionAtom
  , isSyntacticSugar
  , isLastAtom
  , isLessAtom
  , isEqAtom
  , toAtom

  -- * LFormula
  , BLAtom

  -- * Pretty-Printing
  , prettyProtoAtom
  , prettyAtom
  , prettyNAtom
  , prettySyntacticNAtom
  )
where

-- import           Control.Basics
import           Control.DeepSeq

import           GHC.Generics (Generic)
import           Data.Binary
-- import           Data.Foldable      (Foldable, foldMap)
import           Data.Data
-- import           Data.Monoid        (mappend, mempty)
-- import           Data.Traversable

import           Term.LTerm
import           Term.Unification
import           Theory.Model.Fact
import           Theory.Text.Pretty


------------------------------------------------------------------------------
-- Atoms
------------------------------------------------------------------------------

-- | @ProtoAtom@s are the atoms of trace formulas parametrized over arbitrary
-- terms, including syntactic sugar
data ProtoAtom s t = Action   t (Fact t)
                 | EqE  t t
                 | Less t t
                 | Last t
                 | Syntactic (s t)
            deriving( Eq, Ord, Show, Data, Typeable, Generic, NFData, Binary )

-- | Datatype for syntactic sugar that is removed while parsing
data SyntacticSugar t = Pred (Fact t)
            deriving( Eq, Ord, Show, Data, Typeable, Generic, NFData, Binary
                        , Foldable, Traversable, Functor )

-- Unit type with kind * -> *. Maybe there is a builtin alternative?
data Unit2 t = Unit2
            deriving( Eq, Ord, Show, Data, Typeable, Generic, NFData, Binary
                        , Foldable, Traversable, Functor )

instance Apply (Unit2 t) where apply _ _ = Unit2

-- | @Atom@s are the atoms of trace formulas parametrized over arbitrary
-- terms, excluding syntactic sugar
type Atom t = ProtoAtom Unit2 t

-- | @SyntacticAtom@s are the atoms of trace formulas parametrized over arbitrary
-- terms, including syntactic sugar
type SyntacticAtom t = ProtoAtom SyntacticSugar t

-- | @LAtom@ are the atoms we actually use in graph formulas input by the user.
type NAtom v = Atom (VTerm Name v)

-- | @LAtom@ are the atoms we actually use in graph formulas input by the user.
type LNAtom = Atom LNTerm

-- | Atoms built over 'BLTerm's.
type BLAtom = Atom BLTerm

type SyntacticLNAtom = SyntacticAtom LNTerm
type SyntacticNAtom v = SyntacticAtom (VTerm Name v)
type SyntacticBLAtom = SyntacticAtom BLTerm


-- Instances
------------

instance (Functor s) => Functor (ProtoAtom s) where
    fmap f (Action   i fa) = Action    (f i) (fmap f fa)
    fmap f (EqE l r)       = EqE       (f l) (f r)
    fmap f (Less v u)      = Less      (f v) (f u)
    fmap f (Last i)        = Last      (f i)
    fmap f (Syntactic se)   = Syntactic (fmap f se)

instance (Foldable s) => Foldable (ProtoAtom s) where
    foldMap f (Action i fa)   =
        f i `mappend` (foldMap f fa)
    foldMap f (EqE l r)       = f l `mappend` f r
    foldMap f (Less i j)      = f i `mappend` f j
    foldMap f (Last i)        = f i
    foldMap f (Syntactic s)   = foldMap f s

instance (Traversable s) => Traversable (ProtoAtom s) where
    traverse f (Action i fa)   =
        Action <$> f i <*> traverse f fa
    traverse f (EqE l r)       = EqE <$> f l <*> f r
    traverse f (Less v u)      = Less <$> f v <*> f u
    traverse f (Last i)        = Last <$> f i
    traverse f (Syntactic s)       = Syntactic <$> traverse f s

instance Apply (SyntacticSugar LNTerm) where
    apply subst (Pred fa) = Pred $ apply subst fa

instance Apply (SyntacticSugar BLTerm) where
    apply subst (Pred fa) = Pred $ apply subst fa

instance HasFrees t => HasFrees (Atom t) where
    foldFrees f = foldMap (foldFrees f)
    foldFreesOcc _ _ = const mempty -- we ignore occurences in atoms for now
    mapFrees  f = traverse (mapFrees f)

instance Apply LNAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)
    apply subst (Syntactic fa)    = Syntactic (apply subst fa)

instance Apply BLAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)
    apply subst (Syntactic fa)         = Syntactic (apply subst fa)

instance Apply SyntacticLNAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)
    apply subst (Syntactic fa)         = Syntactic (apply subst fa)

instance Apply SyntacticBLAtom where
    apply subst (Action i fact)   = Action (apply subst i) (apply subst fact)
    apply subst (EqE l r)         = EqE (apply subst l) (apply subst r)
    apply subst (Less i j)        = Less (apply subst i) (apply subst j)
    apply subst (Last i)          = Last (apply subst i)
    apply subst (Syntactic fa)         = Syntactic (apply subst fa)


-- Queries
----------

-- | True iff the atom is an action atom.
isActionAtom :: Atom t -> Bool
isActionAtom ato = case ato of Action _ _ -> True; _ -> False

-- | True iff the atom is a predicate atom.
isSyntacticSugar :: Atom t -> Bool
isSyntacticSugar ato = case ato of Syntactic _ -> True; _ -> False

-- | True iff the atom is a last atom.
isLastAtom :: Atom t -> Bool
isLastAtom ato = case ato of Last _ -> True; _ -> False

-- | True iff the atom is a temporal ordering atom.
isLessAtom :: Atom t -> Bool
isLessAtom ato = case ato of Less _ _ -> True; _ -> False

-- | True iff the atom is an equality atom.
isEqAtom :: Atom t -> Bool
isEqAtom ato = case ato of EqE _ _ -> True; _ -> False


-- | Throw away syntactic sugar
toAtom:: ProtoAtom s t -> Atom t
toAtom (Syntactic _) = Syntactic Unit2
toAtom (Action t fa) = Action t fa
toAtom (EqE t t')    = EqE t t'
toAtom (Less t t')   = Less t t'
toAtom (Last t)      = Last t

------------------------------------------------------------------------------
-- Pretty-Printing
------------------------------------------------------------------------------

prettyProtoAtom :: (Show v, HighlightDocument d) => 
                 (s v -> d)  --  Function for pretty printing syntactic sugar
              -> (v -> d)  --  Function for pretty printing terms / variables
              -> ProtoAtom s v -> d
prettyProtoAtom _ ppT  (Action v fa) =
    prettyFact ppT fa <-> opAction <-> text (show v)
prettyProtoAtom ppS _ (Syntactic s) = ppS s
prettyProtoAtom _ ppT (EqE l r) =
    sep [ppT l <-> opEqual, ppT r]
    -- sep [prettyNTerm l <-> text "≈", prettyNTerm r]
prettyProtoAtom _ _ (Less u v) = text (show u) <-> opLess <-> text (show v)
prettyProtoAtom _ _ (Last i)   = operator_ "last" <> parens (text (show i))

prettyAtom :: (Show v, HighlightDocument d) => 
              (v -> d)  --  Function for pretty printing terms / variables
              -> Atom v -> d
prettyAtom = prettyProtoAtom (const emptyDoc)


prettyNAtom :: (Show v, HighlightDocument d) => NAtom v -> d
prettyNAtom  = prettyAtom prettyNTerm


prettySyntacticNAtom :: (Show v, HighlightDocument d) => SyntacticNAtom v -> d
prettySyntacticNAtom  = prettyProtoAtom prettyPred prettyNTerm
    where
        prettyPred (Pred fa) = prettyNFact fa
