{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Data types for SAPIC processes in theories
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
module Theory.Sapic.Term (
    -- types
      SapicType
    , defaultSapicTypeS
    , defaultSapicType
    , defaultSapicNodeType
    , SapicFunType
    , SapicLVar(..)
    , SapicTerm
    , SapicNTerm
    , SapicLNFact
    , SapicNFact
    , SapicNFormula
    , SapicFormula
    , SapicFunSym
    , SapicSubst
    -- converters
    , toLVar
    , toLNTerm
    , toLNFact
    , toLFormula
    -- utitlities
    , freesSapicTerm
    , freesSapicFact
    , freshSapicLVarCopy
    -- pretty printing
    , prettySapicTerm
    , prettySapicFact
    , prettySyntacticSapicFormula
    , prettySapicFunType
) where

import Data.Binary
import Data.Data
import GHC.Generics (Generic)
import Control.Parallel.Strategies
import Theory.Model.Fact
import Theory.Model.Atom
import Theory.Model.Formula
import Term.Substitution
import Theory.Text.Pretty
import Data.List (intercalate)
import Control.Monad.Fresh

-- | A process data structure

-- | In general, terms we use in the translation have logical veriables
type SapicType = Maybe String
data SapicLVar = SapicLVar { slvar:: LVar, stype:: SapicType}
     deriving( Ord, Eq, Typeable, Data, Generic, NFData, Binary, IsVar )

type LNTTerm = VTerm Name SapicLVar
type SapicNTerm v = VTerm Name v
type SapicTerm = LNTTerm
type SapicNFact v = Fact (SapicNTerm v)
type SapicLNFact = Fact SapicTerm
type SapicNFormula v = ProtoFormula SyntacticSugar (String, LSort) Name v
type SapicFormula = ProtoFormula SyntacticSugar (String, LSort) Name SapicLVar

-- | Function symbol (f,l,r) with argument types l and return type r
-- define only on NoEqSyms, as we will assume the others to be polymorphic
type SapicFunSym = (NoEqSym, [SapicType], SapicType)
type SapicFunType = ([SapicType], SapicType)

-- TODO alternative definition.
-- 1. If we need to extend, switch to this tyoe
-- 2. If we are done and merge into main and have not used it,
--    then delete this comment.
-- data SapicFunSym = SapicFunSym
--        { _sfSym            :: NoEqSym
--        , _sfOutType        :: SapicType
--        , _sfInType         :: [SapicType]
--        }
--        deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- $(mkLabels [''SapicFunSym])

defaultSapicTypeS :: String
defaultSapicTypeS = "Any"
defaultSapicType :: SapicType
defaultSapicType = Nothing

defaultSapicNodeType :: SapicType
defaultSapicNodeType = Just "node"

-- | A substitution with names and typed logical variables.
type SapicSubst = Subst Name SapicLVar

deriving instance Data SapicSubst


instance Show SapicLVar where
    show (SapicLVar v (Just t)) = show  v ++ ":" ++ t
    show (SapicLVar v Nothing ) = show  v
instance Hinted SapicLVar where
    hint (SapicLVar v _) = hint v

-- | apply substitutions on LVars ignoring (and preserving) the type
instance Apply (Subst Name LVar) SapicLVar
    where
        apply s (SapicLVar v t) = SapicLVar (apply s v) t

-- | apply substitutions on SapicTerms ignoring (and preserving) the type
instance Apply (Subst Name LVar) SapicTerm
    where
        apply = applyVTermProj applyLit'
            where
                 applyLit' subst (Var v) = LIT (Var (apply subst v))
                 applyLit' _     (Con v) = LIT (Con v)

prettySapicFunType :: SapicFunType -> String
prettySapicFunType (ins,out) = intercalate  " * " (map show ins) ++ " -> " ++ show out

-- | return free variabes in SapicTerm  (frees from HasFrees only returns LVars)
freesSapicTerm :: VTerm n v -> [v]
freesSapicTerm = foldMap $ foldMap (: [])

-- | return free variabes in SapicFact
---- fold over terms in fact and use freesSapicTerm to get list monoid
freesSapicFact :: Fact (VTerm n v) -> [v]
freesSapicFact = foldMap freesSapicTerm

-- conversion functions for sapic types
toLVar:: SapicLVar -> LVar
toLVar = slvar

toLNTerm:: SapicTerm -> LNTerm
toLNTerm = fmap f
    where
        f (Con c) = Con c
        f (Var v) = Var $ toLVar v

toLNFact:: SapicLNFact -> LNFact
toLNFact = fmap toLNTerm

toLFormula:: (Functor syn) => ProtoFormula syn (String, LSort) c SapicLVar -> ProtoFormula syn (String, LSort) c LVar
toLFormula = mapAtoms f
    where f _ = fmap $ fmap $ fmap $ fmap toLVar

-- | Create fresh copy of a sapic variable
freshSapicLVarCopy :: MonadFresh m => SapicLVar -> m SapicLVar
freshSapicLVarCopy sv = do
    flv <- freshLVar name sort 
    return sv {slvar = flv}
    where
        lv = toLVar sv
        name = lvarName lv
        sort = lvarSort lv

-- | Pretty print an @SapicTerm@.
-- prettySapicTerm :: Document d => SapicTerm -> d
prettySapicTerm :: (Document d, Show v) => SapicNTerm v -> d
prettySapicTerm = prettyTerm (text . show)

prettySapicFact :: Document d => Fact SapicTerm -> d
prettySapicFact = prettyFact prettySapicTerm

prettySyntacticSapicFormula :: HighlightDocument d => ProtoFormula SyntacticSugar (String, LSort) Name SapicLVar -> d
prettySyntacticSapicFormula = prettySyntacticLNFormula . toLFormula

