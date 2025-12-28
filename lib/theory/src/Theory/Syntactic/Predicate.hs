{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Theory.Syntactic.Predicate
    (
        Predicate(..)
      , mkPredicate
      , smallerFact
      , builtinPredicates
    ,lookupPredicate,expandFormula)
where

import Optics.TH
import Theory.Model
import qualified Data.Set as S
import GHC.Generics
import Control.DeepSeq
import Data.Binary
import Data.List
import Data.Char (toUpper)

------------------------------------------------------------------------------
-- Predicates
------------------------------------------------------------------------------

data Predicate = Predicate
        { fact            :: Fact LVar
        , formula         :: LNFormula
        }
        deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | smart constructor for predicates. makes sure names are capitalized
mkPredicate name formula = Predicate fact formula
    where
        fact = protoFact Linear (capitalize name) (frees formula)
        capitalize (head:tail) = toUpper head : tail
        capitalize [] = []

-- generate accessors for Predicate data structure records

makeFieldLabelsNoPrefix ''Predicate


smallerFact :: t -> t -> Fact t
smallerFact t1 t2 =
  Fact
    { factTag = ProtoFact Linear "Smaller" 2,
      factAnnotations = S.empty,
      factTerms = [t1, t2]
    }

builtinPredicates :: [Predicate]
builtinPredicates = [
  Predicate
    (smallerFact x y)
    (hinted exists z
     (Ato $
      EqE (bvt y) (
      fAppUnion (fvt x, fvt z)
      )
    ))
  ]
  where
     x = LVar "x" LSortMsg 0
     y = LVar "y" LSortMsg 0
     z = LVar "z" LSortMsg 0
     bvt = varTerm . Free
     fvt = varTerm . Free

-- | Find the predicate with the fact name in a list
lookupPredicate :: Fact t -> [Predicate] -> Maybe Predicate
lookupPredicate fact = find (sameName fact . (.fact)) . (++ builtinPredicates)
    where
        sameName (Fact tag _ _) (Fact tag' _ _) = tag == tag'

expandFormula :: [Predicate] -> ProtoFormula SyntacticSugar (String, LSort) Name LVar -> Either FactTag (ProtoFormula Unit2 (String, LSort) Name LVar)
expandFormula plist = traverseFormulaAtom f
  where
        f:: SyntacticAtom (VTerm Name (BVar LVar)) -> Either FactTag LNFormula
        f x | Syntactic (Pred fa)   <- x
            , Just pr <- lookupPredicate fa plist
              = return $ apply' (compSubst pr.fact fa) pr.formula

            | (Syntactic (Pred fa))   <- x
            , Nothing <- lookupPredicate fa plist = Left fa.factTag

            | otherwise = return $ Ato $ toAtom x
        apply' :: (Integer -> Subst Name (BVar LVar)) -> LNFormula -> LNFormula
        apply' subst = mapAtoms (\i a -> fmap (applyVTerm $ subst i) a)
        compSubst (Fact _ _ ts1) (Fact _ _ ts2) i = substFromList $ zip ts1' ts2'
        -- ts1 varTerms that are free in the predicate definition
        -- ts2 terms used in reference, need to add the number of quantifiers we added
        -- to correctly dereference.
            where
                  ts1':: [BVar LVar]
                  ts1' = map Free ts1
                  ts2' = map (fmap $ fmap up) ts2
                  up (Free v) = Free v
                  up (Bound i') = Bound $ i' + i
