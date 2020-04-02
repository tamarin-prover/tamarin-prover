{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- |
-- Copyright   : (c) 2020 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert.kuennemann@cispa.saarland>
-- Portability : GHC only
--
-- Tools for transforming rule-level restrictions

module Theory.Model.Restriction (
    ProtoRestriction(..)
  , Restriction
  , SyntacticRestriction
  , RestrictionAttribute(..)
  , rstrName
  , rstrFormula
  , varNow
  , fromRuleRestriction
) where

import           Control.DeepSeq
import qualified Control.Monad.State           as State
import           Control.Monad.Trans.FastFresh (evalFreshT)
import           Extension.Data.Label          hiding (get)
import           GHC.Generics                  (Generic)
import           Prelude                       hiding (id)
-- import qualified Extension.Data.Label                as L
import qualified Data.List                     as L
import qualified Data.Map                      as M
import qualified Data.Set                      as S
import           Term.LTerm
-- import           Term.Unification
import           Term.Substitution
import           Data.Binary
import           Theory.Model.Atom
import           Theory.Model.Fact
import           Theory.Model.Formula

------------------------------------------------------------------------------
-- Restrictions (Trace filters)
------------------------------------------------------------------------------

-- | An attribute for a 'Restriction'.
data RestrictionAttribute = LHSRestriction
    | RHSRestriction
    | BothRestriction
    deriving (Eq, Ord, Show)

-- | A restriction describes a property that must hold for all traces. Restrictions are
-- always used as lemmas in proofs.
data ProtoRestriction f = Restriction
    { _rstrName    :: String
    , _rstrFormula :: f
    }
    deriving (Generic)

type Restriction = ProtoRestriction LNFormula
type SyntacticRestriction = ProtoRestriction SyntacticLNFormula

deriving instance Eq Restriction
deriving instance Ord Restriction
deriving instance Show Restriction
deriving instance NFData Restriction
deriving instance Binary Restriction

$(mkLabels [''ProtoRestriction])

------------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------------

-- | Used in liftedAddProtoRule to expand restriction, used in process
-- translation
varNow :: LVar
varNow = LVar "NOW" LSortNode 0

-- | rewrite f so all formulas with free variables are substituted by fresh
-- | free variables.  outputs modified formula and substitution
rewrite :: Traversable syn2 =>
           ProtoFormula syn2 s c2 LVar
           -> (ProtoFormula syn2 s c2 LVar,
               M.Map LVar (Term (Lit c2 LVar)))
rewrite f = State.runState (evalFreshT (traverseFormulaAtom fAt' f) 0 ) M.empty
    where
                fAt' atom = Ato <$> traverse fAt atom
                fAt t -- traverse into term and substitute all subterms
                   |  Lit (Var bv) <- viewTerm t , isFree bv   = substitute t
                   |  Lit (Var _ ) <- viewTerm t               = return t
                   |  FApp _ as    <- viewTerm t
                    , any containsFree as
                    , all (not . containsBound) as             = substitute t
                   |  FApp fs as    <- viewTerm t
                    , any containsFree as
                    , any containsBound as                     = do
                                as' <- traverse fAt as
                                return $ termViewToTerm $ FApp fs as'
                                    -- here we have a problem with reducible symbols
                   | otherwise                                 = return t
                   where
                    substitute t' = do
                                v <- freshLVar "x" LSortMsg
                                m <- State.get
                                let t'' =  fmap (fmap fromFree) t'
                                -- remove bvar
                                State.put (M.insert v t'' m)
                                return $ varTerm  $ Free v
                containsVar p t = case viewTerm t of
                    Lit (Var bv) -> p bv
                    Lit _        -> False
                    FApp _ as    -> any containsFree as
                containsFree  = containsVar isFree
                containsBound = containsVar (not . isFree)
                isFree (Bound _) = False
                isFree (Free  v) = if v == varNow then False
                                   else True

-- | From f, create restriction with rname and an action to insert in some protocol rule
fromRuleRestriction :: String -> LNFormula -> (Restriction, Fact LNTerm)
-- fromRuleRestriction :: (Apply (VTerm c LVar), Traversable syn2,
--                         HasFrees (ProtoFormula syn2 (String, LSort) Name LVar)) =>
--                        [Char]
--                        -> ProtoFormula syn2 (String, LSort) Name LVar
--                        -> (ProtoRestriction (ProtoFormula syn2 (String, LSort) Name LVar),
--                            Fact (VTerm c LVar))
fromRuleRestriction rname f =
                (mkRestriction,  mkFact (getVarTerms $ rewrSubst f) f)
            where
                --- canot handle predicates with reducible function symbols
                -- what we should do:
                -- 1. find those in f
                -- 2. substitute by variables
                -- 3. quantify over variables in restriction
                -- 3. in actions, create fact with these terms

                -- creates restriction with prefix "restr_"++rname and counter n
                -- and formula f quantified over free variables and varnow
                mkRestriction = Restriction
                                        ("restr_"++ rname)
                                        (foldr (hinted forall) f'' (frees' f'))
                                        where
                                            f'' = Ato (Action timepoint (facts f')) .==>. f'
                                            f' = rewrF f
                                            timepoint = varTerm $ Free varNow
                                            facts = mkFact getBVarTerms


                rewrF     = fst . rewrite -- rewritten formula
                rewrSubst = substFromMap . snd . rewrite -- rewritten formula
                frees' formula = frees formula `L.union` [varNow]
                getBVarTerms =  map (varTerm . Free) . L.delete varNow . frees
                getVarTerms subst =   map (varTerm . apply subst) . L.delete varNow . freesList
                mkFact  getTerms formula  =
                        protoFactAnn
                            Linear ("restr_"++ rname)
                            S.empty  -- no annotations
                            -- (getTerms formula) -- TODO apply substitution
                            ( (getTerms formula)) -- does not work need to get expanded formula
