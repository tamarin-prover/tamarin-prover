{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE PatternGuards        #-}
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

import           Prelude                             hiding (id)
import           GHC.Generics                        (Generic)
import qualified Control.Monad.State           as State
import           Control.Monad.Trans.FastFresh (evalFreshT)
import           Control.DeepSeq
import           Extension.Data.Label                hiding (get)
-- import qualified Extension.Data.Label                as L
import qualified Data.List                     as L
import qualified Data.Set                      as S
import qualified Data.Map                   as M
import           Term.LTerm
-- import           Term.Unification
import           Theory.Model.Atom
import           Theory.Model.Formula
import           Theory.Model.Fact
import           Data.Binary

------------------------------------------------------------------------------
-- Restrictions (Trace filters)
------------------------------------------------------------------------------

-- | An attribute for a 'Restriction'.
data RestrictionAttribute =
         LHSRestriction
       | RHSRestriction
       | BothRestriction
       deriving( Eq, Ord, Show )

-- | A restriction describes a property that must hold for all traces. Restrictions are
-- always used as lemmas in proofs.
data ProtoRestriction f = Restriction
       { _rstrName    :: String
       , _rstrFormula :: f
       }
       deriving( Generic )

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
-- free variables.  | output modified formula and substitution
-- rewrite :: Traversable syn2 =>
--            ProtoFormula syn2 s c2 LVar
--            -> (ProtoFormula syn2 s c2 LVar, M.Map LVar (VTerm c2 (BVar LVar)))
rewrite f = State.runState (evalFreshT (traverseFormulaAtom fAt' f) 0 ) M.empty
    where
                -- fAt' ::ProtoAtom syn1 (VTerm Name (BVar v1))
                --     -> State.StateT (Subst c v) Identity (ProtoFormula syn2 s c2 LNTerm)
                fAt' atom = Ato <$> traverse fAt atom
                -- fAt :: State.MonadState (Subst c v) m => LNTerm -> m LNTerm
                fAt t -- traverse into term and substitute all subterms 
                   |  Lit (Var bv) <- viewTerm t , isFree bv   = substitute t
                   |  Lit (Var bv) <- viewTerm t               = return t
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
                    substitute t = do
                                v <- freshLVar "par" LSortMsg
                                m <- State.get
                                State.put (M.insert v t m)
                                return $ varTerm  $ Free v
                -- (f,emptySubst)
                containsVar p t = case viewTerm t of
                    Lit (Var bv) -> p bv
                    Lit _               -> False
                    FApp _ as           -> any containsFree as 
                containsFree  = containsVar isFree
                containsBound = containsVar (not . isFree)
                isFree (Bound _) = False
                isFree (Free  _) = True


-- | From f, create restriction with rname and an action to insert in some protocol rule
-- fromRuleRestriction :: (Show a, HasFrees t) =>
--                        String
--                        -> p
--                        -> ((Int, LNFormula) -> Restriction, (a, t) -> Fact (VTerm c LVar))
fromRuleRestriction :: String -> LNFormula -> (Restriction, Fact (VTerm c LVar))
fromRuleRestriction rname f =
                (mkRestriction,  mkFact getVarTerms f)
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


                rewrF = fst . rewrite -- rewritten formula
                -- rewrSubst = snd . rewrite -- substitution

                frees' formula = frees formula `L.union` [varNow]

                getBVarTerms =  map (varTerm . Free) . L.delete varNow . frees
                getVarTerms =   map (varTerm) . frees 
                mkFact  getTerms formula  =
                        protoFactAnn 
                            Linear ("_rstr_"++ rname) 
                            S.empty  -- no annotations
                            (getTerms formula) -- TODO apply substitution
                            -- (apply (rewrSubst f) getTerms f) -- does not work need to get expanded formula
