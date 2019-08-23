{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation rules common for different translation types in SAPIC
module Sapic.ProgressTranslation (
     progressTrans
   , progressTransNull
   , progressTransAct
   , progressTransComb
   , progressInit
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
import Control.Monad.Catch
import Theory
import Theory.Sapic
-- import Theory.Sapic.Print
-- import Sapic.Exceptions
import Sapic.Facts
-- import Sapic.Annotation
-- import Theory.Model.Rule
import Data.Typeable
import Data.Set            hiding (map)
import Sapic.ProgressFunction
-- import Control.Monad.Trans.FastFresh


addProgressFrom :: Set [Int] -> [Int]
                    -> ([TransFact], [TransAction], [TransFact])
                    -> ([TransFact], [TransAction], [TransFact])
addProgressFrom domPF child (l,a,r)
             | any isNonSemiState r
             , child `member` domPF =
                     (Fr(varProgress child):l
                     , ProgressFrom child:a
                     , map (addVarToState $ varProgress child) r)
             | otherwise = (l,a,r)

progressInit :: (MonadCatch m, Show ann1, Typeable ann1)
                => AnProcess ann1 -> ([AnnotatedRule ann2], Set LVar) -> m ([AnnotatedRule ann2], Set LVar)
progressInit anP (initrules,initTx) = do
    domPF <- pfFrom anP
    -- invPF <- pfInv anP
    return (initrules' domPF, initTx' domPF `union` initTx)
    where
          initTx' domPF = if [] `member` domPF then singleton $ varProgress [] else empty
          initrules' domPF =  map (mapAct $ addProgressFrom domPF []) initrules

extendVars :: Set ProcessPosition -> [Int] -> Set LVar -> Set LVar
extendVars domPF pos tx
    | lhsP pos `member` domPF =  varProgress (lhsP pos) `insert` tx
    | otherwise = tx

addProgressItems :: Set [Int]
                       -> ([Int] -> Maybe ProcessPosition)
                       -> [Int]
                       -> ([TransFact], [TransAction], [TransFact])
                       -> ([TransFact], [TransAction], [TransFact])
addProgressItems domPF invPF pos =addProgressFrom domPF (lhsP pos) -- can only start from ! or in, which have no rhs position
                                  . addProgressTo invPF (lhsP pos)
                                  . addProgressTo invPF (rhsP pos)

-- corresponds to step2 (child[12] p) in Firsttranslation.ml if
-- one of the direct childen of anrule is in the range of the pf
-- it has an inverse. We thus add ProgressTo to each such rule
-- that has the *old* state in the premise (we don't want to move
-- into Semistates too early). ProgressTo is annotated with the
-- inverse of the child's position, for verification speedup.
addProgressTo :: Foldable t =>
                 ([Int] -> Maybe ProcessPosition)
                 -> [Int]
                 -> (t TransFact, [TransAction], c)
                 -> (t TransFact, [TransAction], c)
addProgressTo invPF child (l,a,r) 
  | any isState l
  , (Just posFrom) <- invPF child = (l,ProgressTo child posFrom:a,r)
  | otherwise                     = (l,a,r)


progressTransNull :: p1 -> p2 -> p2
progressTransNull _ tNull = tNull

progressTransAct :: (MonadCatch m, Show ann, Typeable ann) =>
                    AnProcess ann
                    -> (t1
                        -> t2
                        -> [Int]
                        -> t3
                        -> m ([([TransFact], [TransAction], [TransFact])], Set LVar))
                    -> t1
                    -> t2
                    -> [Int]
                    -> t3
                    -> m ([([TransFact], [TransAction], [TransFact])], Set LVar)
progressTransAct anP tAct ac an pos tx = do 
                (rs0,tx1) <- tAct ac an pos tx 
                domPF <- pfFrom anP
                invPF <- pfInv anP
                return (map (addProgressItems domPF invPF pos) rs0,extendVars domPF pos tx1)

progressTransComb :: (MonadCatch m, Show ann, Typeable ann) =>
                     AnProcess ann
                     -> (t1
                         -> t2
                         -> [Int]
                         -> t3
                         -> m ([([TransFact], [TransAction], [TransFact])], Set LVar,
                               Set LVar))
                     -> t1
                     -> t2
                     -> [Int]
                     -> t3
                     -> m ([([TransFact], [TransAction], [TransFact])], Set LVar,
                           Set LVar)
progressTransComb anP tComb comb an pos tx =  do
                (rs0,tx1,tx2) <- tComb comb an pos tx
                domPF <- pfFrom anP
                invPF <- pfInv anP
                return (map (addProgressItems domPF invPF pos) rs0
                       ,extendVars domPF pos tx1
                       ,extendVars domPF pos tx2)

progressTrans :: (Show ann, Typeable ann, MonadCatch m1,
                  MonadCatch m2) =>
                 AnProcess ann
                 -> (a,
                     t4
                     -> t5
                     -> [Int]
                     -> t6
                     -> m1 ([([TransFact], [TransAction], [TransFact])], Set LVar),
                     t7
                     -> t8
                     -> [Int]
                     -> t9
                     -> m2 ([([TransFact], [TransAction], [TransFact])], Set LVar,
                            Set LVar))
                 -> (a,
                     t4
                     -> t5
                     -> [Int]
                     -> t6
                     -> m1 ([([TransFact], [TransAction], [TransFact])], Set LVar),
                     t7
                     -> t8
                     -> [Int]
                     -> t9
                     -> m2 ([([TransFact], [TransAction], [TransFact])], Set LVar,
                            Set LVar))
progressTrans anP (tN,tA,tC) = ( progressTransNull anP tN
                               , progressTransAct anP tA
                               , progressTransComb anP tC)
