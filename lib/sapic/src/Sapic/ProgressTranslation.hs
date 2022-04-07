{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation rules for local progress: processes must reduce unless they are of form !P or in(..)
--
-- The theory behind this is quite involved, it is described in the following paper:
--
-- Michael Backes, Jannik Dreier, Steve Kremer and Robert Künnemann. "A Novel
-- Approach for Reasoning about Liveness in Cryptographic Protocols and its
-- Application to Fair Exchange". EuroS&P 2017 
--
module Sapic.ProgressTranslation (
     progressTrans
   , progressTransNull
   , progressTransAct
   , progressTransComb
   , progressInit
   , progressRestr
) where
import qualified Data.List              as List
import           Data.Set               hiding (map)
import           Data.Typeable
import qualified Text.RawString.QQ    as QQ
import           Control.Monad.Catch
import           Theory
import           Theory.Sapic
import           Sapic.Facts
import           Sapic.ProgressFunction
import           Sapic.Basetranslation

-- | Adds event @ProgressFrom@ to any rule with a state fact (not semi-state
-- fact) on the rhs, if the followup position (as marked in the state) is in
-- @domPF@, i.e., the domain of the progress function.
addProgressFrom :: Set [Int] -> [Int]
                    -> ([TransFact], [TransAction], [TransFact],a)
                    -> ([TransFact], [TransAction], [TransFact],a)
addProgressFrom domPF child (l,a,r,res)
             | any isNonSemiState r
             , child `member` domPF =
                     (Fr(varProgress child):l
                     , ProgressFrom child:a
                     , map (addVarToState $ varProgress child) r
                     , res)
             | otherwise = (l,a,r,res)

-- | Initial rules for progress: adds @ProgressFrom@ to the previous set of
-- init rules, if [] in @domPF@, the domain of the progress function. Updates
-- the initial ~x accordingly.
progressInit :: (MonadCatch m, Show ann1, Typeable ann1)
                => AnProcess ann1 -> ([AnnotatedRule ann2], Set LVar) -> m ([AnnotatedRule ann2], Set LVar)
progressInit anP (initrules,initTx) = do
    domPF <- pfFrom anP
    -- invPF <- pfInv anP
    return (initrules' domPF, initTx' domPF `union` initTx)
    where
          initTx' domPF = if [] `member` domPF then singleton $ varProgress [] else empty
          initrules' domPF =  map (mapAct $ addProgressFrom domPF []) initrules

-- | Helper function: add progress variable for @lhsP pos@ to @tx@ if if is in
-- the dom(progress function)
extendVars :: Set ProcessPosition -> [Int] -> Set LVar -> Set LVar
extendVars domPF pos tx
    | lhsP pos `member` domPF =  varProgress (lhsP pos) `insert` tx
    | otherwise = tx

-- | Add ProgressTo and ProgressFrom events to a rule: ProgressFrom for the
-- position itself, and ProgressTo for one of the children.
addProgressItems :: Set [Int]
                       -> ([Int] -> Maybe ProcessPosition)
                       -> [Int]
                       -> ([TransFact], [TransAction], [TransFact], a)
                       -> ([TransFact], [TransAction], [TransFact], a)
addProgressItems domPF invPF pos =addProgressFrom domPF (lhsP pos) -- can only start from ! or in, which have no rhs position
                                  . addProgressTo invPF (lhsP pos)
                                  . addProgressTo invPF (rhsP pos)

-- | Add ProgressTo events:
--   (corresponds to step2 (child[12] p) in Firsttranslation.ml)
-- If one of the direct childen of anrule is in the range of the pf it has an
-- inverse. We thus add ProgressTo to each such rule that has the *old* state in
-- the premise (we don't want to move into Semistates too early). ProgressTo is
-- annotated with the inverse of the child's position, for verification speedup.
-- addProgressTo :: Foldable t =>
--                  ([Int] -> Maybe ProcessPosition)
--                  -> [Int]
--                  -> ([] TransFact, [TransAction], c, d)
--                  -> (t TransFact, [TransAction], c,d )
addProgressTo :: Foldable t => ([Int] -> Maybe ProcessPosition) -> [Int] -> (a, [TransAction], t TransFact, d) -> (a, [TransAction], t TransFact, d)
addProgressTo invPF child (l,a,r,res) 
--   | any isState l
--   , (Just posFrom) <- invPF child = (l,ProgressTo child posFrom:a,r,res)
  | any isTargetState r
  , (Just posFrom) <- invPF child = (l,ProgressTo child posFrom:a,r,res)
  | otherwise                     = (l,a,r,res)
  where
      isTargetState (State kind nextPos _) = nextPos == child && (kind == PState || kind == LState)
      isTargetState _ = False



-- | Null Processes are translated without any modification
progressTransNull :: p1 -> p2 -> p2
progressTransNull _ tNull = tNull

-- | Add ProgressTo or -From to rules generated on an action.
progressTransAct :: (MonadCatch m, Show ann, Typeable ann) =>
                    AnProcess ann
                    -> TransFAct (m TranslationResultAct)
                    -> TransFAct (m TranslationResultAct)
progressTransAct anP tAct ac an pos tx = do 
                (rs0,tx1) <- tAct ac an pos tx 
                domPF <- pfFrom anP
                invPF <- pfInv anP
                return (map (addProgressItems domPF invPF pos) rs0,extendVars domPF pos tx1)

-- | Add ProgressTo or -From to rules generated on a combinator.
progressTransComb :: (MonadCatch m, Show ann, Typeable ann) =>
                     AnProcess ann
                    -> TransFComb (m TranslationResultComb)
                    -> TransFComb (m TranslationResultComb)
progressTransComb anP tComb comb an pos tx =  do
                (rs0,tx1,tx2) <- tComb comb an pos tx
                domPF <- pfFrom anP
                invPF <- pfInv anP
                return (map (addProgressItems domPF invPF pos) rs0
                       ,extendVars domPF pos tx1
                       ,extendVars domPF pos tx2)

-- | Overall translation is a triple of the other translations.
progressTrans :: (Show ann, Typeable ann, MonadCatch m2,
                  MonadCatch m3) =>
                 AnProcess ann
                 -> 
                          (TransFNull (m1 TranslationResultNull),
                           TransFAct (m2 TranslationResultAct),
                           TransFComb (m3 TranslationResultComb))
                 -> 
                          (TransFNull (m1 TranslationResultNull),
                           TransFAct (m2 TranslationResultAct),
                           TransFComb (m3 TranslationResultComb))
progressTrans anP (tN,tA,tC) = ( progressTransNull anP tN
                               , progressTransAct anP tA
                               , progressTransComb anP tC)

resProgressInit :: String
resProgressInit = [QQ.r|restriction progressInit: 
"Ex #t . Init()@t"
|]

-- | Add restrictions for all transitions that have to take place according to the progress function.
progressRestr :: (MonadThrow m, MonadCatch m, Show ann, Typeable ann) => AnProcess ann -> [SyntacticRestriction] -> m [SyntacticRestriction] 
progressRestr anP restrictions  = do
    domPF <- pfFrom anP -- set of "from" positions
    initL <- toEx resProgressInit
    lss_to <- mapM restriction (toList domPF) -- list of set of sets of "to" positions
    return $ restrictions ++ concat lss_to ++ [initL]
    where 
        restriction pos = do  -- produce restriction to go to one of the tos once pos is reached
            toss <- pf anP pos
            mapM (\tos -> return $ Restriction (name tos) (formula tos))  (toList toss)
            where
                name tos = "Progress_" ++ prettyPosition pos ++ "_to_" ++ List.intercalate "_or_" (map prettyPosition $ toList tos)
                formula tos = hinted forall pvar $ hinted forall t1var $ antecedent .==>. conclusion tos
                pvar = msgVarProgress pos
                t1var = LVar "t" LSortNode 1
                t2var = LVar "t" LSortNode 2
                antecedent = Ato $ Action (varTerm $ Free t1var) $ actionToFactFormula (ProgressFrom pos)
                conclusion tos = bigOr $ map progressTo $ toList tos
                bigOr [to] = to
                bigOr (to:tos) = to .||. bigOr tos 
                bigOr []   = TF False -- This case should never occur
                progressTo to = hinted exists t2var $ Ato $ Action (varTerm $ Free t2var) $ actionToFactFormula $ ProgressTo to pos
