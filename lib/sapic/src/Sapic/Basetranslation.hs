{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation rules common for different translation types in SAPIC
module Sapic.Basetranslation (
     baseTransNull
   , baseTransComb
   , baseTransAction
   , baseTrans
   , baseInit
) where
-- import Data.Maybe
-- import Data.Foldable
import Control.Exception
-- import Control.Monad.Fresh
import Control.Monad.Catch
import Theory
import Theory.Sapic
import Theory.Sapic.Print
import Sapic.Exceptions
import Sapic.Facts
import Sapic.Annotation
-- import Theory.Model.Rule
-- import Data.Typeable
import Data.Set            hiding (map)
-- import Control.Monad.Trans.FastFresh

-- | The basetranslation has three functions, one for translating the Null
-- Process, one for actions (i.e. constructs with only one child process) and
-- one for combinators (i.e., constructs with two child processes).
baseTrans :: MonadThrow m =>
                          (p
                          -> ProcessPosition -> Set LVar -> m [([TransFact], [a1], [a2])],
                          SapicAction
                          -> ProcessAnnotation
                          -> [Int]
                          -> Set LVar
                          -> m ([([TransFact], [TransAction], [TransFact])], Set LVar),
                          ProcessCombinator
                          -> p1
                          -> ProcessPosition
                          -> Set LVar
                          -> m ([([TransFact], [TransAction], [TransFact])], Set LVar,
                                 Set LVar))
baseTrans = (\ a p tx ->  return $ baseTransNull a p tx,
             \ ac an p tx -> return $ baseTransAction ac an p tx,
             \ comb an p tx -> return $ baseTransComb comb an p tx) -- I am sure there is nice notation for that.

--  | Each part of the translation outputs a set of multiset rewrite rules,
--    and ~x (tildex), the set of variables hitherto bound
baseTransNull :: p -> ProcessPosition -> Set LVar -> [([TransFact], [a1], [a2])]
baseTransNull _ p tildex =  [([State LState p tildex ], [], [])]

baseTransAction :: SapicAction
                             -> ProcessAnnotation
                             -> [Int]
                             -> Set LVar
                             -> ([([TransFact], [TransAction], [TransFact])], Set LVar)
baseTransAction ac an p tildex
    |  Rep <- ac = ([
          ([def_state], [], [State PSemiState (p++[1]) tildex ]),
          ([State PSemiState (p++[1]) tildex], [], [def_state' tildex])
          ], tildex)
    | (New v) <- ac = let tx' = v `insert` tildex in
        ([ ([def_state, Fr v], [], [def_state' tx']) ], tx')
    | (ChIn (Just tc) t) <- ac, (Just (AnLVar _)) <- secretChannel an =
          let tx' = (freeset tc) `union` (freeset t) `union` tildex in
          ([
          ([def_state, Message tc t], [], [Ack tc t, def_state' tx'])], tx')
    | (ChIn (Just tc) t) <- ac, Nothing <- secretChannel an =
          let tx' = (freeset tc) `union` (freeset t) `union` tildex in
          let ts  = fAppPair (tc,t) in
          ([
          ([def_state, In ts], [ ChannelIn ts], [def_state' tx']),
          ([def_state, Message tc t], [], [Ack tc t, def_state' tx'])], tx')
    | (ChIn Nothing t) <- ac =
          let tx' = freeset t `union` tildex in
          ([ ([def_state, (In t) ], [ ], [def_state' tx']) ], tx')
    | (ChOut (Just tc) t) <- ac, (Just (AnLVar _)) <- secretChannel an =
          let semistate = State LSemiState (p++[1]) tildex in
          ([
          ([def_state], [], [Message tc t,semistate]),
          ([semistate, Ack tc t], [], [def_state' tildex])], tildex)
    | (ChOut (Just tc) t) <- ac, Nothing <- secretChannel an =
          let semistate = State LSemiState (p++[1]) tildex in
          ([
          ([def_state, In tc], [ ChannelIn tc], [Out t, def_state' tildex]),
          ([def_state], [], [Message tc t,semistate]),
          ([semistate, Ack tc t], [], [def_state' tildex])], tildex)
    | (ChOut Nothing t) <- ac =
          ([
          ([def_state], [], [def_state' tildex, Out t])], tildex)
    | (Insert t1 t2 ) <- ac =
          ([
          ([def_state], [InsertA t1 t2], [def_state' tildex])], tildex)
    | (Delete t ) <- ac =
          ([
          ([def_state], [DeleteA t ], [def_state' tildex])], tildex)
    | (Lock t ) <- ac, (Just (AnLVar v)) <- lock an =
          let tx' = v `insert` tildex in
      ([
      ([def_state, Fr v], [LockNamed t v, LockUnnamed t v ], [def_state' tx'])], tx')
    | (Lock _ ) <- ac, Nothing <- lock an = throw (NotImplementedError "Unannotated lock" :: SapicException AnnotatedProcess)

    | (Unlock t ) <- ac, (Just (AnLVar v)) <- unlock an =
          ([([def_state], [UnlockNamed t v, UnlockUnnamed t v ], [def_state' tildex])], tildex)
    | (Unlock _ ) <- ac, Nothing <- lock an = throw ( NotImplementedError "Unannotated unlock" :: SapicException AnnotatedProcess)
    | (Event f ) <- ac =
          ([([def_state], [TamarinAct f], [def_state' tildex])], tildex)
    | (MSR (l,a,r)) <- ac =
          let tx' = (freeset' r) `union` tildex in
          ([(def_state:map TamarinFact l, map TamarinAct a, def_state' tx':map TamarinFact r)], tx')
    | otherwise = throw ((NotImplementedError $ "baseTransAction:" ++ prettySapicAction ac) :: SapicException AnnotatedProcess)
    where
        def_state = State LState p tildex -- default state when entering
        def_state' tx = State LState (p++[1]) tx -- default follow upstate, possibly with new bound variables
        freeset = fromList . frees
        freeset' = fromList . concatMap getFactVariables


-- | The translation for combinators expects:
--      c - the combinator
--      _ - annotations (for future use, currently ignored)
--      p - the current position
--      tildex - the logical variables bound up to here
--   It outputs
--      a set of mrs
--      the set of bound variables for the lhs process
--      the set of bound variables for the rhs process
baseTransComb :: ProcessCombinator -> p -> ProcessPosition -> Set LVar
    -> ([([TransFact], [TransAction], [TransFact])], Set LVar, Set LVar)
baseTransComb c _ p tildex
    | Parallel <- c = (
               [([def_state], [], [def_state1 tildex,def_state2 tildex])]
             , tildex, tildex )
    | NDC <- c = (
               []
             , tildex, tildex )
    | Cond f <- c = condition f
    | CondEq t1 t2 <- c = condition (protoFact Linear "Eq" [t1,t2])
    | Lookup t v <- c =
           let tx' = v `insert` tildex in
                (
       [ ([def_state], [IsIn t v], [def_state1 tx' ]),
         ([def_state], [IsNotSet t], [def_state2 tildex])]
             , tx', tildex )
    | otherwise = throw ((NotImplementedError "baseTransComb"):: SapicException AnnotatedProcess)
    where
        def_state = State LState p tildex
        def_state1 tx = State LState (p++[1]) tx
        def_state2 tx = State LState (p++[2]) tx
        condition f =
                let vars_f = fromList $ getFactVariables f in
                if vars_f `isSubsetOf` tildex then
                ( [ ([def_state], [PredicateA f], [def_state1 tildex]),
                    ([def_state], [NegPredicateA f], [def_state2 tildex])]
                     , tildex, tildex )
                else
                    throw $
                    ( ProcessNotWellformed $ WFUnboundProto (vars_f `difference` tildex)
                        :: SapicException AnnotatedProcess)

-- | @baseInit@ provides the initial rule that is used to create the first
-- linear statefact. An additional restriction on InitEmpty makes sure it can
-- only be used once.
baseInit :: AnProcess ann -> ([AnnotatedRule ann], Set a)
baseInit anP = ([AnnotatedRule (Just "Init") anP (Right InitPosition) l a r 0],empty)
  where
        l = []
        a = [InitEmpty ]
        r = [State LState [] empty]

