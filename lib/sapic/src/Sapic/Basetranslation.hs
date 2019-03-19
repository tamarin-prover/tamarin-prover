{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- TODO
module Sapic.Basetranslation (
    baseTransNull
   ,baseTransComb
   ,baseTransAction
   , baseTrans
) where
-- import Data.Maybe
-- import Data.Foldable
import Control.Exception
-- import Control.Monad.Fresh
-- import Control.Monad.Catch
-- import Sapic.Exceptions
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

--- TODO rewrite
--  should output rule and new tilde x

baseTrans = (baseTransNull, baseTransAction, baseTransComb)


baseTransNull :: p -> ProcessPosition -> Set LVar -> [([TransFact], [a1], [a2])]
baseTransNull _ p tildex =  [([State LState p tildex ], [], [])] 

baseTransAction ac an p tildex 
    |  Rep <- ac = ([
          ([def_state], [], [State PSemiState (p++[1]) tildex ]),
          ([State PSemiState (p++[1]) tildex], [], [def_state' tildex])
          ], tildex)
    | (New v) <- ac = let tx' = v `insert` tildex in
        ([ ([def_state, Fr v], [], [def_state' tx']) ], tx')
    | (ChIn (Just tc) t) <- ac = 
          let tx' = (freeset tc) `union` (freeset t) `union` tildex in 
          let ts  = fAppPair (tc,t) in
          ([
          ([def_state, In ts], [ ChannelIn ts], [def_state' tx']),
          ([def_state, Message tc t], [], [Ack tc t, def_state' tx'])], tx')
    | (ChIn Nothing t) <- ac = 
          let tx' = freeset t `union` tildex in 
          ([ ([def_state, (In t) ], [ ], [def_state' tx']) ], tx')
    | (ChOut (Just tc) t) <- ac = 
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
        def_state = State LState p tildex
        def_state' tx = State LState (p++[1]) tx
        freeset = fromList . frees
        freeset' = fromList . concatMap getFactVariables
    

-- baseTrans_action 

-- let basetrans act p tildex = match act with
--   | MSR(prems,acts,concls) ->
--     let tildex' = tildex @@ (vars_factlist prems)  @@ (vars_factlist concls) in
--     [ ( State(p,tildex):: prems, (* EventEmpty::*)acts, State(1::p,tildex')::concls ) ]

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
                    -- TODO Catch and add substitute process in calling function.
                    ( ProcessNotWellformed $ WFUnboundProto (vars_f `difference` tildex) 
                        :: SapicException AnnotatedProcess)

