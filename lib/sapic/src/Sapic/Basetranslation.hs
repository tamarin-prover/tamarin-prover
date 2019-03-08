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
import Sapic.Exceptions
import Sapic.Facts
import Sapic.Annotation
-- import Theory.Model.Rule
-- import Data.Typeable
import Data.Set            
-- import Control.Monad.Trans.FastFresh

--- TODO rewrite
--  should output rule and new tilde x

baseTrans = (baseTransNull, baseTransAction, baseTransComb)


baseTransNull :: p -> ProcessPosition -> Set LVar -> [([TransFact], [a1], [a2])]
baseTransNull _ p tildex =  [([State LState p tildex ], [], [])] 

baseTransAction ac _ p tildex 
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
    -- | Lock SapicTerm 
    -- | Unlock SapicTerm 
    -- | Event LNFact 
--   | Event(a) -> [([State(p,tildex)], [(* EventEmpty;*) a], [State(1::p,tildex)])]
    -- | MSR ([LNFact], [LNFact], [LNFact])
    | otherwise = throw ((NotImplementedError "baseTransAction") :: SapicException AnnotatedProcess)
    where
        def_state = State LState p tildex
        def_state' tx = State LState (p++[1]) tx
        freeset = fromList . frees
    

-- baseTrans_action 

-- let basetrans act p tildex = match act with
--   | MSR(prems,acts,concls) ->
--     let tildex' = tildex @@ (vars_factlist prems)  @@ (vars_factlist concls) in
--     [ ( State(p,tildex):: prems, (* EventEmpty::*)acts, State(1::p,tildex')::concls ) ]
--   | AnnotatedUnlock(t,a)  ->
--     let str = "lock"^(string_of_int a) in
--     let unlock_str = "Unlock_"^(string_of_int a) in
--     let nonce=a in
--     [([ State(p,tildex)], [Action("Unlock",[Var (Pub (string_of_int nonce));  Var (Fresh str); t ]); Action(unlock_str,[Var (Pub (string_of_int nonce));  Var (Fresh str); t ])], [State(1::p, tildex) ])] 
--   | AnnotatedLock(t,a)  ->
--     let str = "lock"^(string_of_int a) in
--     let lock_str = "Lock_"^(string_of_int a) in
--     let nonce=(Fresh str) in
--     [([ State(p,tildex); Fr(nonce)], [Action("Lock",[Var (Pub (string_of_int a)); Var (nonce); t ]);Action(lock_str,[Var (Pub (string_of_int a)); Var (nonce); t ])], [State(1::p, nonce @:: tildex)])]
--   | Lock(_) | Unlock(_) -> raise (UnAnnotatedLock ("There is an unannotated lock (or unlock) in the proces description, at position:"^pos2string p))
--   | Let(s) -> raise (TranslationError "'Let' should not be present at this point")
--   | Comment(s) -> raise (TranslationError "Comments should not be present at this point")

baseTransComb :: ProcessCombinator -> p -> ProcessPosition -> Set LVar
    -> ([([TransFact], [TransAction], [TransFact])], Set LVar, Set LVar)
baseTransComb c _ p tildex 
    | Parallel <- c = (
               [([def_state], [], [def_state1 tildex,def_state2 tildex])]
             , tildex, tildex )
    | NDC <- c = (
               []
             , tildex, tildex )
    | Cond f <- c = 
                let vars_f = fromList $ getFactVariables f in
                if vars_f `isSubsetOf` tildex then 
                (
       [ ([def_state], [Predicate f], [def_state1 tildex]),
         ([def_state], [NegPredicate f], [def_state2 tildex])]
             , tildex, tildex )
                else 
                    throw $ 
                    -- TODO Catch and add substitute process in calling function.
                    ( ProcessNotWellformed $ WFUnboundProto (vars_f `difference` tildex) 
                        :: SapicException AnnotatedProcess)
    | CondEq _ _ <- c = throw (ImplementationError "Cond node should contain Action constructor" :: SapicException AnnotatedProcess) 
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

