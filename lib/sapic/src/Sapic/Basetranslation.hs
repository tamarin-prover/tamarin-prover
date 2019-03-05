{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
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

baseTransNull :: p -> Position -> Set LVar -> [([TransFact], [a1], [a2])]
baseTransNull _ p tildex =  [([State LState p tildex ], [], [])] 

baseTransComb :: ProcessCombinator -> p -> Position -> Set LVar
    -> ([([TransFact], [TransAction], [TransFact])], Set LVar, Set LVar)
baseTransComb c _ p tildex 
    | Parallel <- c = (
               [([State LState p tildex], [], [State LState ( 1:p ) tildex,State LState ( 2:p ) tildex])]
             , tildex, tildex )
    | NDC <- c = (
               []
             , tildex, tildex )
    | Cond f <- c = 
                let vars_f = fromList $ getFactVariables f in
                if vars_f `isSubsetOf` tildex then 
                (
       [ ([State LState p tildex], [Predicate f], [State LState (1:p) tildex]),
         ([State LState p tildex ], [NegPredicate f], [State LState (2:p) tildex])]
             , tildex, tildex )
                else 
                    throw $ 
                    ( ProcessNotWellformed $ WFUnboundProto (vars_f `difference` tildex) -- TODO Catch and add substitute process in calling function.
 :: SapicException AnnotatedProcess)
    | CondEq _ _ <- c = throw (ImplementationError "Cond node should contain Action constructor" :: SapicException AnnotatedProcess) 
    | otherwise = throw (SomethingBad :: SapicException AnnotatedProcess)

-- data ProcessCombinator = Parallel | NDC | Cond LNFact 
--         | CondEq SapicTerm SapicTerm | Lookup SapicTerm LVar

baseTransAction ac _ p tildex 
    |  Rep <- ac = ([
          ([State LState p tildex], [], [State PSemiState (1:p) tildex ]),
          ([State PSemiState (1:p) tildex], [], [State LState ( 1:p ) tildex])
          ], tildex)
    | otherwise = throw (SomethingBad :: SapicException AnnotatedProcess)
    

-- baseTrans_action 

-- let basetrans act p tildex = match act with
--   | MSR(prems,acts,concls) ->
--     let tildex' = tildex @@ (vars_factlist prems)  @@ (vars_factlist concls) in
--     [ ( State(p,tildex):: prems, (* EventEmpty::*)acts, State(1::p,tildex')::concls ) ]
--   | New(v) -> [([State(p,tildex);Fr(v)], [], [State(1::p, v@::tildex)])]
--   | Msg_In(t) -> [([State(p,tildex);In(t)],[],[State(1::p,(vars_t t) @@ tildex)])]
--   | Msg_Out(t) -> [([State(p,tildex)],[],[State(1::p,(vars_t t) @@ tildex);Out(t)])]
--   | Ch_In(t1,t2) -> let tildex' = tildex @@ (vars_t t1) @@ (vars_t t2) in
--     [ ( [State(p,tildex);In(List([t1;t2]))], [Action("ChannelInEvent",[List([t1;t2])])], [State(1::p,tildex')]);
--       ( [State(p,tildex);Message(t1, t2)], [], [Ack(t1,t2);State(1::p,tildex')])]
--   | Ch_Out(t1,t2) -> [
--       ( [State(p,tildex);In(t1)], [Action("ChannelInEvent",[t1])], [Out(t2);State(1::p,tildex)]);
--       ( [State(p,tildex) ], [], [Semistate(p,tildex); Message(t1, t2)] );
--       ( [Semistate(p, tildex);Ack(t1,t2)], [], [State(1::p,tildex)])]
--   | Insert(t1,t2) -> [([State(p,tildex)], [Action("Insert",[t1 ; t2])], [State(1::p,tildex)])]
--   | Event(a) -> [([State(p,tildex)], [(* EventEmpty;*) a], [State(1::p,tildex)])]
--   | Lookup(t1,t2) -> 
--     [
--       ([State(p,tildex)], [Action("IsIn",[t1; t2])], [State(1::p, tildex @@ (vars_t t2))]);
--       ([State(p,tildex)], [Action("IsNotSet",[t1])], [State(2::p,tildex)]) ]
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
--   | Delete(t)  -> [
--       ( [ State(p,tildex)], [Action("Delete",[ t ])], [State(1::p, tildex) ])]
--   | Lock(_) | Unlock(_) -> raise (UnAnnotatedLock ("There is an unannotated lock (or unlock) in the proces description, at position:"^pos2string p))
--   | Let(s) -> raise (TranslationError "'Let' should not be present at this point")
--   | Comment(s) -> raise (TranslationError "Comments should not be present at this point")

