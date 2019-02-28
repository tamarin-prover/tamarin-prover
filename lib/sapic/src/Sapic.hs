{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Theories with Processes to mrs

module Sapic (
    translate
) where
import Data.Maybe
import Data.Foldable
import Control.Exception
import Control.Monad.Fresh
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Theory.Model.Rule

data ProcessAnnotation = ProcessAnnotation {
    processnames :: [String]
  , lock :: Maybe LVar 
  , unlock :: Maybe LVar  } deriving (Show)

-- instance Monoid (Maybe a) where
--     mempty = Nothing
--     mappend Nothing Nothing  = Nothing
--     mappend Nothing (Just v) =  Just v
--     mappend (Just v) Nothing  =  Just v
--     mappend (Just v) (Just v')  =  Just v'

instance Semigroup (LVar) where  -- override annotations if necessary
    (<>) a b = b
deriving instance Semigroup (ProcessAnnotation)

instance Monoid ProcessAnnotation where
    mempty = ProcessAnnotation { processnames = [], lock = Nothing, unlock = Nothing }
    mappend a b = ProcessAnnotation {
                   processnames = (processnames a) `mappend` (processnames b)
                ,  lock = (lock a) `mappend` (lock b)
                ,  unlock = (unlock a) `mappend` (unlock b)
    }

annLock v = ProcessAnnotation { processnames = [], lock = Just v, unlock = Nothing }
annUnlock v = ProcessAnnotation { processnames = [], lock = Nothing, unlock = Just v }


instance Functor (AnProcess) where
    fmap f (ProcessNull an) = (ProcessNull (f an))
    fmap f (ProcessComb c an pl pr)  = (ProcessComb c (f an) (fmap f pl) (fmap f pr))
    fmap f (ProcessAction a an p)   =  (ProcessAction a (f an) (fmap f p))


toAnProcess :: Process -> AnProcess ProcessAnnotation
toAnProcess = fmap f
    where
        f l = ProcessAnnotation { processnames = l, lock = Nothing, unlock = Nothing }


translate th = case theoryProcesses th of
      [] -> return th
      [p] -> do 
            -- p' <- toAnProcess p
            -- an_proc <- annotate_locks p
            th' <- liftedAddProtoRule th testrule
            return th'
      _ -> throw SomethingBad
  where
    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate rule: " -- ++ render (prettyRuleName ru)
    testrule = Rule (ProtoRuleEInfo (StandRule "lol") [])  [] [] [] []


-- let translation input =
--   let annotated_process = annotate_locks ( sapic_tree2annotatedtree input.proc) in
--   let msr =  
--       if input.op.progress 
--       then progresstrans annotated_process
--       else noprogresstrans annotated_process 
--   and lemmas_tamarin = print_lemmas input.lem
--   and predicate_restrictions = print_predicates input.pred
--   and sapic_restrictions = print_lemmas (generate_sapic_restrictions input.op annotated_process)
--   in
--   let msr' = if Lemma.contains_control input.lem (* equivalent to op.accountability *)
--              then annotate_eventId msr 
--              else msr
--   in
--   input.sign ^ ( print_msr msr' ) ^ sapic_restrictions ^
--   predicate_restrictions ^ lemmas_tamarin 

annotateEachClosestUnlock t v (ProcessNull a') = (ProcessNull a')
annotateEachClosestUnlock t v (ProcessAction (Unlock t') a' p) = 
            if t == t' then -- TODO do we need more precide equality? test this
                ProcessAction (Unlock t') (a' `mappend` annUnlock (v)) p
            else 
                (ProcessAction (Unlock t') a' (f p))
    where f = annotateEachClosestUnlock t v
-- annotateEachClosestUnlock t a (ProcessAction Rep a' p) = ..
annotateEachClosestUnlock t v (ProcessAction ac a' p) = (ProcessAction ac a' (f p))
    where f = annotateEachClosestUnlock t v
-- annotateEachClosestUnlock t a (ProcessComb Parallel a' pl pr ) = 
annotateEachClosestUnlock t v (ProcessComb c a' pl pr ) = (ProcessComb c a' (f pl) (f pr))
    where f = annotateEachClosestUnlock t v

--  match tree with  
--     Empty -> Empty
--   | Node(Unlock(t'),l,r) ->
--           if Term.compare t t' = 0 
--           then (* same term including strings inside variable names *)
--               Node(AnnotatedUnlock(t,annotation),l,r)
--           else 
--              Node(Unlock(t'),(annotateEachClosestUnlock t annotation l),
--                     (annotateEachClosestUnlock t annotation r))
--   | Node(Rep,l,r) -> raise ( ProcessNotWellformed "Replication underneath lock")
--   | Node(Par,l,r) -> raise (ProcessNotWellformed "Parallel underneath lock")
--   | Node(y,l,r) -> Node(y,(annotateEachClosestUnlock t annotation l),
--                          (annotateEachClosestUnlock t annotation r))
-- and 
--       max a b = if a> b then a else b

annotateLocks :: MonadFresh m => Monoid (m (AnProcess ProcessAnnotation)) => AnProcess ProcessAnnotation -> m (AnProcess ProcessAnnotation)
annotateLocks = pfoldMap f 
    where
        f (ProcessAction (Lock t) a p) = do 
                                            v <- freshLVar "lock" LSortMsg
                                            -- p'  <-  p
                                            -- return (ProcessAction (Lock t) (a `paddAnn` a') p')
                                            return (ProcessAction (Lock t) (a `mappend` (annLock v)) (annotateEachClosestUnlock t v p)) 
        f p                            = return p
-- annotateLocks (ProcessAction (Lock t) a p) = do 
--                                             v <- freshLVar "lock" LSortMsg
--                                             -- p'  <-  p
--                                             -- return (ProcessAction (Lock t) (a `paddAnn` a') p')
--                                             return (ProcessAction (Lock t) (a `mappend` (annLock v)) (annotateEachClosestUnlock t v p)) 
-- annotateLocks (ProcessAction ac a p) = return (ProcessAction ac a (annotateLocks p))
-- annotateLocks (ProcessAction ac a p) = return (ProcessAction ac a (annotateLocks p))
    
    
-- in
-- let (result,_) = fold_bottom (fun (l,p_l) (r,p_r) a->
--              let p=(max p_l p_r)+1 in
--              let annotation= p (* Fresh("lock"^string_of_int p) *) in
--                match (a:annotated_sapic_action) with
--                 Lock(t) -> (Node(AnnotatedLock(t,annotation),
--                               annotateEachClosestUnlock t annotation l,
--                               annotateEachClosestUnlock t annotation r), p)
--                | _ -> (Node(a,l,r),p)
--     ) (Empty,0) (tree:annotated_btree)
--  in
--     result

