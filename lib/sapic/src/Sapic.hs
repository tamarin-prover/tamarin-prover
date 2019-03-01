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
import Control.Monad.Catch
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Theory.Model.Rule
import Data.Typeable
import Control.Monad.Trans.FastFresh

data ProcessAnnotation = ProcessAnnotation {
    processnames :: [String]
  , lock :: Maybe LVar 
  , unlock :: Maybe LVar  } deriving (Show, Typeable,Monoid)

instance Semigroup (LVar) where  -- override annotations if necessary
    (<>) a b = b
deriving instance Semigroup (ProcessAnnotation)

newtype AnnotatedProcess = AnProcess ProcessAnnotation
    deriving (Typeable, Monoid,Semigroup)

-- instance Monoid ProcessAnnotation where
--     mempty = ProcessAnnotation { processnames = [], lock = Nothing, unlock = Nothing }
--     mappend a b = ProcessAnnotation {
--                    processnames = (processnames a) `mappend` (processnames b)
--                 ,  lock = (lock a) `mappend` (lock b)
--                 ,  unlock = (unlock a) `mappend` (unlock b)
--     }

-- deriving instance (Monoid a,Semigroup a) => Monoid (AnProcess a)
deriving instance (Monad m, Monoid m') => Semigroup (FreshT m m')
deriving instance (Monad m, Monoid m') => Monoid (FreshT m m')

annLock :: LVar -> ProcessAnnotation
annLock v = ProcessAnnotation { processnames = [], lock = Just v, unlock = Nothing }
annUnlock :: LVar -> ProcessAnnotation
annUnlock v = ProcessAnnotation { processnames = [], lock = Nothing, unlock = Just v }


instance Functor (AnProcess) where
    fmap f (ProcessNull an) = (ProcessNull (f an))
    fmap f (ProcessComb c an pl pr)  = (ProcessComb c (f an) (fmap f pl) (fmap f pr))
    fmap f (ProcessAction a an p)   =  (ProcessAction a (f an) (fmap f p))


toAnProcess :: Process -> AnProcess ProcessAnnotation
toAnProcess = fmap f
    where
        f l = ProcessAnnotation { processnames = l, lock = Nothing, unlock = Nothing }

translate :: (Monad m, MonadThrow m) =>
             Monoid (m (AnProcess ProcessAnnotation)) => 
             OpenTheory
             -> m (OpenTheory)
translate th = case theoryProcesses th of
      [] -> return th
      [p] -> do 
            an_proc <- evalFreshT (annotateLocks (toAnProcess p)) 0
            th' <- liftedAddProtoRule th testrule
            return th'
      _ -> throw (SomethingBad :: SapicException AnnotatedProcess)
  where
    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> throwM (SomethingBad :: SapicException AnnotatedProcess)
        -- fail $ "duplicate rule: " -- ++ render (prettyRuleName ru)
    testrule = Rule (ProtoRuleEInfo (StandRule "lol") [])  [] [] [] []


  -- let msr =  
  --     if input.op.progress 
  --     then progresstrans annotated_process
  --     else noprogresstrans annotated_process 
  -- and lemmas_tamarin = print_lemmas input.lem
  -- and predicate_restrictions = print_predicates input.pred
  -- and sapic_restrictions = print_lemmas (generate_sapic_restrictions input.op annotated_process)
  -- in
  -- let msr' = if Lemma.contains_control input.lem (* equivalent to op.accountability *)
  --            then annotate_eventId msr 
  --            else msr
  -- in
  -- input.sign ^ ( print_msr msr' ) ^ sapic_restrictions ^
  -- predicate_restrictions ^ lemmas_tamarin 
  -- ^ "end"


newtype LocalException = LocalException WFLockTag deriving (Show)
instance Exception LocalException

annotateEachClosestUnlock :: MonadThrow m => 
                            Theory.Sapic.SapicTerm
                             -> LVar
                             -> AnProcess ProcessAnnotation
                             -> m( AnProcess ProcessAnnotation)
annotateEachClosestUnlock t v (ProcessNull a') = return $ ProcessNull a'
annotateEachClosestUnlock t v (ProcessAction (Unlock t') a' p) = 
            if t == t' then -- TODO do we need more precise equality? test this
                return $ ProcessAction (Unlock t') (a' `mappend` annUnlock v) p
            else do
                p' <- annotateEachClosestUnlock t v p
                return $ProcessAction (Unlock t') a' p'
annotateEachClosestUnlock t v (ProcessAction Rep a' p) = throwM $ LocalException WFRep
annotateEachClosestUnlock t a (ProcessComb Parallel a' pl pr ) = throwM $ LocalException WFPar
annotateEachClosestUnlock t v (ProcessAction ac a' p) = do p' <- annotateEachClosestUnlock t v p
                                                           return $ ProcessAction ac a' p'
annotateEachClosestUnlock t v (ProcessComb c a' pl pr ) = do pl' <- annotateEachClosestUnlock t v pl
                                                             pr' <- annotateEachClosestUnlock t v pr
                                                             return $ ProcessComb c a' pl' pr'

-- annotateLocks :: MonadFresh m =>
--                  Monoid (FreshT m (AnProcess ProcessAnnotation)) => 
--                  MonadThrow m =>
                    -- AnProcess ProcessAnnotation -> (FreshT m (AnProcess ProcessAnnotation))
annotateLocks :: ( MonadThrow m
                 , Monoid (m (AnProcess ProcessAnnotation))
                -- , MonadFresh m'
                -- , Monoid (m' (m (AnProcess ProcessAnnotation))))
                )
                    => AnProcess ProcessAnnotation -> (FreshT m (AnProcess ProcessAnnotation))
annotateLocks = pfoldMap f 
    where
        f (ProcessAction (Lock t) a p) = do 
            v <- freshLVar "lock" LSortMsg
            -- v <- LVar ("lock") LSortMsg -- TODO make sure that names are fresh here. Checkout our MonadFresh, but requires us to
            -- p'  <-  p
            -- return (ProcessAction (Lock t) (a `paddAnn` a') p')
            -- case annotateEachClosestUnlock t v p of
            --     Right p' -> return (ProcessAction (Lock t) (a `mappend` annLock v) p' ) 
            --     Left tag -> throw (ProcessNotWellformed $ WFLock tag p)
            p' <- annotateEachClosestUnlock t v p
            return (ProcessAction (Lock t) (a `mappend` annLock v) p')
        f p = return p
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

