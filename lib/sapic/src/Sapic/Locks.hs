-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- TODO
module Sapic.Locks (
    annotateLocks
) where
-- import Data.Maybe
-- import Data.Foldable
import Control.Exception
import Control.Monad.Fresh
import Control.Monad.Catch
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Sapic.Annotation
-- import Theory.Model.Rule
-- import Data.Typeable
-- import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh

newtype LocalException = LocalException WFLockTag deriving (Show)
instance Exception LocalException

annotateEachClosestUnlock :: MonadThrow m => 
                            Theory.Sapic.SapicTerm
                             -> AnLVar
                             -> AnProcess ProcessAnnotation
                             -> m( AnProcess ProcessAnnotation)
annotateEachClosestUnlock t v (ProcessNull a') = return $ ProcessNull a'
annotateEachClosestUnlock t v (ProcessAction (Unlock t') a' p) = 
            if t == t' then -- TODO do we need more precise equality? test this
                return $ ProcessAction (Unlock t') (a' `mappend` annUnlock v) p
            else do
                p' <- annotateEachClosestUnlock t v p
                return $ProcessAction (Unlock t') a' p'
annotateEachClosestUnlock t v (ProcessAction Rep _ _) = throwM $ LocalException WFRep
annotateEachClosestUnlock t a (ProcessComb Parallel _ _ _) = throwM $ LocalException WFPar
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
            p' <- annotateEachClosestUnlock t (AnLVar v) p
            return (ProcessAction (Lock t) (a `mappend` annLock (AnLVar v)) p')
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

