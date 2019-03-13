{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- TODO
module Sapic.Restrictions (
    generateSapicRestrictions
) where
-- import Data.Maybe
-- import Data.Foldable
import qualified  Data.Monoid as M
import Data.Maybe
import Control.Exception
import Control.Monad.Fresh
import Control.Monad.Catch
import qualified Data.Traversable as T
import qualified Extension.Data.Label                as L
import Sapic.Exceptions
import Theory 
import Theory.Sapic
import Theory.Text.Parser
import Sapic.Annotation
import Text.RawString.QQ
-- import Theory.Model.Rule
-- import Data.Typeable
-- import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh


toEx (Left  err) = throwM ( ImplementationError ( "Error parsing hard-coded restrictions: " ++ show err )::SapicException AnnotatedProcess)
toEx (Right res ) = return res

resSetIn = parseRestriction [r|restriction set_in: 
"All x y #t3 . IsIn(x,y)@t3 ==>  
(Ex #t2 . Insert(x,y)@t2 & #t2<#t3 
& ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 |  #t3<#t1))
& ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) 
)" |]

resSetNotIn = parseRestriction [r|restriction set_notin:
"All x #t3 . IsNotSet(x)@t3 ==> 
        (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )
  | ( Ex #t1 .   Delete(x)@t1 & #t1<#t3 *) 
                &  (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==>  #t2<#t1))"
|]

resSetInNoDelete = parseRestriction [r|restriction set_in: 
"All x y #t3 . IsIn(x,y)@t3 ==>  
(Ex #t2 . Insert(x,y)@t2 & #t2<#t3 
& ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) 
)" |]

resSetNotInNoDelete = parseRestriction [r|restriction set_notin:
"All x #t3 . IsNotSet(x)@t3 ==> 
(All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )"
|]

resLocking_l  = parseRestriction [r|restriction locking:
"All p pp l x lp #t1 #t3 . LockPOS(p,l,x)@t1 & Lock(pp,lp,x)@t3 
        ==> 
        ( #t1<#t3 
                 & (Ex #t2. UnlockPOS(p,l,x)@t2 & #t1<#t2 & #t2<#t3 
                 & (All #t0 pp  . Unlock(pp,l,x)@t0 ==> #t0=#t2) 
                 & (All pp lpp #t0 . Lock(pp,lpp,x)@t0 ==> #t0<#t1 | #t0=#t1 | #t2<#t0) 
                 & (All pp lpp #t0 . Unlock(pp,lpp,x)@t0 ==> #t0<#t1 | #t2<#t0 | #t2=#t0 )
                ))
        | #t3<#t1 | #t1=#t3"
|]
--- We hardcode the variable used in the lemma. Let $i be its index:
-- "All p pp l x lp #t1 #t3 . Lock_$i(p,l,x)@t1 & Lock(pp,lp,x)@t3 
--         ==> 
--         ( #t1<#t3 
--                  & (Ex #t2. Unlock_$i(l,x)@t2 & #t1<#t2 & #t2<#t3 
--                  & (All #t0 pp  . Unlock(pp,l,x)@t0 ==> #t0=#t2) 
--                  & (All pp lpp #t0 . Lock(pp,lpp,x)@t0 ==> #t0<#t1 | #t0=#t1 | #t2<#t0) 
--                  & (All pp lpp #t0 . Unlock(pp,lpp,x)@t0 ==> #t0<#t1 | #t2<#t0 | #t2=#t0 )
--                 ))
--         | #t3<#t1 | #t1=#t3"

-- resLocking v = Right (Restriction {_rstrName = "locking", _rstrFormula = Qua All ("p",LSortMsg) (Qua All ("pp",LSortMsg) (Qua All ("l",LSortMsg) (Qua All ("x",LSortMsg) (Qua All ("lp",LSortMsg) (Qua All ("t1",LSortNode) (Qua All ("t3",LSortNode) (Conn Imp (Conn And (Ato (Action (Bound 1) (Fact {factTag = ProtoFact Linear (hardcode "Lock") 3, factAnnotations = fromList [], factTerms = [Bound 6,Bound 4,Bound 3]}))) (Ato (Action Bound 0 (Fact {factTag = ProtoFact Linear "Lock" 3, factAnnotations = fromList [], factTerms = [Bound 5,Bound 2,Bound 3]})))) (Conn Or (Conn Or (Conn And (Ato (Less Bound 1 Bound 0)) (Qua Ex ("t2",LSortNode) (Conn And (Conn And (Conn And (Conn And (Conn And (Ato (Action Bound 0 (Fact {factTag = ProtoFact Linear (hardcode "Unlock") 3, factAnnotations = fromList [], factTerms = [Bound 7,Bound 5,Bound 4]}))) (Ato (Less Bound 2 Bound 0))) (Ato (Less Bound 0 Bound 1))) (Qua All ("t0",LSortNode) (Qua All ("pp",LSortMsg) (Conn Imp (Ato (Action Bound 1 (Fact {factTag = ProtoFact Linear "Unlock" 3, factAnnotations = fromList [], factTerms = [Bound 0,Bound 7,Bound 6]}))) (Ato (EqE Bound 1 Bound 2)))))) (Qua All ("pp",LSortMsg) (Qua All ("lpp",LSortMsg) (Qua All ("t0",LSortNode) (Conn Imp (Ato (Action Bound 0 (Fact {factTag = ProtoFact Linear "Lock" 3, factAnnotations = fromList [], factTerms = [Bound 2,Bound 1,Bound 7]}))) (Conn Or (Conn Or (Ato (Less Bound 0 Bound 5)) (Ato (EqE Bound 0 Bound 5))) (Ato (Less Bound 3 Bound 0)))))))) (Qua All ("pp",LSortMsg) (Qua All ("lpp",LSortMsg) (Qua All ("t0",LSortNode) (Conn Imp (Ato (Action Bound 0 (Fact {factTag = ProtoFact Linear "Unlock" 3, factAnnotations = fromList [], factTerms = [Bound 2,Bound 1,Bound 7]}))) (Conn Or (Conn Or (Ato (Less Bound 0 Bound 5)) (Ato (Less Bound 3 Bound 0))) (Ato (EqE Bound 3 Bound 0)))))))))) (Ato (Less Bound 0 Bound 1))) (Ato (EqE Bound 1 Bound 0))))))))))})
--     where hardcode s = s -- ++ show $ lvarIdx v

resLocking v =  case resLocking_l of
    Left l -> Left l
    Right r -> Right $ mapName hardcode $ mapFormula (mapAtoms subst) r
    where
        subst _ a 
            | (Action t f) <- a,
              Fact {factTag = ProtoFact Linear "LockPOS" 3} <- f
            =
              Action t (f {factTag = ProtoFact Linear (hardcode "Lock") 3})
            | (Action t f) <- a,
              Fact {factTag = ProtoFact Linear "UnlockPOS" 3} <- f =
              Action t (f {factTag = ProtoFact Linear (hardcode "Unlock") 3})
            | otherwise = a
        hardcode s = s ++ "_" ++ show (lvarIdx v)
        mapFormula = L.modify rstrFormula
        mapName = L.modify rstrName

resEq = parseRestriction [r|restriction predicate_eq:
"All #i a b. Pred_Eq(a,b)@i ==> a = b"
|]

resNotEq = parseRestriction [r|restriction predicate_not_eq:
"All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)"
|]

generateSapicRestrictions :: MonadThrow m => p -> AnProcess ProcessAnnotation -> m [Restriction]
generateSapicRestrictions _ anP = 
  let rest = 
       (if contains isLookup then
        if contains isDelete then
            [resSetIn,  resSetNotIn]
              else 
            [resSetInNoDelete, resSetNotInNoDelete]
         else [])
        ++ 
        addIf (contains isLock) (map resLocking $ getLockPositions anP) -- TODO do we need to remove duplicates?
          -- @ (if contains_locking annotated_process then  List.map res_locking_l (remove_duplicates (get_lock_positions  annotated_process)) else [])
        ++ 
        addIf (contains isEq) [resEq, resNotEq] 
    in
    do
        rest' <- mapM toEx rest
        return rest'
    where
        addIf phi list = if phi then list else []
        contains f = M.getAny $ pfoldMap  (M.Any . f) anP
        isLock (ProcessAction (Lock _) _ _) = True
        isLock _  = False
        isLookup (ProcessComb (Lookup _ _) _ _ _) = True
        isLookup _  = False
        isDelete (ProcessAction (Delete _) _ _) = True
        isDelete _  = False
        isEq (ProcessComb (CondEq _ _) _ _ _) = True
        isEq _  = False
        getLock p 
            | (ProcessAction (Lock _) an _) <- p, (Just (AnLVar v)) <- lock an = [v] -- annotation is Maybe type
            | otherwise  = []
        getLockPositions = pfoldMap  getLock

          -- @ (if op.progress then generate_progress_restrictions annotated_process else [])
          -- @ (if op.progress && contains_resilient_io annotated_process then [res_resilient_l] else [])
          -- @ (if op.accountability then [] else [res_single_session_l])
        -- (*  ^ ass_immeadiate_in -> disabled, sound for most lemmas, see liveness paper
         -- *                  TODO it would be better if we would actually check whether each lemma
         -- *                  is of the right form so we can leave it out...
         -- *                  *)
    -- in
        -- if op.accountability then
          --   (* if an accountability lemma with control needs to be shown, we use a 
          --    * more complex variant of the restritions, that applies them to only one execution *)
          --   (List.map (bind_lemma_to_session (Msg id_ExecId)) restrs)
          --   @ (if op.progress then [progress_init_lemma_acc] else [])
        -- else 
          --   restrs
          --    @ (if op.progress then [progress_init_lemma] else [])

-- TODO need to incorporate lemma2string_noacc
