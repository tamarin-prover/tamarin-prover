{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternGuards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute translation-specific restrictions
module Sapic.Restrictions (
      generateSapicRestrictions
    , RestrictionOptions(..)
) where
import qualified  Data.Monoid as M
import Data.Maybe
import Data.Typeable
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

-- | Options passed to the restriction generator:
data RestrictionOptions = RestrictionOptions {
    hasAccountabilityLemmaWithControl :: Bool -- for future use
  , hasProgress :: Bool                       -- for progress translation
  } deriving (Show, Typeable)

-- | Convert parsing erros into Exceptions. To make restrictions easier to
-- modify and thus maintain, we use the parser to convert from
-- a hand-written string. It is possible that there are syntax arrors, in
-- which case the translation should crash with the following error
-- message.
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

resSingleSession = parseRestriction [r|restrictionsingle_session: // for a single session
"All #i #j. Init()@i & Init()@j ==> #i=#j"
|]

-- | Restriction for Locking. Note that LockPOS hardcodes positions that
-- should be modified below.
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

-- | Produce locking lemma for variable v by instantiating resLocking_l 
--  with (Un)Lock_pos instead of (Un)LockPOS, where pos is the variable id
--  of v.
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

-- | generate restrictions depending on options set (op) and the structure
-- of the process (anP)
generateSapicRestrictions :: MonadThrow m => RestrictionOptions -> AnProcess ProcessAnnotation -> m [Restriction]
generateSapicRestrictions op anP = 
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
        ++ 
        addIf (not $ hasAccountabilityLemmaWithControl op) [resSingleSession] 
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

        -- TODO need to incorporate lemma2string_noacc
        -- TODO add missing features. This is what SAPIC did
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

