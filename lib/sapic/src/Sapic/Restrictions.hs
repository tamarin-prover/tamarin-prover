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
import           Control.Monad.Catch
import qualified Data.List              as List
import qualified Data.Monoid            as M
import qualified Data.Set               as S
import           Data.Typeable
import qualified Extension.Data.Label   as L
import           Sapic.Annotation
import           Sapic.Exceptions
import           Sapic.Facts
import           Sapic.ProgressFunction
-- import           Text.Parsec.Error           
import           Text.RawString.QQ
import           Theory
import           Theory.Sapic
import           Theory.Text.Parser

-- | Options passed to the restriction generator:
data RestrictionOptions = RestrictionOptions {
    hasAccountabilityLemmaWithControl :: Bool -- for future use
  , hasProgress :: Bool                       -- for progress translation
  , hasReliableChannels :: Bool               -- adds restriction for reliable channels
  } deriving (Show, Typeable)

-- | Convert parsing erros into Exceptions. To make restrictions easier to
-- modify and thus maintain, we use the parser to convert from
-- a hand-written string. It is possible that there are syntax arrors, in
-- which case the translation should crash with the following error
-- message.
toEx :: MonadThrow m => String -> m Restriction
toEx s 
    | (Left  err) <- parseRestriction s =
        throwM ( ImplementationError ( "Error parsing hard-coded restriction: " ++ s ++ show err )::SapicException AnnotatedProcess)
    | (Right res) <- parseRestriction s = return res
    | otherwise = throwM ( ImplementationError "toEx, otherwise case to satisfy compiler"::SapicException AnnotatedProcess)

resSetIn :: String
resSetIn = [r|restriction set_in: 
"All x y #t3 . IsIn(x,y)@t3 ==>  
(Ex #t2 . Insert(x,y)@t2 & #t2<#t3 
& ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 |  #t3<#t1))
& ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) 
)" |]

resSetNotIn :: String
resSetNotIn = [r|restriction set_notin:
"All x #t3 . IsNotSet(x)@t3 ==> 
        (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )
  | ( Ex #t1 .   Delete(x)@t1 & #t1<#t3  
                &  (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==>  #t2<#t1))"
|]

resSetInNoDelete :: String
resSetInNoDelete = [r|restriction set_in: 
"All x y #t3 . IsIn(x,y)@t3 ==>  
(Ex #t2 . Insert(x,y)@t2 & #t2<#t3 
& ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) 
)" |]

resSetNotInNoDelete :: String
resSetNotInNoDelete = [r|restriction set_notin:
"All x #t3 . IsNotSet(x)@t3 ==> 
(All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )"
|]

resSingleSession :: String
resSingleSession = [r|restrictionsingle_session: // for a single session
"All #i #j. Init()@i & Init()@j ==> #i=#j"
|]

-- | Restriction for Locking. Note that LockPOS hardcodes positions that
-- should be modified below.
resLocking_l :: String
resLocking_l  = [r|restriction locking:
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
resLocking :: MonadThrow m => LVar -> m Restriction
resLocking v =  do
    rest <- toEx resLocking_l
    return $ mapName hardcode $ mapFormula (mapAtoms subst) rest
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

resEq :: String
resEq = [r|restriction predicate_eq:
"All #i a b. Pred_Eq(a,b)@i ==> a = b"
|]


resNotEq :: String
resNotEq = [r|restriction predicate_not_eq:
"All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)"
|]

resResilient :: String
resResilient = [r|restriction resilient: 
"All #i x y. Send(x,y)@i ==> Ex #j. Receive(x,y)@j & #i<#j"
|]

resProgressInit :: String
resProgressInit = [r|restriction progressInit: 
"Ex #t . Init()@t"
|]

flattenList :: Eq a0 => [[a0]] -> [a0]
flattenList = foldr List.union []

-- flattenSet :: Ord a =>  S.Set (S.Set a) -> S.Set a
-- flattenSet = S.foldr S.union S.empty 

-- | Generate set of restrictions:  for a given "from" position
-- | @pf anP pos@ gives set of set position in conjunctive normal form
-- | we produce one restriction for each set of positions in it
generateProgressRestrictions :: (Show ann, Typeable ann, MonadCatch m) => AnProcess ann -> m [Restriction]
generateProgressRestrictions anp = do
    dom_pf <- pfFrom anp -- set of "from" positions
    lss_to <- mapM (restriction) (S.toList dom_pf) -- list of set of sets of "to" positions
    return $ flattenList $ lss_to
    where 
        restriction pos = do  -- produce restriction to go to one of the tos once pos is reached
            toss <- pf anp pos
            restrL <- mapM (\tos -> return $ Restriction (name tos) (formula tos))  (S.toList toss)
            initL <- toEx resProgressInit
            -- return $ Restriction (name tos) (formula tos)
            return $ restrL ++ [initL]
            where
                name tos = "Progress_" ++ show pos ++ "_to_" ++ List.intercalate "_or_" (map show $ S.toList tos)
                formula tos = hinted forall pvar $ hinted forall t1var $ antecedent .==>. (conclusion tos)
                pvar = msgVarProgress pos
                -- pvar = ("prog", LSortMsg)
                -- t1var = ("t1", LSortNode)
                -- t2var = ("t2", LSortNode)
                t1var = LVar "t" LSortNode 1
                t2var = LVar "t" LSortNode 2
                antecedent = Ato $ Action (varTerm $ Free t1var) $ actionToFactFormula (ProgressFrom pos)
                conclusion tos = bigOr $ map progressTo $ S.toList tos
                bigOr [to] = to
                bigOr (to:tos) = to .||. bigOr tos 
                bigOr []   = TF False -- This case should never occur
                progressTo to = hinted exists t2var $ Ato $ Action (varTerm $ Free t2var) $ actionToFactFormula $ ProgressTo to pos
            

-- let generate_progress_restrictions anP =
--   let pf = Progressfunction.generate anP in
--   let rec big_or = function 
--                 | [f] -> f
--                 | f::fl -> Or(f,big_or fl)
--                 | [] -> raise (ImplementationError "There should be at least one to position for every from.")
--   in
--   let lemma a bset = 
--     let a'= Position.pos2string a 
--     in 
--     let pvar = "p "
--     in
--     let blist = (PSet.elements bset)
--     in
--     let progress_to =
--       (* List.map (fun p -> (sprintf "(Ex #t2. ProgressTo_%s(%s)@t2)" (pos2string p) pvar)) blist *)
--         List.map (fun p -> (Ex ( (VarSet.of_list [Temp "t2"]), 
--                             Atom ( At (Action("ProgressTo_"^(pos2string p),[Var (Msg pvar)]),Temp "t2")))))
--                   blist
--     in
--     Restriction ( (sprintf "progress_%s_to_%s" a' (rule_name_part)),
--                  All (VarSet.of_list [Msg pvar; Temp "t1"],
--                   Imp( Atom ( At (Action("ProgressFrom_"^a',[Var (Msg pvar)]),Temp "t1")),
--                        (big_or progress_to))))
--   in
--   (* let print_tosetset a bsetset = *) 

--   (*   PSetSet.fold (fun bset s -> (print_toset a bset) ^ s) bsetset "" *)
--   (* in *)
--   (* (PMap.fold (fun a bsetset s -> (print_tosetset a bsetset) ^ s) pf "") *)
--   let lemmas a bsetset = List.map (lemma a) (PSetSet.elements bsetset) in
--         List.flatten (PMap.fold (fun a bsetset s -> (lemmas a bsetset) :: s) pf [])


-- | generate restrictions depending on options set (op) and the structure
-- of the process (anP)
generateSapicRestrictions :: (MonadThrow m, MonadCatch m) => RestrictionOptions -> AnProcess ProcessAnnotation -> m [Restriction] 
generateSapicRestrictions op anP = 
  let hardcoded_l = 
       (if contains isLookup then
        if contains isDelete then
            [resSetIn,  resSetNotIn]
              else 
            [resSetInNoDelete, resSetNotInNoDelete]
         else [])
        ++ 
        addIf (contains isEq) [resEq, resNotEq] 
        ++ 
        addIf (not $ hasAccountabilityLemmaWithControl op) [resSingleSession] 
        ++
        addIf (hasReliableChannels op && contains isReliableTrans) [resResilient] 
    in
    do
        hardcoded <- mapM toEx hardcoded_l
        locking   <- mapM resLocking (getLockPositions anP)
        -- TODO do we need to remove duplicates?
          -- @ (if contains_locking annotated_process then  List.map res_locking_l (remove_duplicates (get_lock_positions  annotated_process)) else [])
        progress  <- if hasProgress op then
                    generateProgressRestrictions anP
                else
                    return []
        return $ hardcoded ++ locking ++ progress
    where
        addIf phi list = if phi then list else []
        contains f = M.getAny $ pfoldMap  (M.Any . f) anP
        -- isLock (ProcessAction (Lock _) _ _) = True
        -- isLock _  = False
        isLookup (ProcessComb (Lookup _ _) _ _ _) = True
        isLookup _  = False
        isDelete (ProcessAction (Delete _) _ _) = True
        isDelete _  = False
        isEq (ProcessComb (CondEq _ _) _ _ _) = True
        isEq _  = False
        isReliableTrans (ProcessAction ac _ _) 
            -- | (ChIn (Just r) t) <- ac
            -- ,Lit (Con name) <- viewTerm r
            -- , sortOfName name == LSortPub
            -- , getNameId (nId name) == "r" = True
            | (ChOut (Just tr) _) <- ac -- If there are only receives on the
                                       -- reliable channel, we do not need the restriction
            ,Lit (Con name) <- viewTerm tr
            , sortOfName name == LSortPub
            , getNameId (nId name) == "r" = True
            | otherwise = False
        isReliableTrans _ = False 
        getLock p 
            | (ProcessAction (Lock _) an _) <- p, (Just (AnLVar v)) <- lock an = [v] -- annotation is Maybe type
            | otherwise  = []
        getLockPositions = pfoldMap  getLock

        -- TODO need to incorporate lemma2string_noacc
        -- TODO add missing features. This is what SAPIC did
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

