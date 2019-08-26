{-# LANGUAGE QuasiQuotes #-}
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
   , toEx
   , baseRestr
   , toLVar
   , toLNTerm
   , toLNFact
) where

import           Control.Exception
import           Control.Monad.Catch
import           Data.Set             hiding (map)
import qualified Extension.Data.Label as L
import           Sapic.Annotation
import           Sapic.Exceptions
import           Sapic.Facts
import           Sapic.ProcessUtils
import qualified Text.RawString.QQ    as QQ
import           Theory
import           Theory.Sapic
import           Theory.Sapic.Print
import           Theory.Text.Parser

-- TODO not sure which module to move these two
toLVar:: SapicLVar -> LVar
toLVar = slvar

toLNTerm:: SapicTerm -> LNTerm 
toLNTerm = fmap f 
    where 
        f (Con c) = Con c
        f (Var v) = Var $ toLVar v

toLNFact:: SapicLNFact -> LNFact 
toLNFact = fmap toLNTerm

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
    | (New v) <- ac = let tx' = (toLVar v) `insert` tildex in
        ([ ([def_state, Fr $ toLVar v], [], [def_state' tx']) ], tx')
    | (ChIn (Just tc') t') <- ac, (Just (AnLVar _)) <- secretChannel an
      , tc <- toLNTerm tc', t <- toLNTerm t' =
          let tx' = (freeset tc) `union` (freeset t) `union` tildex in
          ([
          ([def_state, Message tc t], [], [Ack tc t, def_state' tx'])], tx')
    | (ChIn (Just tc') t') <- ac, Nothing <- secretChannel an
      , tc <- toLNTerm tc', t <- toLNTerm t' =
          let tx' = (freeset tc) `union` (freeset t) `union` tildex in
          let ts  = fAppPair (tc,t) in
          ([
          ([def_state, In ts], [ ChannelIn ts], [def_state' tx']),
          ([def_state, Message tc t], [], [Ack tc t, def_state' tx'])], tx')
    | (ChIn Nothing t') <- ac 
      , t <- toLNTerm t' =
          let tx' = freeset t `union` tildex in
          ([ ([def_state, (In t) ], [ ], [def_state' tx']) ], tx')
    | (ChOut (Just tc') t') <- ac, (Just (AnLVar _)) <- secretChannel an 
      , tc <- toLNTerm tc', t <- toLNTerm t' =
          let semistate = State LSemiState (p++[1]) tildex in
          ([
          ([def_state], [], [Message tc t,semistate]),
          ([semistate, Ack tc t], [], [def_state' tildex])], tildex)
    | (ChOut (Just tc') t') <- ac, Nothing <- secretChannel an 
      , tc <- toLNTerm tc', t <- toLNTerm t' =
          let semistate = State LSemiState (p++[1]) tildex in
          ([
          ([def_state, In tc], [ ChannelIn tc], [Out t, def_state' tildex]),
          ([def_state], [], [Message tc t,semistate]),
          ([semistate, Ack tc t], [], [def_state' tildex])], tildex)
    | (ChOut Nothing t') <- ac 
      , t <- toLNTerm t' =
          ([
          ([def_state], [], [def_state' tildex, Out t])], tildex)
    | (Insert t1' t2' ) <- ac 
      , t1 <- toLNTerm t1' , t2 <- toLNTerm t2'  =
          ([
          ([def_state], [InsertA t1 t2], [def_state' tildex])], tildex)
    | (Delete t') <- ac 
      , t <- toLNTerm t' =
          ([
          ([def_state], [DeleteA t ], [def_state' tildex])], tildex)
    | (Lock t') <- ac, (Just (AnLVar v)) <- lock an 
      , t <- toLNTerm t' =
          let tx' = v `insert` tildex in
      ([
      ([def_state, Fr v], [LockNamed t v, LockUnnamed t v ], [def_state' tx'])], tx')
    | (Lock _ ) <- ac, Nothing <- lock an = throw (NotImplementedError "Unannotated lock" :: SapicException AnnotatedProcess)

    | (Unlock t') <- ac, (Just (AnLVar v)) <- unlock an 
      , t <- toLNTerm t' =
          ([([def_state], [UnlockNamed t v, UnlockUnnamed t v ], [def_state' tildex])], tildex)
    | (Unlock _ ) <- ac, Nothing <- lock an = throw ( NotImplementedError "Unannotated unlock" :: SapicException AnnotatedProcess)
    | (Event f' ) <- ac 
      , f <- toLNFact f' =
          ([([def_state], [TamarinAct f], [def_state' tildex])], tildex)
    | (MSR (l',a',r')) <- ac
      , (l,a,r) <- ( map toLNFact l' , map toLNFact a' , map toLNFact r') =
          let tx' = (freeset' r) `union` tildex in
          ([(def_state:map TamarinFact l, map TamarinAct a, def_state' tx':map TamarinFact r)], tx')
    | otherwise = throw ((NotImplementedError $ "baseTransAction:" ++ prettySapicAction ac) :: SapicException AnnotatedProcess)
    where
        -- dropTypes = fmap toLVar
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
    | Lookup t' v' <- c 
      , t <- toLNTerm t', v <- toLVar v' =
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
        condition f'
            | f <- toLNFact f' =
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
resSetIn = [QQ.r|restriction set_in: 
"All x y #t3 . IsIn(x,y)@t3 ==>  
(Ex #t2 . Insert(x,y)@t2 & #t2<#t3 
& ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 |  #t3<#t1))
& ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) 
)" |]

resSetNotIn :: String
resSetNotIn = [QQ.r|restriction set_notin:
"All x #t3 . IsNotSet(x)@t3 ==> 
        (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )
  | ( Ex #t1 .   Delete(x)@t1 & #t1<#t3  
                &  (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==>  #t2<#t1))"
|]

resSetInNoDelete :: String
resSetInNoDelete = [QQ.r|restriction set_in: 
"All x y #t3 . IsIn(x,y)@t3 ==>  
(Ex #t2 . Insert(x,y)@t2 & #t2<#t3 
& ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)) 
)" |]

resSetNotInNoDelete :: String
resSetNotInNoDelete = [QQ.r|restriction set_notin:
"All x #t3 . IsNotSet(x)@t3 ==> 
(All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )"
|]

resSingleSession :: String
resSingleSession = [QQ.r|restrictionsingle_session: // for a single session
"All #i #j. Init()@i & Init()@j ==> #i=#j"
|]

-- | Restriction for Locking. Note that LockPOS hardcodes positions that
-- should be modified below.
resLockingL :: String
resLockingL  = [QQ.r|restriction locking:
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

-- | Produce locking lemma for variable v by instantiating resLockingL 
--  with (Un)Lock_pos instead of (Un)LockPOS, where pos is the variable id
--  of v.
resLocking :: MonadThrow m => LVar -> m Restriction
resLocking v =  do
    rest <- toEx resLockingL
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
resEq = [QQ.r|restriction predicate_eq:
"All #i a b. Pred_Eq(a,b)@i ==> a = b"
|]


resNotEq :: String
resNotEq = [QQ.r|restriction predicate_not_eq:
"All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)"
|]

-- | generate restrictions depending on options set (op) and the structure
-- of the process (anP)
baseRestr :: (MonadThrow m, MonadCatch m) => AnProcess ProcessAnnotation -> Bool -> [Restriction] -> m [Restriction] 
baseRestr anP hasAccountabilityLemmaWithControl prevRestr = 
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
        addIf (hasAccountabilityLemmaWithControl) [resSingleSession] 
    in
    do
        hardcoded <- mapM toEx hardcoded_l
        locking   <- mapM resLocking (getLockPositions anP)
        return $ prevRestr ++ hardcoded ++ locking
    where
        addIf phi list = if phi then list else []
        contains = processContains anP
        isLookup (ProcessComb (Lookup _ _) _ _ _) = True
        isLookup _  = False
        isDelete (ProcessAction (Delete _) _ _) = True
        isDelete _  = False
        isEq (ProcessComb (CondEq _ _) _ _ _) = True
        isEq _  = False
        getLock p 
            | (ProcessAction (Lock _) an _) <- p, (Just (AnLVar v)) <- lock an = [v] -- annotation is Maybe type
            | otherwise  = []
        getLockPositions = pfoldMap getLock

        -- TODO add feature checking lemmas for wellformedness, adding ass_immeadiate_in if necessary 
        -- This is what SAPIC did
          -- @ (if op.accountability then [] else [res_single_session_l])
        -- (*  ^ ass_immeadiate_in -> disabled, sound for most lemmas, see liveness paper
         -- *                  it would be better if we would actually check whether each lemma
         -- *                  is of the right form so we can leave it out...
         -- *                  *)
    -- in
