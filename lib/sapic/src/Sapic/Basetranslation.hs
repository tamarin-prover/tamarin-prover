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
   -- types
   , TransFact
   , TranslationResultNull 
   , TranslationResultAct 
   , TranslationResultComb 
   , TransFNull 
   , TransFAct
   , TransFComb
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

type TranslationResultNull  = ([([TransFact], [TransAction], [TransFact], [SyntacticLNFormula])])
type TranslationResultAct  = ([([TransFact], [TransAction], [TransFact], [SyntacticLNFormula])], Set LVar)
type TranslationResultComb  = ([([TransFact], [TransAction], [TransFact], [SyntacticLNFormula])], Set LVar, Set LVar)

type TransFNull t = ProcessAnnotation
                             -> ProcessPosition
                             -> Set LVar
                             -> t

type TransFAct t = SapicAction
                             -> ProcessAnnotation
                             -> ProcessPosition
                             -> Set LVar
                             -> t
type TransFComb t = ProcessCombinator
                        -> ProcessAnnotation
                        -> ProcessPosition -> Set LVar
                        -> t

-- | The basetranslation has three functions, one for translating the Null
-- Process, one for actions (i.e. constructs with only one child process) and
-- one for combinators (i.e., constructs with two child processes).
baseTrans :: MonadThrow m => Bool ->
                          (TransFNull (m TranslationResultNull),
                           TransFAct (m TranslationResultAct),
                           TransFComb (m TranslationResultComb))
baseTrans needsAssImmediate = (\ a p tx ->  return $ baseTransNull a p tx,
             \ ac an p tx -> return $ baseTransAction needsAssImmediate ac an p tx,
             \ comb an p tx -> return $ baseTransComb comb an p tx) -- I am sure there is nice notation for that.

--  | Each part of the translation outputs a set of multiset rewrite rules,
--    and ~x (tildex), the set of variables hitherto bound
baseTransNull :: TransFNull TranslationResultNull
baseTransNull _ p tildex =  [([State LState p tildex ], [], [], [])]

baseTransAction :: Bool -> TransFAct TranslationResultAct
baseTransAction needsAssImmediate ac an p tildex
    |  Rep <- ac = ([
          ([def_state], [], [State PSemiState (p++[1]) tildex ], []),
          ([State PSemiState (p++[1]) tildex], [], [def_state' tildex], [])
          ], tildex)
    | (New v) <- ac = let tx' = v `insert` tildex in
        ([ ([def_state, Fr v], [], [def_state' tx'], []) ], tx')
    | (ChIn (Just tc) t) <- ac, (Just (AnLVar _)) <- secretChannel an =
          let tx' = freeset tc `union` freeset t `union` tildex in
          ([
          ([def_state, Message tc t], [], [Ack tc t, def_state' tx'], [])], tx')
    | (ChIn (Just tc) t) <- ac, Nothing <- secretChannel an =
          let tx' = freeset tc `union` freeset t `union` tildex in
          let ts  = fAppPair (tc,t) in
          ([
          ([def_state, In ts], if needsAssImmediate then [ ChannelIn ts] else [], [def_state' tx'], []),
          ([def_state, Message tc t], [], [Ack tc t, def_state' tx'], [])], tx')
    | (ChIn Nothing t) <- ac =
          let tx' = freeset t `union` tildex in
          ([ ([def_state, In t ], [ ], [def_state' tx'], []) ], tx')
    | (ChOut (Just tc) t) <- ac, (Just (AnLVar _)) <- secretChannel an =
          let semistate = State LSemiState (p++[1]) tildex in
          ([
          ([def_state], [], [Message tc t,semistate], []),
          ([semistate, Ack tc t], [], [def_state' tildex], [])], tildex)
    | (ChOut (Just tc) t) <- ac, Nothing <- secretChannel an =
          let semistate = State LSemiState (p++[1]) tildex in
          ([
          ([def_state, In tc], if needsAssImmediate then [ ChannelIn tc] else [], [Out t, def_state' tildex], []),
          ([def_state], [], [Message tc t,semistate], []),
          ([semistate, Ack tc t], [], [def_state' tildex], [])], tildex)
    | (ChOut Nothing t) <- ac =
          ([
          ([def_state], [], [def_state' tildex, Out t], [])], tildex)
    | (Insert t1 t2 ) <- ac =
          ([
          ([def_state], [InsertA t1 t2], [def_state' tildex], [])], tildex)
    | (Delete t ) <- ac =
          ([
          ([def_state], [DeleteA t ], [def_state' tildex], [])], tildex)
    | (Lock t ) <- ac, (Just (AnLVar v)) <- lock an =
          let tx' = v `insert` tildex in
      ([
      ([def_state, Fr v], [LockNamed t v, LockUnnamed t v ], [def_state' tx'], [])], tx')
    | (Lock _ ) <- ac, Nothing <- lock an = throw (NotImplementedError "Unannotated lock" :: SapicException AnnotatedProcess)

    | (Unlock t ) <- ac, (Just (AnLVar v)) <- unlock an =
          ([([def_state], [UnlockNamed t v, UnlockUnnamed t v ], [def_state' tildex], [])], tildex)
    | (Unlock _ ) <- ac, Nothing <- lock an = throw ( NotImplementedError "Unannotated unlock" :: SapicException AnnotatedProcess)
    | (Event f ) <- ac =
          ([([def_state], [TamarinAct f] ++ if needsAssImmediate then [EventEmpty] else [], [def_state' tildex], [])], tildex)
    | (MSR (l,a,r,res)) <- ac =
          let tx' = freeset' l `union` tildex in
          ([(def_state:map TamarinFact l, map TamarinAct a ++ if needsAssImmediate then [EventEmpty] else [], def_state' tx':map TamarinFact r, res)], tx')
    | otherwise = throw ((NotImplementedError $ "baseTransAction:" ++ prettySapicAction ac) :: SapicException AnnotatedProcess)
    where
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
baseTransComb :: TransFComb TranslationResultComb
baseTransComb c _ p tildex
    | Parallel <- c = (
               [([def_state], [], [def_state1 tildex,def_state2 tildex], [])]
             , tildex, tildex )
    | NDC <- c = (
               []
             , tildex, tildex )
    | Cond f <- c =
        let freevars_f = fromList $ freesList  f in
        if freevars_f `isSubsetOf` tildex then
                ([ ([def_state], [], [def_state1 tildex], [f]),
                    ([def_state], [], [def_state2 tildex], [Not f])]
                     , tildex, tildex )
        else
                    throw ( 
                    ProcessNotWellformed $ WFUnboundProto (freevars_f `difference` tildex)
                        :: SapicException AnnotatedProcess)

    | CondEq t1 t2 <- c =
        let fa = (protoFact Linear "Eq" [t1,t2]) in
        let vars_f = fromList $ getFactVariables fa in
        if vars_f `isSubsetOf` tildex then
                ([ ([def_state], [PredicateA fa], [def_state1 tildex], []),
                    ([def_state], [NegPredicateA fa], [def_state2 tildex], [])]
                     , tildex, tildex )
                else
                    throw ( 
                    ProcessNotWellformed $ WFUnboundProto (vars_f `difference` tildex)
                        :: SapicException AnnotatedProcess)
    | Lookup t v <- c =
           let tx' = v `insert` tildex in
                (
       [ ([def_state], [IsIn t v], [def_state1 tx' ], []),
         ([def_state], [IsNotSet t], [def_state2 tildex], [])]
             , tx', tildex )
    | otherwise = throw (NotImplementedError "baseTransComb":: SapicException AnnotatedProcess)
    where
        def_state = State LState p tildex
        def_state1 tx = State LState (p++[1]) tx
        def_state2 tx = State LState (p++[2]) tx

-- | @baseInit@ provides the initial rule that is used to create the first
-- linear statefact. An additional restriction on InitEmpty makes sure it can
-- only be used once.
baseInit :: AnProcess ann -> ([AnnotatedRule ann], Set a)
baseInit anP = ([AnnotatedRule (Just "Init") anP (Right InitPosition) l a r [] 0],empty)
  where
        l = []
        a = [InitEmpty ]
        r = [State LState [] empty]


-- | Convert parsing erros into Exceptions. To make restrictions easier to
-- modify and thus maintain, we use the parser to convert from
-- a hand-written string. It is possible that there are syntax arrors, in
-- which case the translation should crash with the following error
-- message.
toEx :: MonadThrow m => String -> m SyntacticRestriction
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

-- | Restriction for Locking where no Unlock is necessary.
resLockingLNoUnlockPOS :: String
resLockingLNoUnlockPOS  = [QQ.r|restriction locking:
"All p l x #t1 . LockPOS(p,l,x)@t1 
                   ==> (All pp lp #t2. LockPOS(pp,lp,x)@t2 ==> #t1=#t2)"
|]

-- | Restriction for Locking where no Unlock is necessary.
resLockingNoUnlock :: String
resLockingNoUnlock  = [QQ.r|restriction locking:
"All p l x #t1 . Lock(p,l,x)@t1 
                   ==> (All pp lp #t2. Lock(pp,lp,x)@t2 ==> #t1=#t2)"
|]

-- | Produce locking lemma for variable v by instantiating resLockingL 
--  with (Un)Lock_pos instead of (Un)LockPOS, where pos is the variable id
--  of v.
resLocking :: MonadThrow m => Bool -> LVar -> m SyntacticRestriction
resLocking hasUnlock v =  do
    rest <- if hasUnlock then
              toEx resLockingL
            else
              toEx resLockingLNoUnlockPOS
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


resInEv :: String
resInEv = [QQ.r|restriction ass_immediate:
"All x #t3. ChannelIn(x)@t3 ==> (Ex #t2. K(x)@t2 & #t2 < #t3
                                & (All #t1. Event()@t1  ==> #t1 < #t2 | #t3 < #t1)
                                & (All #t1 xp. K(xp)@t1 ==> #t1 < #t2 | #t1 = #t2 | #t3 < #t1))"
|]


-- | generate restrictions depending on options set (op) and the structure
-- of the process (anP)
baseRestr :: (MonadThrow m, MonadCatch m) => AnProcess ProcessAnnotation -> Bool -> Bool -> Bool -> [SyntacticRestriction] -> m [SyntacticRestriction]
baseRestr anP needsAssImmediate containChannelIn hasAccountabilityLemmaWithControl prevRestr =
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
        addIf hasAccountabilityLemmaWithControl [resSingleSession]
        ++
        addIf (needsAssImmediate && containChannelIn) [resInEv]
    in
    do
        hardcoded <- mapM toEx hardcoded_l
        locking   <- mapM (resLocking $ contains isUnlock) (getLockPositions anP) 
        singleLocking <- toEx resLockingNoUnlock

        return $ prevRestr ++ hardcoded ++ locking 
                 ++ 
                 addIf ((not $ contains isUnlock) && (contains isLock)) [singleLocking]
    where
        addIf phi list = if phi then list else []
        contains = processContains anP
        getLock p
            | (ProcessAction (Lock _) an _) <- p, (Just (AnLVar v)) <- lock an = [v] -- annotation is Maybe type
            | otherwise  = []
        getLockPositions = pfoldMap getLock

        -- This is what SAPIC did
          -- @ (if op.accountability then [] else [res_single_session_l])
