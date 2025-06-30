{-# LANGUAGE QuasiQuotes #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation rules common for different translation types in SAPIC
module Sapic.Basetranslation (
    -- translation
     baseTransNull
   , baseTransComb
   , baseTransAction
   , baseTrans
   , baseInit
   , baseRestr
   , resLockingPure
   -- helper
   , toEx
   , toLVar
   , toLNTerm
   , toLNFact
   -- types
   , TransFact
   , TranslationResultNull
   , TranslationResultAct
   , TranslationResultComb
   , TransFNull
   , TransFAct
   , TransFComb
) where

import Control.Exception
import Control.Monad.Catch
import Data.Set hiding (map, (\\))
import Data.Maybe
import Data.List qualified as List
import Sapic.Annotation
import Sapic.Exceptions
import Sapic.Facts
import Sapic.ProcessUtils
import Text.RawString.QQ qualified as QQ
import Theory
import Theory.Sapic
import Theory.Sapic.Print
import Theory.Text.Parser

type TranslationResultNull  = [([TransFact], [TransAction], [TransFact], [SyntacticLNFormula])]
type TranslationResultAct  = ([([TransFact], [TransAction], [TransFact], [SyntacticLNFormula])], Set LVar)
type TranslationResultComb  = ([([TransFact], [TransAction], [TransFact], [SyntacticLNFormula])], Set LVar, Set LVar)

type TransFNull t = ProcessAnnotation LVar
                             -> ProcessPosition
                             -> Set LVar
                             -> t

type TransFAct t = SapicAction SapicLVar
                             -> ProcessAnnotation LVar
                             -> ProcessPosition
                             -> Set LVar
                             -> t
type TransFComb t = ProcessCombinator SapicLVar
                        -> ProcessAnnotation LVar
                        -> ProcessPosition -> Set LVar
                        -> t

-- | The basetranslation has three functions, one for translating the Null
-- Process, one for actions (i.e. constructs with only one child process) and
-- one for combinators (i.e., constructs with two child processes).
baseTrans :: MonadThrow m => Bool -> Bool ->
                          (TransFNull (m TranslationResultNull),
                           TransFAct (m TranslationResultAct),
                           TransFComb (m TranslationResultComb))
baseTrans asyncChannels needsInEvRes = (\ a p tx ->  return $ baseTransNull a p tx,
             \ ac an p tx -> return $ baseTransAction asyncChannels needsInEvRes ac an p tx,
             \ comb an p tx -> return $ baseTransComb comb an p tx) -- I am sure there is nice notation for that.

--  | Each part of the translation outputs a set of multiset rewrite rules,
--    and ~x (tildex), the set of variables hitherto bound
baseTransNull :: TransFNull TranslationResultNull
baseTransNull _ p tildex =  [([State LState p tildex ], [], [], [])]

mergeWithStateRule' :: ([TransFact], [a1], [a2]) -> ([TransFact], [a1], [a2], d) -> ([TransFact], [a1], [a2], d)
mergeWithStateRule' (l',a',r') (l,a,r,f)
  | (Just _) <- List.find isState l
  = (l ++ l', a ++ a', r++r', f)
  | otherwise
  = (l,a,r,f)

mergeWithStateRule :: ([TransFact], [a1], [a2]) -> [([TransFact], [a1], [a2], d)] -> [([TransFact], [a1], [a2], d)]
mergeWithStateRule r' = map (mergeWithStateRule' r')

baseTransAction :: Bool -> Bool -> TransFAct TranslationResultAct
baseTransAction
  asyncChannels -- true if private channels ought to be asnchronous
  needsAssImmediate  -- produce actions that axiom AssImmediate requires
  ac an p tildex -- current action, its annotation, position in the process tree, and variables bound so far
    |  Rep <- ac = ([
          ([def_state], [], [State PSemiState (p++[1]) tildex ], []),
          ([State PSemiState (p++[1]) tildex], [], [def_state' tildex], [])
          ], tildex)
    | (New v) <- ac = let tx' = toLVar v `insert` tildex in
        ([ ([def_state, Fr $ toLVar v], [], [def_state' tx'], []) ], tx')
    | (ChIn channel t' matchVar) <- ac, t <- toLNTerm t' =  -- handle channel input in(c,pat);P like in(c,x); let pat = x in P
          let x = evalFreshAvoiding (freshLVar "x" LSortMsg) tildex in
          let xt = varTerm x in
          let xTerm = varTerm (SapicLVar { slvar = x, stype = Nothing}) in
          let (rules,tx',_) =  baseTransComb (Let t' xTerm matchVar) (an {elseBranch = False }) p tildex
          -- tx' does not include fresh x because it is on the right hand side
          -- that's ok because follow up process does not use x anyway, since
          -- the process was ground before introducing x freshly
          in
          case channel of
            Nothing -> if needsAssImmediate then  -- delay matching, as in(pat) behaves like in(x); let pat = x in ..
                         (mergeWithStateRule ([In (varTerm x)], channelIn (varTerm x), []) rules, tx')
                       else
                         let tx2' = freeset t `union` tildex in
                           ([ ([def_state, In t], [ ], [def_state' tx2'], []) ], tx2')
            Just tc' -> let tc = toLNTerm tc' in
                        let ts = fAppPair (tc,varTerm x) in
                        let ack = [Ack tc xt | not asyncChannels] in
                          (mergeWithStateRule ([Message tc xt], [], ack) rules
                            ++ (if isNothing (secretChannel an) -- only add adversary rule if channel is not guaranteed secret
                                 then mergeWithStateRule ([In ts], channelIn ts, []) rules
                                 else []
                               ), tx')
    | (ChOut (Just tc') t') <- ac, (Just (AnVar _)) <- secretChannel an
      , tc <- toLNTerm tc', t <- toLNTerm t' =
          if asyncChannels then
              ([
              ([def_state], [], [Message tc t, def_state' tildex], [])], tildex)
          else
            let semistate = State LSemiState (p++[1]) tildex in
              ([
               ([def_state], [], [Message tc t,semistate], []),
               ([semistate, Ack tc t], [], [def_state' tildex], [])], tildex)
    | (ChOut (Just tc') t') <- ac, Nothing <- secretChannel an
      , tc <- toLNTerm tc', t <- toLNTerm t' =
          if asyncChannels then
              ([
              ([def_state, In tc], channelIn tc, [Out t, def_state' tildex], []),
              ([def_state], [], [Message tc t,def_state' tildex], [])], tildex)
          else
            let semistate = State LSemiState (p++[1]) tildex in
              ([
              ([def_state, In tc], channelIn tc, [Out t, def_state' tildex], []),
              ([def_state], [], [Message tc t,semistate], []),
              ([semistate, Ack tc t], [], [def_state' tildex], [])], tildex)
    | (ChOut Nothing t') <- ac
      , t <- toLNTerm t' =
          ([
          ([def_state], [], [def_state' tildex, Out t], [])], tildex)

      -- Pure cell translation
    | (Insert t1' t2' ) <- ac, True <- pureState an,  (Just (AnVar v)) <- unlock an,
      t1 <- toLNTerm t1' , t2 <- toLNTerm t2' =
          let tx' = v `insert` tildex in
          ([
          ([def_state, CellLocked t1 (varTerm v)], [
              --UnlockUnnamed t1 v
                                                   ], [def_state' tx', PureCell t1 t2], [])], tx')
    | (Insert t1' t2' ) <- ac, True <- pureState an,
      t1 <- toLNTerm t1' , t2 <- toLNTerm t2' =
          ([
          ([def_state], [
              --UnlockUnnamed t1 v
                                                   ], [def_state' tildex, PureCell t1 t2], [])], tildex)

    | (Lock _) <- ac, True <- pureState an =
      ([
      ([def_state], [], [def_state' tildex], [])], tildex)
    | (Unlock _) <- ac, True <- pureState an =
          ([([def_state], [], [def_state' tildex], [])], tildex)

    -- Classical state translation
    | (Insert t1' t2' ) <- ac
      , t1 <- toLNTerm t1' , t2 <- toLNTerm t2'  =
          ([
          ([def_state], [InsertA t1 t2], [def_state' tildex], [])], tildex)
    | (Delete t') <- ac
      , t <- toLNTerm t' =
          ([
          ([def_state], [DeleteA t ], [def_state' tildex], [])], tildex)
    | (Lock t') <- ac, (Just (AnVar v)) <- lock an
      , t <- toLNTerm t' =
          let tx' = v `insert` tildex in
      ([
      ([def_state, Fr v], [LockNamed t v, LockUnnamed t v ], [def_state' tx'], [])], tx')
    | (Lock _ ) <- ac, Nothing <- lock an = throw (NotImplementedError "Unannotated lock" :: SapicException AnnotatedProcess)
    | (Unlock t') <- ac, (Just (AnVar v)) <- unlock an
      , t <- toLNTerm t' =
          ([([def_state], [UnlockNamed t v, UnlockUnnamed t v ], [def_state' tildex], [])], tildex)
    | (Unlock _ ) <- ac, Nothing <- lock an = throw ( NotImplementedError "Unannotated unlock" :: SapicException AnnotatedProcess)

-- CHARLIE : still add locks and unlocks in the pure state thing, but with weaker formula only used to contradict injectivity, e.g    Lock(x,s)@i & Unlock(x,s)@j ==> not(Ex k s2. Lock(x,s2)@k & i<k<j) & not(Ex k s2. UnLock(x,s2)@k & i<k<j)
    | (Event f' ) <- ac
      , f <- toLNFact f' =
          ([([def_state], TamarinAct f : [EventEmpty | needsAssImmediate], [def_state' tildex], [])], tildex)
    | (MSR l' a' r' res' _) <- ac
      , (l,a,r,res) <- ( map toLNFact l' , map toLNFact a' , map toLNFact r', map toLFormula res') =
          let tx' = freeset' l `union` tildex in
          ([(def_state:map TamarinFact l, map TamarinAct a ++ [EventEmpty | needsAssImmediate ], def_state' tx':map TamarinFact r, res)], tx')
    | otherwise = throw ((NotImplementedError $ "baseTransAction:" ++ prettySapicAction ac) :: SapicException AnnotatedProcess)
    where
        def_state = State LState p tildex -- default state when entering
        def_state' tx = State LState (p++[1]) tx -- default follow upstate, possibly with new bound variables
        channelIn ts = [ChannelIn ts | needsAssImmediate]
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
baseTransComb c an p tildex
    | Parallel <- c = (
               [([def_state], [], [def_state1 tildex,def_state2 tildex], [])]
             , tildex, tildex )
    | NDC <- c = (
               []
             , tildex, tildex )
    | Cond f' <- c
      , f <- toLFormula f' =
        let freevars_f = fromList $ freesList  f in
        if freevars_f `isSubsetOf` tildex then
                ([ ([def_state], [], [def_state1 tildex], [f]),
                    ([def_state], [], [def_state2 tildex], [Not f])]
                     , tildex, tildex )
        else
                    throw $ WFUnbound (freevars_f `difference` tildex)
    | CondEq t1 t2 <- c =
        let fa = toLNFact (protoFact Linear "Eq" [t1,t2]) in
        let vars_f = fromList $ getFactVariables fa in
        if vars_f `isSubsetOf` tildex then
                ([ ([def_state],  [PredicateA fa], [def_state1 tildex], []),
                    ([def_state], [NegPredicateA fa], [def_state2 tildex], [])]
                     , tildex, tildex )
                else
                    throw $ WFUnbound (vars_f `difference` tildex)
    | Let t1' t2' _ <- c,  -- match vars are ignored in the translation, as they are bound in the def_state
      elsBranch <- elseBranch an
      =
        let t1or = toLNTerm t1' in
        let (t1, t2, freevars) =
              case destructorEquation an of
                Nothing -> (t1or, toLNTerm t2', freeset t1or)
                Just (tl1,tl2) -> (tl1, tl2, freeset tl1 `difference` tildex)
        in
        let fa = Conn Imp (Ato (EqE (fmapTerm (fmap Free) t1) (fmapTerm (fmap Free) t2))) (TF False) in
        let tildexl =  freeset t1or `union` tildex in
        let faN = fold (hinted forAll) fa freevars in
        let pos = p++[1] in
        if elsBranch then
          ([
              ([def_state], [], [FLet pos t2 tildex], []),
              ([FLet pos t1 tildex], [], [def_state1 tildexl], []),
              ([FLet pos t2 tildex], [] , [def_state2 tildex], [faN])
           ],
            tildexl, tildex)
        else
          ([
              ([def_state], [], [FLet pos t2 tildex], []),
              ([FLet pos t1 tildex], [], [def_state1 tildexl], [])
           ],
            tildexl, tildex)

    -- Pure cell translation
    | Lookup t' v' <- c,  True <- pureState an,  (Just (AnVar vs)) <- unlock an,
       t <- toLNTerm t', v <- toLVar v' =
           let tx' = vs `insert ` (v `insert` tildex) in
                (
       [ ([def_state,  PureCell t (varTerm v), Fr vs], [
             --LockUnnamed t vs
                                                       ], [def_state1 tx', CellLocked t (varTerm vs) ], [])
--        , ([def_state], [IsNotSet t], [def_state2 tildex], [])
       ]
             , tx', tildex )


    -- Classical state translation
    | Lookup t' v' <- c
      , t <- toLNTerm t', v <- toLVar v' =
           let tx' = v `insert` tildex in
                (
       [ ([def_state], [IsIn t v], [def_state1 tx' ], []),
         ([def_state], [IsNotSet t], [def_state2 tildex], [])]
             , tx', tildex )
-- Process Calls are currently made by a simple inlining of the process, where the parameters have already been substituded by the value of the caller inside the parser. Variants could be defined to optimize this behaviour.
    | ProcessCall {} <- c =
       ([ ([def_state], [], [def_state1 tildex, def_state2 tildex ], [])], -- TODO remove second state def_state2 but make sure `gen` does not produce rule for it in this case, otherwise we get warnings.
        tildex,tildex)

    -- | otherwise = throw (NotImplementedError "baseTransComb":: SapicException AnnotatedProcess)
    where
        def_state = State LState p tildex
        def_state1 tx = State LState (p++[1]) tx
        def_state2 tx = State LState (p++[2]) tx
        freeset = fromList . frees


-- | @baseInit@ provides the initial rule that is used to create the first
-- linear statefact. An additional restriction on InitEmpty makes sure it can
-- only be used once.
baseInit :: LProcess ann -> ([AnnotatedRule ann], Set a)
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
    -- | otherwise = throwM ( ImplementationError "toEx, otherwise case to satisfy compiler"::SapicException AnnotatedProcess)

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
resLockingPOS :: String
resLockingPOS  = [QQ.r|restriction locking:
"All p pp l x lp #t1 #t3. LockPOS(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>
        (#t1<#t3 & (Ex #t2. UnlockPOS(p, l, x)@t2 & #t1 < #t2 & #t2 < #t3
                   & (All #t0 pp. Unlock(pp, l, x)@t0 ==> #t0 = #t2)
                   & (All pp lpp #t0. Lock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t0 = #t1 | #t2 < #t0)
                   & (All pp lpp #t0. Unlock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t2 < #t0 | #t2 = #t0 )))
      | #t3<#t1 | #t1=#t3"
|]

-- | Restriction for Locking where no Unlock is necessary.
resLockingPOSNoUnlock :: String
resLockingPOSNoUnlock = [QQ.r|restriction locking:
"All p pp l x lp #t1 #t3. LockPOS(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>
        #t3<#t1 | #t1=#t3"
|]



-- | Restrictions for Locking and Unlocking in the pureState case.
resLockingPure ::  MonadThrow m => [SyntacticRestriction] -> m [SyntacticRestriction]
resLockingPure prev = do
  news <- mapM toEx [
    [QQ.r|restriction locking1:
         "All p l x #t1 pp lp #t2 #t3 . Lock(p,l,x)@t1 &  Lock(pp,lp,x)@t2
                     & Unlock(p,l,x)@t3 & not(#t1=#t2)
                   ==> (t2 < t1) | (t3 < t2)"
                   |] ,
      [QQ.r|restriction locking2:
           "All p l x #t1 pp lp #t2 #t3 . Lock(p,l,x)@t1 &  Unlock(pp,lp,x)@t2
           & Unlock(p,l,x)@t3 & not(#t2=#t3)
           ==> (t3 < t2) | (t2 < t1)"
           |]
      ]
  return $ news ++ prev
-- | Produce locking lemma for variable v by instantiating resLockingL
--  with (Un)Lock_pos instead of (Un)LockPOS, where pos is the variable id
--  of v.
resLocking :: MonadThrow m => Bool -> LVar -> m SyntacticRestriction
resLocking hasUnlock v =  do
    rest <- if hasUnlock then
              toEx resLockingPOS
            else
              toEx resLockingPOSNoUnlock
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
        mapFormula f r = r { _rstrFormula = f r._rstrFormula }
        mapName f r = r { _rstrName = f r._rstrName }

resEq :: String
resEq = [QQ.r|restriction predicate_eq:
"All #i a b. Pred_Eq(a,b)@i ==> a = b"
|]


resNotEq :: String
resNotEq = [QQ.r|restriction predicate_not_eq:
"All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)"
|]


resInEv :: String
resInEv = [QQ.r|restriction in_event:
"All x #t3. ChannelIn(x)@t3 ==> (Ex #t2. K(x)@t2 & #t2 < #t3
                                & (All #t1. Event()@t1  ==> #t1 < #t2 | #t3 < #t1)
                                & (All #t1 xp. K(xp)@t1 ==> #t1 < #t2 | #t1 = #t2 | #t3 < #t1))"
|]


-- | generate restrictions depending on options set (op) and the structure
-- of the process (anP)
baseRestr :: MonadThrow m => Process (ProcessAnnotation LVar) v -> Bool -> Bool -> [SyntacticRestriction] -> m [SyntacticRestriction]
baseRestr anP needsInEvRes hasAccountabilityLemmaWithControl prevRestr =
  let hardcoded_l =
       (if contains isLookup then
        if contains isDelete then
            [resSetIn,  resSetNotIn]
              else
            [resSetInNoDelete, resSetNotInNoDelete]
         else [])
        ++ addIf (contains isEq) [resEq, resNotEq]
        ++ addIf hasAccountabilityLemmaWithControl [resSingleSession]
        ++ addIf needsInEvRes [resInEv]
    in do
        hardcoded <- mapM toEx hardcoded_l
        lockingWithUnlock <- mapM (resLocking True) (List.nub $ getUnlockPositions anP)
        lockingOnlyLock   <- mapM (resLocking False) (getLockPositions anP List.\\ getUnlockPositions anP)
        return $ prevRestr
              ++ hardcoded
              ++ lockingWithUnlock
              ++ lockingOnlyLock
    where
        addIf phi list = if phi then list else []
        contains = processContains anP
        getLock p
            | (ProcessAction (Lock _) an@ProcessAnnotation{pureState=False} _) <- p, (Just (AnVar v)) <- lock an = [v] -- annotation is Maybe type
            | otherwise  = []
        getUnlock p
            | (ProcessAction (Unlock _) an@ProcessAnnotation{pureState=False} _) <- p, (Just (AnVar v)) <- unlock an = [v] -- annotation is Maybe type
            | otherwise  = []
        getLockPositions = pfoldMap getLock
        getUnlockPositions = pfoldMap getUnlock

        -- This is what SAPIC did
          -- @ (if op.accountability then [] else [res_single_session_l])
