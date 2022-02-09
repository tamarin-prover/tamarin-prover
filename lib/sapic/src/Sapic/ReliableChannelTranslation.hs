{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes   #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Transforms translation into translation that includes reliable channels.
module Sapic.ReliableChannelTranslation (
     reliableChannelTrans
   , reliableChannelInit
   , reliableChannelRestr
) where
import           Control.Monad.Catch
import           Data.Set              hiding (map)
import           Sapic.Annotation
import           Sapic.Basetranslation
import           Sapic.Exceptions
import           Sapic.Facts
import           Sapic.ProcessUtils
import qualified Text.RawString.QQ     as QQ
import           Theory
import           Theory.Sapic

-- | Init-rule that allows generating MessageIDSender and MessageIDReceiver facts, 
-- | for later consumption.
reliableChannelInit :: Monad m => AnProcess ann -> ([AnnotatedRule ann], Set LVar) -> m ([AnnotatedRule ann], Set LVar)
reliableChannelInit anP (initrules,initTx) = return (messageidrule : initrules, initTx)
  where
        messageidrule = AnnotatedRule (Just "MessageIDRule") anP (Right NoPosition)
                    [ Fr  $ varMID [] ] -- prem
                    []                -- act
                    [ MessageIDReceiver [], MessageIDSender [] ]
                    []
                    0

-- | Send and receive actions are modified to produce the necessary Send and Receive events.
reliableChannelTransAct :: MonadThrow m =>
                           TransFAct (m TranslationResultAct)
                           -> TransFAct (m TranslationResultAct)
reliableChannelTransAct tAct ac an p tx 
            | (ChIn (Just v) t) <- ac
            ,Lit (Con name) <- viewTerm v
            , sortOfName name == LSortPub
            , getNameId (nId name) == "c"
            = let tx' = (freeset v) `union` (freeset t) `union` tx in
              let ts  = fAppPair (v,t) in
              return $ ([ ([def_state, (In ts) ], [ChannelIn ts], [def_state1 tx'],[]) ],tx')
            | (ChOut (Just v) t) <- ac
            ,Lit (Con name) <- viewTerm v
            , sortOfName name == LSortPub
            , getNameId (nId name) == "c"
            = let tx' = (freeset v) `union` (freeset t) `union` tx in
              return $ ([ ([def_state, (In v) ], [ChannelIn v], [def_state1 tx', Out t],[]) ],tx')
            | (ChIn (Just r) t) <- ac
            ,Lit (Con name) <- viewTerm r
            , sortOfName name == LSortPub
            , getNameId (nId name) == "r"
            = let tx' = (freeset r) `union` (freeset t) `union` tx in
              return $ ([ ([def_state, In t, MessageIDReceiver p ], [Receive p t], [def_state1 tx'],[]) ],tx')
            | (ChOut (Just r) t) <- ac
            ,Lit (Con name) <- viewTerm r
            , sortOfName name == LSortPub
            , getNameId (nId name) == "r"
            = let tx' = (freeset r) `union` (freeset t) `union` tx in
              return $ ([ ([MessageIDSender p, def_state], [Send p t], [Out t, def_state1 tx'], []) ],tx')
            | (ChOut (Just _) _) <- ac = throwM ( ProcessNotWellformed WFReliable :: SapicException AnnotatedProcess)
            | (ChIn (Just _) _) <- ac = throwM ( ProcessNotWellformed WFReliable :: SapicException AnnotatedProcess)
            | (ChOut Nothing _) <- ac = throwM ( ProcessNotWellformed WFReliable :: SapicException AnnotatedProcess)
            | (ChIn Nothing _) <- ac = throwM ( ProcessNotWellformed WFReliable :: SapicException AnnotatedProcess)
                         -- raising exceptions is done with throwM. Add exceptions to Exceptions.hs
            | otherwise = tAct ac an p tx -- otherwise case: call tAct
            where
                def_state = State LState p tx
                def_state1 tx' = State LState (p++[1]) tx'
                freeset = fromList . frees

-- | The other parts of the translation remain unmodified.
reliableChannelTrans :: MonadThrow m =>
                          (a,
                           TransFAct (m TranslationResultAct),
                           c)
                 -> 
                          (a,
                           TransFAct (m TranslationResultAct),
                           c)
reliableChannelTrans (tNull,tAct,tComb) = (tNull, reliableChannelTransAct tAct,tComb)

resReliable :: String
resReliable = [QQ.r|restriction reliable: 
"All #i x y. Send(x,y)@i ==> Ex #j. Receive(x,y)@j & #i<#j"
|]

-- | Add restrictions that enforces Send-events to have Receive-events
reliableChannelRestr :: (MonadThrow m, MonadCatch m, Show ann) => AnProcess ann -> [SyntacticRestriction] -> m [SyntacticRestriction] 
reliableChannelRestr anP restrictions  = do
    res <- toEx resReliable
    return $ restrictions ++ addIf (processContains anP isReliableTrans) [res]
    where 
        addIf phi list = if phi then list else []
        isReliableTrans (ProcessAction ac _ _) 
            | (ChOut (Just tr) _) <- ac -- If there are only receives on the reliable channel, we do not need the restriction
            ,Lit (Con name) <- viewTerm tr
            , sortOfName name == LSortPub
            , getNameId (nId name) == "r" = True
            | otherwise = False
        isReliableTrans _ = False 
