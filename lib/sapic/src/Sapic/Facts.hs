{-# LANGUAGE RecordWildCards #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation specific fact types that are translated into LNFacts
module Sapic.Facts (
     TransAction(..)
   , TransFact(..)
   , SpecialPosition(..)
   , AnnotatedRule(..)
   , mapAct
   , StateKind(..)
   , isSemiState
   , isState
   , isNonSemiState
   , addVarToState
   , factToFact
   , actionToFact
   , actionToFactFormula
   , toRule
   , varMID
   , varProgress
   , msgVarProgress
   , propagateNames
) where
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
-- import Control.Monad.Catch
-- import Sapic.Exceptions
import Theory
-- import Theory.Text.Parser
import Theory.Sapic
import Theory.Sapic.Print
import Sapic.Annotation
-- import Theory.Model.Rule
-- import Theory.Model.Rule
-- import Data.Typeable
-- import Data.Text
import Data.Char
import Data.Bits
import qualified Data.Set as S
import Data.Color
-- import Control.Monad.Trans.FastFresh

-- | Facts that are used as actions
data TransAction =
  -- base translation
  InitEmpty
  --    storage
  | IsIn SapicTerm LVar
  | IsNotSet SapicTerm
  | InsertA SapicTerm SapicTerm
  | DeleteA SapicTerm
  -- locks
  | LockUnnamed SapicTerm LVar
  | LockNamed SapicTerm LVar
  | UnlockUnnamed SapicTerm LVar
  | UnlockNamed SapicTerm LVar
  -- in_event restriction
  | ChannelIn SapicTerm
  | EventEmpty
  -- support for msrs
  | TamarinAct LNFact
  -- predicate support
  | PredicateA LNFact
  | NegPredicateA LNFact
  -- progress translation
  | ProgressFrom ProcessPosition
  | ProgressTo ProcessPosition ProcessPosition
  -- reliable channels
  | Send ProcessPosition SapicTerm
  | Receive ProcessPosition SapicTerm
  -- to implement with accountability extension
  --- | InitId
  --- | StopId
  --- | EventId

-- | Facts that are used as premises and conclusions.
-- Most important one is the state, containing the variables currently
-- bound. Persistant variant for replication, and linear for all other
-- actions. Semistates are used in rules where a SAPIC step might take more
-- than one MSR step, i.e., messages over private channels.
data StateKind  = LState | PState | LSemiState | PSemiState
  deriving Eq
data TransFact =  Fr LVar | In SapicTerm
            | Out SapicTerm
            | Message SapicTerm SapicTerm
            | Ack SapicTerm SapicTerm
            | State StateKind ProcessPosition (S.Set LVar)
            | MessageIDSender ProcessPosition
            | MessageIDReceiver ProcessPosition
            | TamarinFact LNFact

data SpecialPosition = InitPosition -- initial position, is logically the predecessor of []
                     | NoPosition -- no real position, e.g., message id rule

-- | annotated rules know:
data AnnotatedRule ann = AnnotatedRule {
      processName  :: Maybe String    -- optional name for rules that are not bound to a process, e.g., Init
    , process      :: AnProcess ann   -- process this rules was generated for
    , position     :: Either ProcessPosition SpecialPosition -- position of this process in top-level process
    , prems        :: [TransFact]     -- Facts/actions to be translated
    , acts         :: [TransAction]
    , concs        :: [TransFact]
    , restr        :: [SyntacticLNFormula]
    , index        :: Int             -- Index to distinguish multiple rules originating from the same process
}

-- | applies function acting on rule taple on annotated rule.
mapAct :: (([TransFact], [TransAction], [TransFact],[SyntacticLNFormula])
           -> ([TransFact], [TransAction], [TransFact],[SyntacticLNFormula]))
          -> AnnotatedRule ann -> AnnotatedRule ann
mapAct f anrule = let (l',a',r',res') = f (prems anrule, acts anrule,
                                           concs anrule, restr anrule)
                  in
                  anrule { prems = l', acts = a', concs = r', restr = res' }

isSemiState :: StateKind -> Bool
isSemiState LState = False
isSemiState PState = False
isSemiState LSemiState = True
isSemiState PSemiState = True

isNonSemiState :: TransFact -> Bool
isNonSemiState (State kind _ _) = not $ isSemiState kind
isNonSemiState _ = False

isState :: TransFact -> Bool
isState (State _ _ _) = True
isState _ = False

addVarToState :: LVar -> TransFact -> TransFact
addVarToState v' (State kind pos vs)  = State kind pos (v' `S.insert` vs)
addVarToState _ x = x

multiplicity :: StateKind -> Multiplicity
multiplicity LState = Linear
multiplicity LSemiState = Linear
multiplicity PState = Persistent
multiplicity PSemiState = Persistent

-- | map f to the name of a fact
mapFactName :: (String -> String) -> Fact t -> Fact t
mapFactName f fact =  fact { factTag = f' (factTag fact) }
    where f' (ProtoFact m s i) = ProtoFact m (f s) i
          f' ft = ft

-- Optimisation: have a diffent fact name for every (unique) locking variable
lockFactName :: LVar -> String
lockFactName v = "Lock_"++ show (lvarIdx v)

unlockFactName :: LVar -> String
unlockFactName v = "Unlock_" ++ show (lvarIdx v)

lockPubTerm :: LVar -> NTerm v
lockPubTerm = pubTerm . show . lvarIdx

varNameProgress :: ProcessPosition -> String
varNameProgress p = "prog_" ++ prettyPosition p

varProgress :: ProcessPosition -> LVar
varProgress p = LVar n s i
    where n = varNameProgress p
          s = LSortFresh
          i = 0

msgVarProgress :: ProcessPosition -> LVar
msgVarProgress p = LVar n s i
    where n = varNameProgress p
          s = LSortMsg
          i = 0

varMsgId :: ProcessPosition -> LVar
varMsgId p = LVar n s i
    where n = "mid_" ++ prettyPosition p
          s = LSortFresh
          i = 0

-- actionToFact :: TransAction -> Fact t
actionToFact :: TransAction -> Fact (VTerm Name LVar)
actionToFact InitEmpty = protoFact Linear "Init" []
  --- | Not implemented yet: progress
  --- | StopId
  --- | EventEmpty
  --- | EventId
actionToFact (Send p t) = protoFact Linear "Send" [varTerm $ varMsgId p ,t]
actionToFact (Receive p t) = protoFact Linear "Receive" [varTerm $ varMsgId p ,t]
actionToFact (IsIn t v)   =  protoFact Linear "IsIn" [t,varTerm v]
actionToFact (IsNotSet t )   =  protoFact Linear "IsNotSet" [t]
actionToFact (InsertA t1 t2)   =  protoFact Linear "Insert" [t1,t2]
actionToFact (DeleteA t )   =  protoFact Linear "Delete" [t]
actionToFact (ChannelIn t)   =  protoFact Linear "ChannelIn" [t]
actionToFact (EventEmpty)   =   protoFact Linear "Event" []
actionToFact (PredicateA f)   =  mapFactName (\s -> "Pred_" ++ s) f
actionToFact (NegPredicateA f)   =  mapFactName (\s -> "Pred_Not_" ++ s) f
actionToFact (LockNamed t v)   = protoFact Linear (lockFactName v) [lockPubTerm v,varTerm v, t ]
actionToFact (LockUnnamed t v)   = protoFact Linear "Lock" [lockPubTerm v, varTerm v, t ]
actionToFact (UnlockNamed t v) = protoFact Linear (unlockFactName v) [lockPubTerm v,varTerm v,t]
actionToFact (UnlockUnnamed t v) = protoFact Linear "Unlock" [lockPubTerm v,varTerm v,t]
actionToFact (ProgressFrom p) = protoFact Linear ("ProgressFrom_"++prettyPosition p) [varTerm $ varProgress p]
actionToFact (ProgressTo p pf) = protoFact Linear ("ProgressTo_"++prettyPosition p) $ [varTerm $ varProgress pf]
actionToFact (TamarinAct f) = f

toFreeMsgVariable :: LVar -> BVar LVar
toFreeMsgVariable (LVar name LSortFresh id') = Free $ LVar name LSortMsg id'
toFreeMsgVariable v = Free $ v

actionToFactFormula :: TransAction -> Fact (Term (Lit Name (BVar LVar)))
actionToFactFormula = fmap (fmap $ fmap toFreeMsgVariable) . actionToFact

-- | Term with variable for message id. Uniqueness ensured by process position.
varMID :: ProcessPosition -> LVar
varMID p = LVar n s i
    where n = "mid_" ++ prettyPosition p
          s = LSortFresh
          i = 0 -- This is the message index.
                -- We could also compute it from the position as before,
                -- but I don't see an advantage (yet)

factToFact :: TransFact -> Fact SapicTerm
factToFact (Fr v) = freshFact $ varTerm (v)
factToFact (In t) = inFact t
factToFact (Out t) = outFact t
factToFact (Message t t') = protoFact Linear "Message" [t, t']
factToFact (Ack t t') = protoFact Linear "Ack" [t, t']
factToFact (MessageIDSender p) = protoFact Linear "MID_Sender" [ varTerm $ varMID p ]
factToFact (MessageIDReceiver p) = protoFact Linear "MID_Receiver" [ varTerm$ varMID p ]
factToFact (State kind p vars) = protoFact (multiplicity kind) (name kind ++ "_" ++ prettyPosition p) ts
    where
        name k = if isSemiState k then "Semistate" else "State"
        ts = map varTerm (S.toList vars)
factToFact (TamarinFact f) = f

prettyEitherPositionOrSpecial:: Either ProcessPosition SpecialPosition -> String
prettyEitherPositionOrSpecial (Left pos) = prettyPosition pos
prettyEitherPositionOrSpecial (Right InitPosition) = "Init"
prettyEitherPositionOrSpecial (Right NoPosition) = ""

getTopLevelName :: (GoodAnnotation an) => AnProcess an -> [String]
getTopLevelName (ProcessNull ann) = getProcessNames ann
getTopLevelName (ProcessComb _ ann _ _) = getProcessNames ann
getTopLevelName (ProcessAction _ ann _) = getProcessNames ann

propagateNames :: (GoodAnnotation ann) => AnProcess ann -> AnProcess ann
propagateNames = propagate' []
    where
      propagate' n (ProcessComb c an pl pr) = ProcessComb c
                                                (setProcessNames (n ++ getProcessNames an) an)
                                                (propagate' (n ++ getProcessNames an) pl)
                                                (propagate' (n ++ getProcessNames an) pr)
      propagate' n (ProcessAction a an p) = ProcessAction a
                                                (setProcessNames (n ++ getProcessNames an) an)
                                                (propagate' (n ++ getProcessNames an) p)
      propagate' n (ProcessNull an) = ProcessNull (setProcessNames (n ++ getProcessNames an) an)

crc32 :: String -> Int
crc32 s = foldl iter 0xffffffff (map ord s)
    where
        inner c = (c `shiftR` 1) `xor` (0xedb88329 .&. (-(c .&. 1)))
        iter c m = iterate inner (c `xor` m) !! 8

interpolate :: (Fractional t, Ord t) => HSV t -> HSV t -> t -> HSV t
interpolate (HSV h1 s1 v1) (HSV h2 s2 v2) a = HSV h' s' v'
      where
        h' = (h2 - h1) * a + h1
        s' = (s2 - s1) * a + s1
        v' = (v2 - v1) * a + v1

colorHash :: (Fractional t, Ord t) => String -> RGB t
colorHash s = RGB r g b
      where
        nthByte x n = (x `shiftR` (8*n)) .&. 0xff
        [r,g,b] = map ((/255) . fromIntegral . nthByte (crc32 s)) [0,1,2]

-- Computes a color for a list of strings by first computing
-- the CRC32 checksum of each string and then interpolating the
-- colors with an exponentionally decaying threshold (2^(-i)).
-- The interpolation is performed on colors in HSV representation.
-- To avoid to bright, dark, or saturated colors, the saturation
-- and luminance of the final color is normalized to to 0.5.
colorForProcessName :: [String] -> RGB Rational
colorForProcessName [] = RGB 255 255 255
colorForProcessName names = hsvToRGB $ normalize $ fst $ foldl f (head palette, 0::Int) (tail palette)
      where
        palette = map (rgbToHSV . colorHash) names
        normalize (HSV h _ _) = HSV h 0.5 0.5
        f (acc, i) v = (interpolate acc v (2^^(-i)), i+1)

toRule :: GoodAnnotation ann => AnnotatedRule ann -> Rule ProtoRuleEInfo
toRule AnnotatedRule{..} = -- this is a Record Wildcard
          Rule (ProtoRuleEInfo (StandRule name ) attr restr) l r a (newVariables l r)
          where
            name = case processName of
                Just s -> s
                Nothing -> 
                         unNull (stripNonAlphanumerical (prettySapicTopLevel process))
                         ++ "_" ++ show index ++ "_"
                         ++ prettyEitherPositionOrSpecial position
            attr = [ RuleColor $ colorForProcessName $ getTopLevelName process
                   , Process $ toProcess process]
            l = map factToFact prems
            a = map actionToFact acts
            r = map factToFact concs
            stripNonAlphanumerical = filter isAlpha
            unNull s = if null s then "p" else s

