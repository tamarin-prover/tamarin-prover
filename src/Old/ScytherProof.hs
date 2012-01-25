-- |
-- Copyright   : (c) 2010 Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Importing theory (items) from scyther-proof's theory representation.
module Theory.Import.ScytherProof where

import Data.Maybe
import Data.List
import qualified Data.Set as S
import Data.Foldable (foldMap)

import Control.Basics
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Bind

import Extension.Prelude

import qualified Scyther.Message as S
import qualified Scyther.Protocol as S
import qualified Scyther.Equalities as S
import qualified Scyther.Formula as S
import qualified Scyther.Facts as S hiding (threadRole)
import qualified Scyther.Sequent as S
import qualified Scyther.Theory.Parser as S hiding (protocol)

import Theory.Rule
import Theory.Formula


------------------------------------------------------------------------------
-- Monadic importing infrastructure for defining free operators
------------------------------------------------------------------------------

-- | Import a pattern.
--
-- WARNING: This import may yield to clashes between agent variables, nonces, 
-- or message variables, if they have the same name. However, this cannot occur
-- in protocols parsed from files, as their syntax does not allow it.
importPattern :: S.Pattern 
              -> (LTerm, [(LTerm, (S.Pattern, Maybe LFact))]) 
                 -- ^ Term plus variables together with their original pattern
                 -- and their facts constraints.
importPattern pt0 = 
    second (sortednubOn fst) $ runWriter (go pt0)
  where
    mkVar s v = varTerm (LVar (S.getId v) s 0)

    go :: S.Pattern -> Writer [(LTerm, (S.Pattern, Maybe LFact))] LTerm
    go (S.PConst c) = pure $ pubTerm $ S.getId c

    go p@(S.PFresh f) = 
        tell [(t, (p, Just (freshFact t)))] *> pure t
      where
        t = mkVar LSortFresh f

    go p@(S.PAVar a) = 
        tell [(t, (p, Nothing))] *> pure t
      where
        t = mkVar LSortPub a

    go p@(S.PMVar v) = 
        tell [(t, (p, Nothing))] *> pure t
      where
        t = mkVar LSortMsg v

    go p@(S.PHash   p1    ) = 
        fromMaybe (Op1 Hash <$> go p1) $ 
        msum
          -- here we exploit the MonadPlus instance of Maybe to compute the
          -- Writer that returns the pattern.
          [ do S.destMultIdentityPat p
               return (pure Unit)
          , do (x,y) <- S.destMultPat p
               return (Mult <$> go x <*> go y)
          , do (x,y) <- S.destExpPat p
               return (Exp <$> go x <*> go y)
          , do x <- S.destLTSPat p
               return (Op1 Lts <$> go x)
          ] 

    go (S.PTup    p1 p2)  = Op2 Pair <$> go p1 <*> go p2
    go (S.PSymK   p1 p2)  = Op1 Lts <$> (Op2 Pair <$> go p1 <*> go p2)
    go (S.PAsymPK p1    ) = (Op1 Pk . Op1 Lts) <$> go p1
    go (S.PAsymSK p1    ) = (Op1 Sk . Op1 Lts) <$> go p1

    go (S.PEnc    p1 p2@(S.PAsymPK _)) = Op2 EncA <$> go p2 <*> go p1
    go (S.PEnc    p1 p2@(S.PAsymSK _)) = Op2 Sign <$> go p2 <*> go p1
    go (S.PEnc    p1 p2              ) = Op2 EncS <$> go p2 <*> go p1

    go (S.PSign   p1 p2) = Op2 Pair <$> t1 <*> (Op2 Sign <$> go p2 <*> t1)
      where
        t1 = go p1

    go t = error $ "importPattern: not supported '" ++ show t ++ "'"

-- | Convert a role to its corresponding rules.
importRole :: String     -- ^ Prefix for rules and state facts.
           -> S.Role 
           -> ([ProtoRuleE], [S.Pattern])
importRole prefix role = 
    case runState (mapM importStep $ S.roleSteps role) (Nothing, [], []) of
      (rules, (_, _, ps)) -> (rules, ps)
  where
    importStep (S.Send l pt) = mkRule l pt (const []) (return . outFact)
    importStep (S.Recv l pt) = mkRule l pt (return . inFact) (const [])
    
    mkRule l pt prems concs = do
        (prevThreadFact, vs, ps) <- get
        let (t, ptVarFacts) = importPattern pt
            newVarFacts     = filter ((`notElem` vs) . fst) ptVarFacts
            vs'             = vs ++ map fst         newVarFacts
            ps'             = ps ++ map (fst . snd) newVarFacts
            threadFact      = protoFact ruName vs'
            ruName          = prefix ++ "_" ++ S.roleName role ++ "_" ++ S.getLabel l
        put (Just threadFact, vs', ps')
        return $ Rule (ProtoRuleEInfo (StandRule ruName) (TypingE []))
            (maybe id (:) prevThreadFact $ mapMaybe (snd . snd) newVarFacts ++ prems t)
            (threadFact : concs t)


-- | Convert a protocol to its corresponding rules.
importProtocol :: S.Protocol -> [ProtoRuleE]
importProtocol p = 
    concatMap (fst . importRole (S.protoName p)) (S.protoRoles p)


------------------------------------------------------------------------------
-- Import sequents
------------------------------------------------------------------------------

type BLTerm = NTerm BLVar
type LFormulaImport = BindT S.Message LVar Fresh

bvarTerm :: LVar -> BLTerm
bvarTerm = varTerm . Free

importMessage :: S.Message -> LFormulaImport BLTerm
importMessage = 
    go
  where
    lidId = S.getId . S.lidId
    importLVar s = importBinding (`LVar` s)

    go   (S.MConst c) = pure $ pubTerm $ S.getId c
    go m@(S.MFresh f) = bvarTerm <$> importLVar LSortFresh m (lidId $ S.getFresh f)
    go m@(S.MMVar v)  = bvarTerm <$> importLVar LSortMsg   m (lidId $ S.getMVar v)
    go m@(S.MAgent _) = bvarTerm <$> importLVar LSortPub   m "a"
    go m@(S.MAVar a)  = bvarTerm <$> importLVar LSortPub   m (lidId $ S.getAVar a)

    go (S.MHash   p1   ) = Op1 Hash <$> go p1
    go (S.MTup    p1 p2) = Op2 Pair <$> go p1 <*> go p2
    go (S.MSymK   p1 p2) = Op1 Lts <$> (Op2 Pair <$> go p1 <*> go p2)
    go (S.MAsymPK p1   ) = (Op1 Pk . Op1 Lts) <$> go p1
    go (S.MAsymSK p1   ) = (Op1 Sk . Op1 Lts) <$> go p1

    go (S.MEnc    p1 p2@(S.MAsymPK _)) = Op2 EncA <$> go p2 <*> go p1
    go (S.MEnc    p1 p2@(S.MAsymSK _)) = Op2 Sign <$> go p2 <*> go p1
    go (S.MEnc    p1 p2              ) = Op2 EncS <$> go p2 <*> go p1
    go (S.MInvKey _                  ) = error "importMessage: invKey not supported"
    go t = error $ "importMessage: not supported '" ++ show t ++ "'"

importEvent :: S.Event -> LFormulaImport (LVar, LFormula)
importEvent (S.Learn m) = do
    vi <- freshLVar "l" LSortNode 
    mi <- importMessage m
    return (vi, Ato (Provides (Free vi) (inFact mi)))
importEvent (S.Step _ _) = do
    error "importEvent: Step: not yet implemented"
    {-
    vi <- freshLVar "s"
    return (vi, ltrue)
    -}

-- | Convert an equality to a message equality if possible.
anyEqToMsgEq :: S.AnyEq -> Maybe (S.Message, S.Message)
anyEqToMsgEq eq0 = case eq0 of
    S.AgentEq eq    -> return $ S.agentEqToMsgEq eq
    S.AVarEq  (l,r) -> return $ (S.MAVar l, S.MAVar r)
    S.MVarEq  eq    -> return $ S.mvarEqToMsgEq eq
    S.MsgEq   eq    -> return $ eq
    _               -> mzero

importAnyEq :: S.AnyEq -> ErrorT String LFormulaImport LFormula
importAnyEq eq0 = do
    (l,r) <- maybe (throwError "importAnyEq: unsupported equality type")
                   return
                   (anyEqToMsgEq eq0)
    Ato <$> (EqE <$> lift (importMessage l) <*> lift (importMessage r))

hinted :: ((String, LSort) -> LVar -> a) -> LVar -> a
hinted f v@(LVar n s _) = f (n,s) v

importAtom :: S.Atom -> ErrorT String LFormulaImport LFormula
importAtom S.AFalse            = pure $ lfalse
importAtom (S.AEq eq)          = importAnyEq eq
importAtom (S.AEv e)           = do
    (v, p) <- lift $ importEvent e
    return $ hinted exists v p
importAtom (S.AEvOrd (e1, e2)) = do
    (v1, p1) <- lift $ importEvent e1
    (v2, p2) <- lift $ importEvent e2
    return $ hinted exists v1 $ hinted exists v2 $
        foldr1 (.&&.) [p1, Ato (Path (Free v1) (Free v2)), p2]
importAtom (S.ACompr a)        = Not <$> importAtom (S.AUncompr a)
importAtom (S.AUncompr a)      = do 
    vi <- lift $ freshLVar "c" LSortNode
    ai <- lift $ importMessage a
    return $ hinted forall vi (Not (Ato (Provides (Free vi) (ltsrFact ai))))

importAtom (S.AHasType _ _) = pure $ ltrue -- error "importAtom: `hasType' not supported"
importAtom (S.ATyping _)    = pure $ ltrue -- error "importAtom: `typing' not supported"
importAtom (S.AReachable _) = pure $ ltrue -- error "importAtom: `reachable state' not supported" 

importFacts :: S.Facts -> ErrorT String LFormulaImport LFormula
importFacts facts =
    foldr1 (.&&.) <$> (errorFree1 $ 
        (map defineStep fatoms) ++
        (map importAtom fatoms))
  where
    fatoms = S.toAtoms facts
    steps  = foldMap requiredStepsAtom fatoms $ S.eqsToMapping facts
    proto  = S.protoName $ S.protocol facts

    defineStep (S.AEq (S.TIDRoleEq (tid, role)))
      | null prefix = throwError "importFacts: no step of this role required"
      | otherwise   = do
          vi <- lift $ freshLVar "s" LSortNode
          psi <- lift $ mapM (importMessage . S.inst tid) ps
          let vsi = map Lit $ concatMap lits psi -- remove `agent' constructors
          return $ Ato (Provides (Free vi) (protoFact factName vsi))
      where
        factName = proto ++ "_" ++ S.roleName role 
                         ++ "_" ++ S.stepLabel (last prefix)
        ps     = snd $ importRole proto (S.Role (S.roleName role) prefix)
        prefix = reverse $ dropWhile (\s -> (tid,s) `notElem` steps) 
                         $ reverse $ S.roleSteps role

    defineStep _ = throwError "defineStep: nothing to do for this atom."

importFormula :: S.Formula -> ErrorT String LFormulaImport LFormula
importFormula (S.FAtom a)     = importAtom a
importFormula (S.FExists _ f) = importFormula f -- FIXME: handle binding correctly
importFormula f@(S.FConj _ _) = 
    foldr1 (.&&.) <$> (errorFree1 (map importFormula $ S.conjuncts f))
    

importSequent :: S.Sequent -> LFormula
importSequent se = (`evalFresh` nothingUsed) $ (`evalBindT` noBindings) $
    (.==>.) <$> prems <*> concs
  where
    prems = either (const ltrue) id <$> (runErrorT $ importFacts $ S.sePrem se)
    concs = either (const lfalse) id <$> (runErrorT $ importFormula $ S.seConcl se)

-- | Gather the steps required for the given message to have all variables
-- defined.
requiredStepsMsg :: S.Message -> S.Mapping -> [(S.TID, S.RoleStep)]
requiredStepsMsg m0 =
    -- we exploit that: Monoid b => Monoid (a -> b)
    foldMap firstUse $ S.submessages m0
  where
    firstUse m mapping = 
          case S.msgTIDs m of
            [tid] -> case S.threadRole tid (S.getMappingEqs mapping) of
                       Nothing   -> mempty
                       Just role -> firstOcc tid role
            _     -> mempty
        where
          firstOcc tid role = case find (occursScytherFree tid) $ S.roleSteps role of
              Just s  -> pure (tid, s)
              Nothing -> mempty
          occursScytherFree tid s = 
              m `S.member` S.submessages (S.inst tid $ S.stepPat s)


-- | Gather the steps required for the given atom to have all variables
-- defined.
requiredStepsAtom :: S.Atom -> S.Mapping -> [(S.TID, S.RoleStep)]
requiredStepsAtom (S.AEq eq) = 
    maybe mempty combine . anyEqToMsgEq $ eq
  where
    combine (l,r) = requiredStepsMsg l `mappend` requiredStepsMsg r

requiredStepsAtom (S.ACompr a)           = requiredStepsMsg a
requiredStepsAtom (S.AUncompr a)         = requiredStepsMsg a
requiredStepsAtom (S.AEv (S.Step tid s)) = pure $ pure (tid,s)
requiredStepsAtom (S.AEvOrd (e1, e2)  )  =
    foldMap (requiredStepsAtom . S.AEv) [e1,e2]

requiredStepsAtom _                      = mempty


