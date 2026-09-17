{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable       #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE PatternGuards       #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Data types for SAPIC processes in theories
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Theory.Sapic.Process (
    -- types
    Process(..)
    , ProcessCombinator(..)
    , SapicAction(..)
    , LSapicAction
    , LProcessCombinator
    , LProcess
    -- utitlities
    , foldProcess
    , foldMProcess
    , traverseTermsAction
    , traverseTermsComb
    , pfoldMap
    , mapTerms
    , mapTermsAction
    , mapTermsComb
    , applyM
    , actionBinders
    , actionBinderDeclarations
    , combinatorBinderDeclarations
    , combinatorBinders
    , renameActionBinders
    , renameCombinatorBinders
    , applyProcessSubstAvoiding
    , expandProcessCall
    , processAddAnnotation
    , varsProc
    , varsProcWithAnnotations
    -- pretty printing
    , prettySapic'
    , prettySapicAction'
    , prettySapicComb
    , prettySapicTopLevel'
    -- exception type for lets
    , LetExceptions (..)
    , prettyLetExceptions
    ,traverseProcess
    ,processGetAnnotation) where

import Data.Binary
import Data.Data
import Data.Set hiding (map, union, (\\))
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)
import Control.Parallel.Strategies
import Term.Substitution
import Theory.Text.Pretty
import Data.List
import Data.Maybe (isJust)
import qualified Data.Foldable as F
import Control.Monad.Catch
import Theory.Sapic.Term
import Theory.Sapic.Substitution
import Theory.Sapic.Annotation
import Theory.Sapic.Pattern ( unextractMatchingVariables )

-- | Actions are parts of the process that maybe connected with ";"
data SapicAction v =
                   Rep
                 | New v
                 | ChIn { inChan:: Maybe (SapicNTerm v), inMsg::SapicNTerm v, inMatch::Set v}
                 | ChOut (Maybe (SapicNTerm v)) (SapicNTerm v)
                 | Insert (SapicNTerm v) (SapicNTerm v)
                 | Delete (SapicNTerm v)
                 | Lock (SapicNTerm v)
                 | Unlock (SapicNTerm v)
                 | Event (SapicNFact v)
                 | ProcessCall String [SapicNTerm v]
                 | MSR { iPrems :: [SapicNFact v]
                       , iActs :: [SapicNFact v]
                       , iConcs :: [SapicNFact v]
                       , iRest :: [SapicNFormula v]
                       , iMatch :: Set v}
            deriving (Foldable)

deriving instance (Show v) => Show (SapicAction v)
deriving instance (Eq v) => Eq (SapicAction v)
deriving instance (Ord v) => Ord (SapicAction v)
deriving instance (Generic v) => Generic (SapicAction v)
deriving instance (NFData v, Generic v) => NFData (SapicAction v)
deriving instance (Binary v, Generic v) => Binary (SapicAction v)
deriving instance (Data v, Generic v, Ord v) => Data (SapicAction v)

-- | When the process tree splits, it is connected with one of these connectives
data ProcessCombinator v = Parallel | NDC | Cond (SapicNFormula v)
        | CondEq (SapicNTerm v) (SapicNTerm v) | Lookup (SapicNTerm v) v
        | Let { letLeft :: SapicNTerm v, letRight :: SapicNTerm v, letMatch :: Set v}
            deriving (Foldable)

deriving instance (Show v) => Show (ProcessCombinator v)
deriving instance (Eq v) => Eq (ProcessCombinator v)
deriving instance (Ord v) => Ord (ProcessCombinator v)
deriving instance (Generic v) => Generic (ProcessCombinator v)
deriving instance (NFData v, Generic v) => NFData (ProcessCombinator v)
deriving instance (Binary v, Generic v) => Binary (ProcessCombinator v)
deriving instance (Data v, Generic v, Ord v) => Data (ProcessCombinator v)

-- | The process tree is terminated with null processes, and either splits
-- (parallel and other combinators) or describes a sequence of actions with
-- only one daughter
data Process ann v =
        ProcessNull ann
    |   ProcessComb (ProcessCombinator v) ann (Process ann v) (Process ann v)
    |   ProcessAction (SapicAction v) ann (Process ann v)
     deriving(Generic, Data)

type LSapicAction = SapicAction SapicLVar
type LProcessCombinator = ProcessCombinator SapicLVar
type LProcess ann =  Process ann SapicLVar

deriving instance (Eq ann, Eq v) => Eq (Process ann v)
deriving instance (Ord ann, Ord v) => Ord (Process ann v)
deriving instance (NFData ann) => NFData (LProcess ann)
deriving instance (Binary ann) => Binary (LProcess ann)
deriving instance (Show ann, Show v) => Show (Process ann v)
-- deriving instance Functor (Process ann)
deriving instance Foldable (Process ann)

-- | map over a process: @mapTerms ft ff fv@ applies @ft@ to terms, @ff@ to formulas and @fv@ to variables
mapTerms :: (Ord v) => (SapicNTerm t -> SapicNTerm v)
            -> (SapicNFormula t -> SapicNFormula v)
            -> (t -> v)
            -> Process ann t
            -> Process ann v
mapTerms _ _  _  (ProcessNull ann)  = ProcessNull ann
mapTerms f ff fv (ProcessAction ac ann p') = ProcessAction (mapTermsAction f ff fv ac) ann (mT p')
    where mT = mapTerms f ff fv
mapTerms f ff fv (ProcessComb c ann pl pr) = ProcessComb (mapTermsComb f ff fv c) ann (mT pl) (mT pr)
    where mT = mapTerms f ff fv

mapTermsAction :: (Ord v) => (SapicNTerm t -> SapicNTerm v)
                  -> (SapicNFormula t -> SapicNFormula v)
                  -> (t -> v)
                  -> SapicAction t
                  -> SapicAction v
mapTermsAction f ff fv ac
        | (New v) <- ac        = New (fv v)
        | (ChIn  mt t mv) <- ac   = ChIn (fmap f mt) (f t) (Set.map fv mv)
        | (ChOut mt t) <- ac   = ChOut (fmap f mt) (f t)
        | (Insert t1 t2) <- ac = Insert (f t1) (f t2)
        | (Delete t) <- ac     = Delete (f t)
        | (Lock t) <- ac       = Lock (f t)
        | (Unlock t) <- ac     = Unlock (f t)
        | (Event fa) <- ac      = Event (fmap f fa)
        | ProcessCall s ts <- ac = ProcessCall s (map f ts)
        | (MSR l a r rest mv) <- ac  = MSR (f2mapf l) (f2mapf a) (f2mapf r) (fmap ff rest) (Set.map fv mv)
        | Rep <- ac            = Rep
            where f2mapf = fmap $ fmap f

mapTermsComb :: (Ord v) => (SapicNTerm t -> SapicNTerm v)
                -> (SapicNFormula t -> SapicNFormula v)
                -> (t -> v)
                -> ProcessCombinator t
                -> ProcessCombinator v
mapTermsComb f ff fv c
        | (Cond fa) <- c = Cond $ ff fa
        | (CondEq t1 t2) <- c = CondEq (f t1) (f t2)
        | (Let t1 t2 vs) <- c  = Let (f t1) (f t2) (Set.map fv vs)
        | (Lookup t v) <- c = Lookup (f t) (fv v)
        | Parallel <- c = Parallel
        | NDC    <- c   = NDC

-- | fold a process: apply @fNull@, @fAct@, @fComb@ on accumulator and action,
-- annotation and nothing/action/combinator to obtain new accumulator to apply
-- to subprocess. @gAct@ and @gComb@ reconstruct result, e.g., process from
-- accumulator and result of subprocess(es). @fNulL@ directly outputs result.
foldProcess :: (t1 -> t2 -> t3)
               -> (t1 -> t2 -> SapicAction v -> t1)
               -> (t1 -> t2 -> ProcessCombinator v -> t1)
               -> (t1 -> t2 -> t3 -> SapicAction v -> t3)
               -> (t1 -> t2 -> t3 -> t3 -> ProcessCombinator v -> t3)
               -> t1
               -> Process t2 v
               -> t3
foldProcess fNull fAct fComb gAct gComb a p
    | (ProcessNull ann) <- p = fNull a ann
    | (ProcessAction ac ann p') <- p =
            let a' = fAct a ann ac -- 1. update accumulator
                r = foldProcess fNull fAct fComb gAct gComb a' p'  -- 2. process subtree with updated acculator
            in
               gAct a' ann r ac -- 3. reconstruct result from accumulator and subtree's result
    | (ProcessComb c ann pl pr) <- p =
            let a' = fComb a ann c
                rl = foldProcess fNull fAct fComb gAct gComb a' pl
                rr = foldProcess fNull fAct fComb gAct gComb a' pr
            in
                gComb a' ann rl rr c

foldMProcess :: Monad m =>
    (t1 -> t2 -> m t3)
    -> (t1 -> t2 -> SapicAction v -> m t1)
    -> (t1 -> t2 -> ProcessCombinator v -> m t1)
    -> (t1 -> SapicAction v -> t2 -> t3 -> m t3)
    -> (t1 -> ProcessCombinator v -> t2 -> t3 -> t3 -> m t3)
    -> t1
    -> Process t2 v
    -> m t3
foldMProcess fNull fAct fComb gAct gComb a p
    | (ProcessNull ann) <- p = fNull a ann
    | (ProcessAction ac ann p') <- p = do
            a' <- fAct a ann ac -- 1. update accumulator
            p''<- foldMProcess fNull fAct fComb gAct gComb a' p'  -- 2. process subtree with updated acculator
            gAct a' ac ann p'' -- 3. reconstruct result from accumulator and subtree's result
    | (ProcessComb c ann pl pr) <- p = do
            a' <- fComb a ann c
            rl <- foldMProcess fNull fAct fComb gAct gComb a' pl
            rr <- foldMProcess fNull fAct fComb gAct gComb a' pr
            gComb a' c ann rl rr

-- | Traverses process. Simplified variant of @foldMProcces@ that avoids
-- accumulator (use state monad for that.)
traverseProcess :: Monad m => (t1 -> m t2) -> (t1 -> SapicAction v -> m ()) ->
    (t1 -> ProcessCombinator v -> m ()) -> (SapicAction v -> t1 -> t2 -> m t2) ->
    (ProcessCombinator v -> t1 -> t2 -> t2 -> m t2) -> Process t1 v -> m t2
traverseProcess fNull fAct fComb gAct gComb p
    | (ProcessNull ann) <- p = fNull ann
    | (ProcessAction ac ann p') <- p = do
            fAct ann ac -- 1. act on current process, potentially updating state
            p''<- traverseProcess fNull fAct fComb gAct gComb p'  -- 2. process subtree with updated trace
            gAct ac ann p'' -- 3. reconstruct result from state and subtree's result
    | (ProcessComb c ann pl pr) <- p = do
            fComb ann c
            rl <- traverseProcess fNull fAct fComb gAct gComb pl
            rr <- traverseProcess fNull fAct fComb gAct gComb pr
            gComb c ann rl rr

-- | Traverse a set. We need this because the typeclass Traverse does not apply to sets,
-- because that would require Functor to apply, which is in contradiction to
-- Data.Set requiring it's elements to have Ord.
traverseSet :: (Eq a1, Applicative f) => (a2 -> f a1) -> Set a2 -> f (Set a1)
traverseSet f vs = fromAscList <$> traverse f (toAscList vs)

traverseTermsAction :: (Eq v, Applicative f) =>
    (SapicNTerm t -> f (SapicNTerm v))
    -> (SapicNFormula t -> f (SapicNFormula v))
    -> (t -> f v)
    -> SapicAction t
    -> f (SapicAction v)
traverseTermsAction ft ff fv ac
        --  | (New v) <- ac = (New . termVar') <$> ft (varTerm v)
        | (New v) <- ac = New <$> fv v
        | (ChIn  mt t vs) <- ac   = ChIn <$> traverse ft mt <*> ft t <*> traverseSet fv vs
        | (ChOut mt t) <- ac   = ChOut<$> traverse ft mt <*> ft t
        | (Insert t1 t2) <- ac = Insert <$> ft t1 <*> ft t2
        | (Delete t) <- ac     = Delete <$> ft t
        | (Lock t) <- ac       = Lock   <$> ft t
        | (Unlock t) <- ac     = Unlock <$> ft t
        | (Event fa) <- ac      = Event <$> traverse ft fa
        | (MSR l a r rest mv) <- ac  =
                    MSR
                    <$>
                         t2f l
                     <*> t2f a
                     <*> t2f r
                     <*> traverse ff rest
                     <*> traverseSet fv mv
        | Rep <- ac            = pure Rep
        | ProcessCall s ts <- ac = ProcessCall s <$> traverse ft ts
            where t2f = traverse (traverse ft)

traverseTermsComb :: (Applicative f, Eq v) =>
    (SapicNTerm a2 -> f (SapicNTerm v))
    -> (SapicNFormula a2 -> f (SapicNFormula v))
    -> (a2 -> f v)
    -> ProcessCombinator a2
    -> f (ProcessCombinator v)
traverseTermsComb ft ff fv c
        | (Cond fa)      <- c = Cond <$> ff fa
        | (CondEq t1 t2) <- c = CondEq <$> ft t1 <*> ft t2
        | (Let t1 t2 vs) <- c    = Let <$> ft t1 <*> ft t2 <*> traverseSet fv vs
        | (Lookup t v)   <- c = Lookup <$> ft t <*> fv v
        | Parallel       <- c = pure Parallel
        | NDC            <- c = pure NDC

-- | folding on the process tree, used, e.g., for printing
pfoldMap :: Monoid a => (Process ann v -> a) -> Process ann v -> a
pfoldMap f (ProcessNull an) = f (ProcessNull an)
pfoldMap f (ProcessComb c an pl pr)  =
        pfoldMap f pl
        `mappend`
        f (ProcessComb c an pl pr)
        `mappend`
        pfoldMap f pr
pfoldMap f (ProcessAction a an p)   =
        f (ProcessAction a an p)
        `mappend`
        pfoldMap f p

-------------------------
-- Applying substitutions ( no error messages )
-------------------------

-- | extracts the variables from all resulting terms. E.g., when we try to match
-- x and y, and substitute x-> <v1,v2> and y->v3, we now match v1,v2 and v3.
applyMatchVars :: IsVar a => Subst c a -> Set a -> Set a
-- applyMatchVars = applyMatchVars' id
applyMatchVars subst = fromList . concatMap extractVars . toList
        where
            extractVars v = -- all variables that are bound by sigma(v), or [v] if undef
                maybe [v] varsVTerm (imageOf subst v)

-- | Same as applyMatchVars, but uses f to perform the substitution, for generality
-- f is intended to be `apply subst`, but we want to avoid having the type constraints here.
applyMatchVars' :: Ord v => (VTerm n v -> VTerm n v) -> Set v -> Set v
applyMatchVars' f = fromList . concatMap extractVars . toList
        where
            extractVars = varsVTerm . f . varTerm


instance Apply SapicSubst (SapicAction SapicLVar) where
    apply subst (ChIn mt t vs) = ChIn (apply subst mt) (apply subst t) (applyMatchVars subst vs)
    apply subst (MSR l a r phi vs) = MSR (apply subst l) (apply subst a) (apply subst r)
                                       (apply subst phi) (applyMatchVars subst vs)
    apply subst ac = mapTermsAction (apply subst) (apply subst) (apply subst) ac

-- | Substitute for LVars, ignoring types
instance {-# OVERLAPPABLE #-} (Ord v, Apply s v) => Apply s (SapicAction v) where
    apply subst (ChIn mt t vs) = ChIn (apply subst mt) (f t) (applyMatchVars' f vs)
        where
            f = apply subst -- to fix the type of the instance of apply that applyMatchVars' gets, use the same as for term t
    apply subst ac = mapTermsAction (apply subst) (apply subst) (apply subst) ac

instance  Apply SapicSubst (ProcessCombinator SapicLVar) where
    apply subst (Let t1 t2 vs)
            = Let (apply subst t1) (apply subst t2) (applyMatchVars subst vs)
    apply subst c
            = mapTermsComb (apply subst) (apply subst) (apply subst) c

-- | Substitute for LVars, ignoring types
instance {-# OVERLAPPABLE #-} (Ord v, Apply s v) => Apply s (ProcessCombinator v) where
    apply subst (Let t1 t2 vs)
            = Let (f t1) (f t2) (applyMatchVars' f vs)
        where f = apply subst -- use same instance of Apply for t2 and applyMatchVars'
    apply subst c
            = mapTermsComb (apply subst) (apply subst) (apply subst) c

instance (Apply SapicSubst ann) => Apply SapicSubst (LProcess ann) where
-- We are ignoring capturing here, use applyM below to get warnings.
    apply _ (ProcessNull ann) = ProcessNull ann
    apply subst (ProcessComb c ann pl pr) =
                ProcessComb (apply subst c) (apply subst ann) (apply subst pl) (apply subst pr)
    apply subst (ProcessAction ac ann p') =
                ProcessAction (apply subst ac) (apply subst ann) (apply subst p')

-- | Substitute for LVars, ignoring types
instance {-# OVERLAPPABLE #-} (Ord v, Apply s v, Apply s ann) => Apply s (Process ann v) where
    apply _ (ProcessNull ann) = ProcessNull ann
    apply subst (ProcessComb c ann pl pr) =
                ProcessComb (apply subst c) (apply subst ann) (apply subst pl) (apply subst pr)
    apply subst (ProcessAction ac ann p') =
                ProcessAction (apply subst ac) (apply subst ann) (apply subst p')

-- | Get all variables for a process
varsProc :: (Ord v, Show v) => Process ann v -> Set v
varsProc = foldMap Data.Set.singleton -- foldProcess fNull fAct fComb gAct gComb empty p

-- | Variables to reserve when freshening a process. Locations can contain
-- variables absent from its actions, and earlier expansions record generated
-- binders in annotations. Back-substitutions only affect diagnostic names.
varsProcWithAnnotations :: GoodAnnotation ann => LProcess ann -> Set SapicLVar
varsProcWithAnnotations p = varsProc p `Set.union` pfoldMap annotationVars p
  where
    annotationVars node =
      let ann = getProcessParsedAnnotation (processGetAnnotation node)
      in fromList $ maybe [] freesSapicTerm (location ann) ++ generatedBinders ann

-------------------------
-- Applying substitutions ( with error messages )
-------------------------

data CapturedTag = CapturedIn | CapturedLookup | CapturedNew
    deriving (Typeable, Show)
data LetExceptions = CapturedEx CapturedTag SapicLVar
    deriving (Typeable, Show, Exception)
    -- deriving (Typeable)

prettyLetExceptions :: LetExceptions -> String
prettyLetExceptions (CapturedEx tag v) = "Error: The variable "++ show v ++ " appears in a let-expression that is captured in " ++ pretty tag ++ ". This is likely unintend. To proceed nonetheless, please rename the variable to pat_" ++ show v ++ " throughout."
    where pretty CapturedIn = "input"
          pretty CapturedLookup = "lookup"
          pretty CapturedNew = "new"

-- | `applyMatchVars subst vs` applies the substitution to each v in vs and

instance ApplyM SapicSubst (ProcessCombinator SapicLVar)
    where
    applyM subst c
        | (Lookup t v) <- c  = if v `elem` dom subst then
                                  throwM $ CapturedEx CapturedLookup v
                               else
                                  return $ Lookup (apply subst t) v
        | otherwise = return $ apply subst c


instance ApplyM SapicSubst (SapicAction SapicLVar)
    where
    applyM subst ac
        | (New v) <- ac =  if v `elem` dom subst then
                                  throwM $ CapturedEx CapturedNew v
                               else
                                  return $ New v
        | (ChIn mt t vs) <- ac,  Lit (Var v) <-  viewTerm t =
                            if v `elem` dom subst && not ( "pat_" `isPrefixOf` lvarName' v) then
                                  -- t is a single variable that is captured by the let.
                                  -- This is likely unintended, so we warn, unless the variable starts with
                                  -- pat_
                                  throwM $ CapturedEx CapturedIn v
                            else
                                  return $ ChIn (apply subst mt) (apply subst t) (applyMatchVars subst vs)
        | otherwise = return $ apply subst ac
        where lvarName' (SapicLVar v _ ) = lvarName v


-- | Binders introduced by an action scope over its continuation, not its
-- channel expression. Pattern matching variables are references, not binders.
-- Type annotations share one LVar namespace for scope and capture checks.
actionBinders :: SapicAction SapicLVar -> [SapicLVar]
actionBinders = uniqueBinderIdentities . actionBinderDeclarations

-- | Combinator binders scope over the left (success) continuation only.
-- The lookup key, let RHS, and right (failure) continuation are outside scope.
combinatorBinders :: ProcessCombinator SapicLVar -> [SapicLVar]
combinatorBinders = uniqueBinderIdentities . combinatorBinderDeclarations

-- | Apply a variable renaming only within an action's binding region.
-- The substitution maps only binder identities to fresh variables; matching
-- variables are references and are therefore left alone.
-- The caller carries the same renaming into the action continuation.
renameActionBinders :: Subst Name LVar -> SapicAction SapicLVar -> SapicAction SapicLVar
renameActionBinders ren (ChIn channel t matches) = ChIn channel (apply ren t) matches
renameActionBinders ren ac = apply ren ac

-- | Rename the local binding region of a combinator. Keys and right-hand
-- sides are evaluated before the binding. The caller carries the renaming
-- into the left continuation only, retaining its old environment on the right.
renameCombinatorBinders :: Subst Name LVar -> ProcessCombinator SapicLVar -> ProcessCombinator SapicLVar
renameCombinatorBinders ren (Lookup key v) = Lookup key (apply ren v)
renameCombinatorBinders ren (Let t rhs matches) = Let (apply ren t) rhs matches
renameCombinatorBinders _ comb = comb

-- | Preserve every annotation variant until typing has merged its constraints.
-- Scope consumers instead use the identity projections above.
actionBinderDeclarations :: SapicAction SapicLVar -> [SapicLVar]
actionBinderDeclarations (New v) = [v]
actionBinderDeclarations (ChIn _ t matches) = patternDeclarations (freesSapicTerm t) matches
actionBinderDeclarations (MSR ls _ _ _ matches) = patternDeclarations (concatMap freesSapicFact ls) matches
actionBinderDeclarations _ = []

combinatorBinderDeclarations :: ProcessCombinator SapicLVar -> [SapicLVar]
combinatorBinderDeclarations (Lookup _ v) = [v]
combinatorBinderDeclarations (Let t _ matches) = patternDeclarations (freesSapicTerm t) matches
combinatorBinderDeclarations _ = []

uniqueBinderIdentities :: [SapicLVar] -> [SapicLVar]
uniqueBinderIdentities = unique Set.empty
  where
    unique _ [] = []
    unique seen (v:vs)
      | toLVar v `member` seen = unique seen vs
      | otherwise = v : unique (Set.insert (toLVar v) seen) vs

patternDeclarations :: [SapicLVar] -> Set SapicLVar -> [SapicLVar]
patternDeclarations vars matches =
  Data.List.filter (\v -> toLVar v `Set.notMember` identities) vars
  where identities = Set.map toLVar matches

-- | Apply a process substitution with a scoped alpha-renaming environment.
-- Reserve the whole process once, including location metadata. A single fresh
-- supply keeps later names distinct without repeatedly scanning each suffix.
applyProcessSubstAvoiding :: (GoodAnnotation ann, MonadThrow m)
                         => [LVar] -> SapicSubst -> LProcess ann -> m (LProcess ann)
applyProcessSubstAvoiding = expandProcessCall Nothing

-- | Expand a call: substitute the arguments for the parameters in the body.
-- The reserved variables are those of the caller's scope. The body of a
-- closed definition (one with a parameter list) is a scope of its own, so
-- local binders that share identities with caller variables are renamed
-- apart first. Pattern parameters are substituted directly instead, since
-- they stand for the supplied pattern rather than a local binding.
expandProcessCall :: (GoodAnnotation ann, MonadThrow m)
                  => Maybe [SapicLVar] -> [LVar] -> SapicSubst -> LProcess ann -> m (LProcess ann)
expandProcessCall parameters reserved original proc =
    evalFreshTAvoiding (go (fromList reserved) Set.empty (substFromList [] :: Subst Name LVar) proc) avoidVars
  where
    -- Scope is indexed by LVar throughout SAPIC. Type annotations constrain
    -- occurrences, but must never change which variable gets substituted.
    images :: Map.Map LVar SapicTerm
    images = Map.fromList [(toLVar v, apply original (varTerm v)) | v <- dom original]
    procVars = Set.toList (varsProcWithAnnotations proc)
    occurrences = procVars ++ dom original
    subst :: SapicSubst
    subst = substFromList [(v, t) | v <- occurrences, Just t <- [Map.lookup (toLVar v) images]]

    incoming = fromList $ map toLVar $ varsRange subst
    -- Substitutions omit identity mappings. Keep the explicit formals too,
    -- so a nested call P(pat_x) cannot freshen P's own pat_x parameter away.
    formals = fromList $ maybe [] (map toLVar) parameters
    callerScope = fromList reserved
    avoidVars = reserved ++ map toLVar
      (dom subst ++ varsRange subst ++ procVars)
    freshening used ann bound = do
      let generated = fromList $ map toLVar $ generatedBinders $ getProcessParsedAnnotation ann
          -- Reallocate binders that an argument would capture, binders of a
          -- scope renamed apart from the caller, and generated binders that
          -- collide with the caller. Other user rebinding in an open body is
          -- preserved for validation.
          -- Pattern parameters are replaced by the argument itself; renaming
          -- them here would remove them from the substitution's domain.
          captures = Data.List.filter (\v -> not (patternParameter v) &&
                                 (v `member` incoming ||
                                  (isJust parameters && v `member` callerScope) ||
                                  (v `member` generated && v `member` used))) bound
      fresh <- mapM (\v -> freshLVar (lvarName v) (lvarSort v)) captures
      return $ substFromList $ zip captures (map varTerm fresh)
    patternParameter v = (v `member` formals || Map.member v images) &&
                         "pat_" `Data.List.isPrefixOf` lvarName v
    -- A closed call owns its local binders even before a name collision.
    -- Remember them through open wrappers, which may introduce a caller clash.
    -- Do not mark a repeated local binder: it must still fail rebinding checks.
    markGenerated local bound ren ann = applyAnn ren $ mapProcessParsedAnnotation (\parsed -> parsed
      { generatedBinders = nub $ generatedBinders parsed ++ map (`SapicLVar` Nothing)
          (dom ren ++ [v | isJust parameters, v <- bound, v `Set.notMember` local, not (patternParameter v)]) }) ann
    go used local env p = case p of
      ProcessNull ann -> ProcessNull <$> applyM subst (applyAnn env ann)
      ProcessAction ac ann rest -> do
        let ac0 = apply env ac
            ann0 = applyAnn env ann
            bound = map toLVar $ actionBinders ac0
        ren <- freshening used ann0 bound
        let ac1 = renameActionBinders ren ac0
        ac' <- applyM subst ac1
        ann' <- applyM subst (markGenerated local bound ren ann0)
        rest' <- go (Set.union (fromList $ map toLVar $ F.toList ac') used)
                    (Set.union (fromList $ map toLVar $ actionBinders ac') local) (ren `compose` env) rest
        return $ ProcessAction ac' ann' rest'
      ProcessComb comb ann left right -> do
        let comb0 = apply env comb
            ann0 = applyAnn env ann
            bound = map toLVar $ combinatorBinders comb0
        ren <- freshening used ann0 bound
        let comb1 = renameCombinatorBinders ren comb0
        comb' <- applyM subst comb1
        ann' <- applyM subst (markGenerated local bound ren ann0)
        left' <- go (Set.union (fromList $ map toLVar $ F.toList comb') used)
                    (Set.union (fromList $ map toLVar $ combinatorBinders comb') local) (ren `compose` env) left
        -- Let/lookup failure branches retain the incoming environment.
        right' <- go used local env right
        return $ ProcessComb comb' ann' left' right'

instance (GoodAnnotation ann) => ApplyM SapicSubst (LProcess ann) where
    applyM = applyProcessSubstAvoiding []

-- | Add another element to the existing annotations, e.g., yet another identifier.
processAddAnnotation :: Monoid ann => Process ann v -> ann -> Process ann v
-- processAddAnnotation ::               PlainProcess -> ProcessParsedAnnotation -> PlainProcess
processAddAnnotation (ProcessNull ann) ann' = ProcessNull $ ann `mappend` ann'
processAddAnnotation (ProcessComb c ann pl pr ) ann' = ProcessComb c (ann `mappend` ann')  pl pr
processAddAnnotation (ProcessAction a ann p ) ann' = ProcessAction a (ann `mappend` ann')  p

processGetAnnotation :: Process ann v -> ann
processGetAnnotation (ProcessNull ann) = ann
processGetAnnotation (ProcessComb _ ann _ _ ) = ann
processGetAnnotation (ProcessAction _ ann _ )  = ann

-------------------------
-- Pretty-printing for exceptions etc. (see Theory.Sapic.Print for nicer printing)
-------------------------


prettyPattern' :: Document c => Set SapicLVar -> SapicTerm -> c
prettyPattern' vs =  prettySapicTerm . unextractMatchingVariables vs

-- | Printer for SAPIC actions.
-- Note: Need to give the pretty printer for rules as a parameter as otherwise
-- we would have circular dependencies.
-- Instantiated in Theory.Sapic.Print later
prettySapicAction' :: ([SapicNFact SapicLVar]
    -> [SapicNFact SapicLVar]
    -> [SapicNFact SapicLVar]
    -> [SapicNFormula SapicLVar]
    -> Set SapicLVar
    -> [Char])
    -> SapicAction SapicLVar -> [Char]
prettySapicAction' _ (New n) = "new "++ show n
prettySapicAction' _ Rep  = "!"
prettySapicAction' _ (ChIn (Just t1) t2 vs)  = "in(" ++ render (prettySapicTerm t1) ++ "," ++ render (prettyPattern' vs t2) ++ ")"
prettySapicAction' _ (ChIn Nothing t2 vs )  = "in(" ++ render (prettyPattern' vs t2) ++ ")"
prettySapicAction' _ (ChOut (Just t1) t2 )  = "out(" ++ render (prettySapicTerm t1) ++ "," ++ render (prettySapicTerm t2) ++ ")"
prettySapicAction' _ (ChOut Nothing t2 )  = "out(" ++ render (prettySapicTerm t2) ++ ")"
prettySapicAction' _ (Insert t1 t2)  = "insert " ++ render (prettySapicTerm t1) ++ "," ++ render (prettySapicTerm t2)
prettySapicAction' _ (Delete t )  = "delete " ++ render (prettySapicTerm t)
prettySapicAction' _ (Lock t )  = "lock " ++ render (prettySapicTerm t)
prettySapicAction' _ (Unlock t )  = "unlock " ++ render (prettySapicTerm t)
prettySapicAction' _ (Event a )  = "event " ++ render (prettySapicFact a)
prettySapicAction' prettyRule' (MSR p a c r mv) = prettyRule' p a c r mv
prettySapicAction' _ (ProcessCall s ts) = s ++ "("++ p ts ++ ")"
                                    where p pts = render $
                                            fsep (punctuate comma (map prettySapicTerm pts))

prettySapicComb :: ProcessCombinator SapicLVar -> String
prettySapicComb Parallel = "|"
prettySapicComb NDC = "+"
prettySapicComb (Cond a) = "if "++ render (prettySyntacticSapicFormula a)
prettySapicComb (CondEq t t') = "if "++ p t ++ "=" ++ p t'
                                    where p = render . prettySapicTerm
prettySapicComb (Let t t' vs) = "let "++ p' t ++ "=" ++ p t'
                                    where p = render . prettySapicTerm
                                          p'= render . prettyPattern' vs
prettySapicComb (Lookup t v) = "lookup "++ p t ++ " as " ++ show v
                                    where p = render . prettySapicTerm

prettySapic' :: (Document d) => ([SapicNFact SapicLVar]
    -> [SapicNFact SapicLVar]
    -> [SapicNFact SapicLVar]
    -> [SapicNFormula SapicLVar]
    -> Set SapicLVar
    -> String)
    -> (ann -> Maybe SapicTerm)
    -> Process ann SapicLVar -> d
prettySapic' ppRR ppLoc = pp
    where
        -- Print a process that is not followed by further tokens.
        pp p = case ppLoc (processGetAnnotation p) of
            Just l  -> ppLocated l p
            Nothing -> ppForm p

        -- Print a process that is followed by further tokens. The printed
        -- form must not be able to absorb them, so any form that is not
        -- clearly delimited is parenthesized.
        ppDelimited p = case ppLoc (processGetAnnotation p) of
            -- the location term could absorb a following '+'
            Just l -> parens (ppLocated l p)
            Nothing
                | delimited p -> ppForm p
                | otherwise   -> parens (ppForm p)

        -- Left operands of '|' and '+' may keep their own '|' and '+'
        -- structure without parentheses: the parser is left-associative.
        ppLeftOp p
            | chainNode p = ppForm p
            | otherwise   = ppDelimited p

        ppLocated l p = parens (ppForm p) <> text "@" <> prettySapicTerm l

        -- A '|' or '+' node without a location annotation. Only these
        -- print as a bare chain; an annotated node prints as "(p)@term".
        chainNode p
            | ProcessComb c _ _ _ <- p
            , Nothing <- ppLoc (processGetAnnotation p) = isParOrNDC c
            | otherwise                                 = False

        isParOrNDC Parallel = True
        isParOrNDC NDC      = True
        isParOrNDC _        = False

        -- Printed forms that neither absorb a following token nor extend to
        -- the right. Replication is excluded on purpose: '!' takes a whole
        -- process, so it would swallow a following '|' or '+'.
        delimited (ProcessNull _)                     = True
        delimited (ProcessAction ProcessCall {} _ _)  = True
        delimited (ProcessAction a _ (ProcessNull _)) = delimitedAction a
        delimited _                                   = False

        -- Actions that do not absorb a following token. Actions ending in a
        -- term are excluded: the term could absorb a following '+'.
        delimitedAction (New _)   = True
        delimitedAction ChIn {}   = True
        delimitedAction ChOut {}  = True
        delimitedAction (Event _) = True
        delimitedAction _         = False

        -- The keyword between the head of a branching combinator and its
        -- first branch.
        branchKeyword c = case c of
            Cond _     -> "then"
            CondEq _ _ -> "then"
            _          -> "in"  -- Let and Lookup

        ppForm (ProcessNull _) = text "0"
        ppForm (ProcessComb c _ pl pr)
            | isParOrNDC c = ppLeftOp pl <-> text (prettySapicComb c) <-> ppDelimited pr
            -- if, let and lookup, with an optional else branch
            | (ProcessNull _) <- pr = hdr $-$ nest 4 (pp pl)
            | otherwise = hdr $-$ nest 4 (ppDelimited pl) $-$ text "else" $-$ nest 4 (pp pr)
            where
                hdr = text (prettySapicComb c) <-> text (branchKeyword c)
        ppForm (ProcessAction Rep _ p') = ppAct Rep <> parens (pp p')
        ppForm (ProcessAction a@ProcessCall {} _ _ ) = ppAct a
        ppForm (ProcessAction a _ (ProcessNull _)) = ppAct a
        ppForm (ProcessAction a _ p') = ppAct a <> semi $-$ ppNext p'

        -- Print the process behind a ';'. The grammar only allows an action
        -- process there, so a '|' or '+' chain needs parentheses.
        ppNext p'
            | chainNode p' = nest 1 (parens (ppForm p'))
            | otherwise    = pp p'

        ppAct a = text (prettySapicAction' ppRR a)

--- >>> render $ prettySapic' undefined (const Nothing) (ProcessNull ())
-- "0"

--- >>> render $ semi <> semi
-- ";;"

--- >>> render $ semi $-$ semi
-- ";\n;"

-- | Printer for the top-level process, used, e.g., for rule names.
prettySapicTopLevel' :: ([SapicNFact SapicLVar]
    -> [SapicNFact SapicLVar]
    -> [SapicNFact SapicLVar]
    -> [SapicNFormula SapicLVar]
    -> Set SapicLVar
    -> [Char])
    -> Process ann SapicLVar -> [Char]
prettySapicTopLevel' _ (ProcessNull _) = "0"
prettySapicTopLevel' _ (ProcessComb c _ _ _)  = prettySapicComb c
prettySapicTopLevel' prettyRuleRestr (ProcessAction Rep _ _)  = prettySapicAction' prettyRuleRestr Rep
prettySapicTopLevel' prettyRuleRestr (ProcessAction a _ _)  = prettySapicAction' prettyRuleRestr a ++ ";"
