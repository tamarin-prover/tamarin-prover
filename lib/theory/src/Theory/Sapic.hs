{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
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
module Theory.Sapic (
    -- types
    Process(..)
    , ProcessCombinator(..)
    , ProcessParsedAnnotation(..)
    , SapicType
    , defaultSapicTypeS
    , defaultSapicType
    , defaultSapicNodeType
    , SapicAction(..)
    , SapicLVar(..)
    , SapicTerm
    , SapicNTerm
    , SapicLNFact
    , SapicFormula
    , SapicFunSym
    , LSapicAction
    , LProcessCombinator
    , LProcess
    , PlainProcess
    -- converters
    , toLVar
    , toLNTerm
    , toLNFact
    , toLFormula
    -- utitlities
    , paddAnn
    , foldProcess
    , foldMProcess
    , traverseProcess
    , traverseProcess'
    , traverseTermsAction
    , traverseTermsComb
    , applyProcess
    , pfoldMap
    , mapTerms
    , mapTermsAction
    , mapTermsComb
    , ProcessPosition
    , lhsP
    , rhsP
    , descendant
    -- pretty printing
    , prettySapic'
    , prettySapicAction'
    , prettySapicComb
    , prettySapicTopLevel'
    , prettyPosition
    -- exception type for lets
    , LetExceptions (..)
    , prettyLetExceptions
    -- TODO external
    , PatternSapicLVar(..)
    , unpattern
    , extractMatchingVariables
) where

import Data.Binary
import Data.Data
import Data.List
import qualified Data.Set as S
import GHC.Generics (Generic)
import Control.Parallel.Strategies
import Theory.Model.Fact
import Theory.Model.Atom
import Theory.Model.Formula
import Term.LTerm
import Term.Substitution
import Theory.Text.Pretty
import Control.Monad.Catch

-- | A process data structure

-- | In general, terms we use in the translation have logical veriables
type SapicType = Maybe String
data SapicLVar = SapicLVar { slvar:: LVar, stype:: SapicType}
     deriving( Ord, Eq, Typeable, Data, Generic, NFData, Binary, IsVar )
data PatternSapicLVar =  PatternBind SapicLVar | PatternMatch SapicLVar
     deriving( Ord, Eq, Typeable, Data, Generic, NFData, Binary, IsVar )

type LNTTerm = VTerm Name SapicLVar
type SapicNTerm v = VTerm Name v
type SapicTerm = LNTTerm
type SapicNFact v = Fact (SapicNTerm v)
type SapicLNFact = Fact SapicTerm
type SapicNFormula v = ProtoFormula SyntacticSugar (String, LSort) Name v
type SapicFormula = ProtoFormula SyntacticSugar (String, LSort) Name SapicLVar

-- | Function symbol (f,l,r) with argument types l and return type r
-- define only on NoEqSyms, as we will assume the others to be polymorphic
type SapicFunSym = (NoEqSym, [SapicType], SapicType)

-- TODO alternative definition.
-- 1. If we need to extend, switch to this tyoe
-- 2. If we are done and merge into main and have not used it,
--    then delete this comment.
-- data SapicFunSym = SapicFunSym
--        { _sfSym            :: NoEqSym
--        , _sfOutType        :: SapicType
--        , _sfInType         :: [SapicType]
--        }
--        deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- $(mkLabels [''SapicFunSym])

defaultSapicTypeS :: String
defaultSapicTypeS = "bitstring"
defaultSapicType :: SapicType
defaultSapicType = Just defaultSapicTypeS

defaultSapicNodeType :: SapicType
defaultSapicNodeType = Just "node"

-- | A substitution with names and typed logical variables.
type SapicSubst = Subst Name SapicLVar

instance Show SapicLVar where
    show (SapicLVar v (Just t)) = show  v ++ ":" ++ t
    show (SapicLVar v Nothing ) = show  v

--- TODO move this stuff into separate file.
instance Show PatternSapicLVar where
    show (PatternBind v) = show v
    show (PatternMatch v) = "=" ++ show v


unpattern :: SapicNTerm PatternSapicLVar -> SapicNTerm SapicLVar
unpattern = fmap (fmap unpattern')
    where
        unpattern' (PatternBind  v) = v
        unpattern' (PatternMatch v) = v

extractMatchingVariables :: SapicNTerm PatternSapicLVar -> S.Set SapicLVar
extractMatchingVariables pt = S.fromList $ foldMap (foldMap isPatternMatch) pt
    where
        isPatternMatch (PatternMatch v) = [v]
        isPatternMatch (PatternBind _ ) = []

instance Hinted SapicLVar where
    hint (SapicLVar v _) = hint v

-- conversion functions for sapic types
toLVar:: SapicLVar -> LVar
toLVar = slvar

toLNTerm:: SapicTerm -> LNTerm
toLNTerm = fmap f
    where
        f (Con c) = Con c
        f (Var v) = Var $ toLVar v

toLNFact:: SapicLNFact -> LNFact
toLNFact = fmap toLNTerm

toLFormula:: (Functor syn) => ProtoFormula syn (String, LSort) c SapicLVar -> ProtoFormula syn (String, LSort) c LVar
toLFormula = mapAtoms f
    where f _ = fmap $ fmap $ fmap $ fmap toLVar

-- | Actions are parts of the process that maybe connected with ";"
data SapicAction v =
                   Rep
                 | New v
                 | ChIn (Maybe (SapicNTerm v)) (SapicNTerm v)
                 | ChOut (Maybe (SapicNTerm v)) (SapicNTerm v)
                 | Insert (SapicNTerm v) (SapicNTerm v)
                 | Delete (SapicNTerm v)
                 | Lock (SapicNTerm v)
                 | Unlock (SapicNTerm v)
                 | Event (SapicNFact v)
                 | MSR ([SapicNFact v], [SapicNFact v], [SapicNFact v], [SapicNFormula v])
            deriving (Functor, Foldable)

deriving instance (Show v) => Show (SapicAction v)
deriving instance (Eq v) => Eq (SapicAction v)
deriving instance (Ord v) => Ord (SapicAction v)
deriving instance (Generic v) => Generic (SapicAction v)
deriving instance (NFData v, Generic v) => NFData (SapicAction v)
deriving instance (Binary v, Generic v) => Binary (SapicAction v)
deriving instance (Data v, Generic v) => Data (SapicAction v)

-- | When the process tree splits, it is connected with one of these connectives
data ProcessCombinator v = Parallel | NDC | Cond (SapicNFormula v)
        | CondEq (SapicNTerm v) (SapicNTerm v) | Lookup (SapicNTerm v) v | Let (SapicNTerm v) (SapicNTerm v) | ProcessCall String [v] [SapicNTerm v]
            deriving (Functor,Foldable)

deriving instance (Show v) => Show (ProcessCombinator v)
deriving instance (Eq v) => Eq (ProcessCombinator v)
deriving instance (Ord v) => Ord (ProcessCombinator v)
deriving instance (Generic v) => Generic (ProcessCombinator v)
deriving instance (NFData v, Generic v) => NFData (ProcessCombinator v)
deriving instance (Binary v, Generic v) => Binary (ProcessCombinator v)
deriving instance (Data v, Generic v) => Data (ProcessCombinator v)

-- | The process tree is terminated with null processes, and either splits
-- (parallel and other combinators) or describes a sequence of actions with
-- only one daughter
data Process ann v =
        ProcessNull ann
    |   ProcessComb (ProcessCombinator v) ann (Process ann v) (Process ann v)
    |   ProcessAction (SapicAction v) ann (Process ann v)
     deriving(Generic, Data )

type LSapicAction = SapicAction SapicLVar
type LProcessCombinator = ProcessCombinator SapicLVar
type LProcess ann =  Process ann SapicLVar

deriving instance (Eq ann, Eq v) => Eq (Process ann v)
deriving instance (Ord ann, Ord v) => Ord (Process ann v)
deriving instance (NFData ann) => NFData (LProcess ann)
deriving instance (Binary ann) => Binary (LProcess ann)
deriving instance (Show ann, Show v) => Show (Process ann v)
deriving instance Functor (Process ann)
deriving instance Foldable (Process ann)

-- | map over a process: @mapTerms ft ff fv@ applies @ft@ to terms, @ff@ to formulas and @fv@ to variables
mapTerms :: (SapicNTerm t -> SapicNTerm v)
            -> (SapicNFormula t -> SapicNFormula v)
            -> (t -> v)
            -> Process ann t
            -> Process ann v
mapTerms _ _  _  (ProcessNull ann)  = ProcessNull ann
mapTerms f ff fv (ProcessAction ac ann p') = ProcessAction (mapTermsAction f ff fv ac) ann (mT p')
    where mT = mapTerms f ff fv
mapTerms f ff fv (ProcessComb c ann pl pr) = ProcessComb (mapTermsComb f ff fv c) ann (mT pl) (mT pr)
    where mT = mapTerms f ff fv

mapTermsAction :: (SapicNTerm t -> SapicNTerm v)
                  -> (SapicNFormula t -> SapicNFormula v)
                  -> (t -> v)
                  -> SapicAction t
                  -> SapicAction v
mapTermsAction f ff fv ac
        | (New v) <- ac        = New (fv v)
        | (ChIn  mt t) <- ac   = ChIn (fmap f mt) (f t)
        | (ChOut mt t) <- ac   = ChOut (fmap f mt) (f t)
        | (Insert t1 t2) <- ac = Insert (f t1) (f t2)
        | (Delete t) <- ac     = Delete (f t)
        | (Lock t) <- ac       = Lock (f t)
        | (Unlock t) <- ac     = Unlock (f t)
        | (Event fa) <- ac      = Event (fmap f fa)
        | (MSR (l,a,r,rest)) <- ac  = MSR (f2mapf l, f2mapf a, f2mapf r, fmap ff rest)
        | Rep <- ac            = Rep
            where f2mapf = fmap $ fmap f

mapTermsComb :: (SapicNTerm t -> SapicNTerm v)
                -> (SapicNFormula t -> SapicNFormula v)
                -> (t -> v)
                -> ProcessCombinator t
                -> ProcessCombinator v
mapTermsComb f ff fv c
        | (Cond fa) <- c = Cond $ ff fa
        | (CondEq t1 t2) <- c = CondEq (f t1) (f t2)
        | (Let t1 t2) <- c  = Let (f t1) (f t2)
        | (Lookup t v) <- c = Lookup (f t) (fv v)
        | Parallel <- c = Parallel
        | NDC    <- c   = NDC
        | ProcessCall s vs ts <- c = ProcessCall s (map fv vs) (map f ts)


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

-- | fold process with side-effect. Just like @foldProcess@, but allows functions with side-effects.
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
            f  <- gAct a' ac ann p'' -- 3. reconstruct result from accumulator and subtree's result
            return f
    | (ProcessComb c ann pl pr) <- p = do
            a' <- fComb a ann c
            rl <- foldMProcess fNull fAct fComb gAct gComb a' pl
            rr <- foldMProcess fNull fAct fComb gAct gComb a' pr
            r  <- gComb a' c ann rl rr
            return r

-- | Traverses process. Simplified variant of @foldMProcces@ that avoids accumulator (can store in monad)
traverseProcess :: Monad m =>
                   (t2 -> m t3)
                   -> (SapicAction v -> t2 -> t3 -> m t3)
                   -> (ProcessCombinator v -> t2 -> t3 -> t3 -> m t3)
                   -> Process t2 v
                   -> m t3
traverseProcess gNull gAct gComb = foldMProcess (const gNull) nothing nothing (const gAct) (const gComb) ()
        where nothing = const $ const $ const $ return ()

traverseProcess' :: Monad m =>
                       (SapicNTerm t -> m (SapicNTerm v))
                       -> (SapicNFormula t -> m (SapicNFormula v))
                       -> (t -> m v)
                       -> Process ann t
                       -> m (Process ann v)
traverseProcess' ft ff fv = traverseProcess gN gA gC
    where
        gN = return . ProcessNull
        gA ac ann p = do
             ac' <- traverseTermsAction ft ff fv ac
             return $ ProcessAction ac' ann p
        gC c ann pl pr = do
             c'  <- traverseTermsComb ft ff fv c
             return $ ProcessComb c' ann pl pr

traverseTermsAction :: Applicative f =>
                       (SapicNTerm t -> f (SapicNTerm v))
                       -> (SapicNFormula t -> f (SapicNFormula v))
                       -> (t -> f v)
                       -> SapicAction t
                       -> f (SapicAction v)
traverseTermsAction ft ff fv ac
        -- | (New v) <- ac = (New . termVar') <$> ft (varTerm v)
        | (New v) <- ac = New <$> fv v
        | (ChIn  mt t) <- ac   = ChIn <$> traverse ft mt <*> ft t
        | (ChOut mt t) <- ac   = ChOut<$> traverse ft mt <*> ft t
        | (Insert t1 t2) <- ac = Insert <$> ft t1 <*> (ft t2)
        | (Delete t) <- ac     = Delete <$> ft t
        | (Lock t) <- ac       = Lock   <$> ft t
        | (Unlock t) <- ac     = Unlock <$> ft t
        | (Event fa) <- ac      = Event <$> traverse ft fa
        | (MSR (l,a,r,rest)) <- ac  = do
                    (\l' a' r' rest' -> MSR (l',a',r',rest'))
                    <$>
                         t2f l
                     <*> t2f a
                     <*> t2f r
                     <*> traverse ff rest
        | Rep <- ac            = pure Rep
            where t2f = traverse (traverse ft)

traverseTermsComb :: Applicative f =>
                     (SapicNTerm t -> f (SapicNTerm a))
                     -> (SapicNFormula t -> f (SapicNFormula a))
                     -> (t -> f a)
                     -> ProcessCombinator t
                     -> f (ProcessCombinator a)
traverseTermsComb ft ff fv c
        | (Cond fa)      <- c = Cond <$> ff fa
        | (CondEq t1 t2) <- c = CondEq <$> ft t1 <*> ft t2
        | (Let t1 t2) <- c    = Let <$> ft t1 <*> ft t2
        | (Lookup t v)   <- c = Lookup <$> ft t <*> fv v
        | Parallel       <- c = pure Parallel
        | NDC            <- c = pure NDC
        | ProcessCall s vs ts <- c = ProcessCall s <$> (traverse fv vs) <*> (traverse ft ts)

-------------------------
-- Applying substitutions
-------------------------

instance (IsVar v) => Apply (Subst Name v) (ProcessCombinator v) where
    apply subst c
            = mapTermsComb (apply subst) (apply subst) (apply subst) c

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



-- | Apply a substitution, but raise an error if necessary
applyProcessCombinatorError :: MonadThrow m => Subst Name SapicLVar
            -> ProcessCombinator SapicLVar -> m (ProcessCombinator SapicLVar)
applyProcessCombinatorError subst c
        | (Lookup t v) <- c  = if v `elem` dom subst then
                                  throwM $ CapturedEx CapturedLookup v
                               else
                                  return $ Lookup (apply subst t) v
        | otherwise = return $ apply subst c


instance Apply SapicSubst (SapicAction SapicLVar) where
    apply subst ac
        = mapTermsAction (apply subst) (apply subst) (apply subst) ac

-- | Apply a substitution, but raise an error if necessary
applySapicActionError :: MonadThrow m =>
    Subst Name SapicLVar -> SapicAction SapicLVar -> m (SapicAction SapicLVar)
applySapicActionError subst ac
        | (New v) <- ac =  if v `elem` dom subst then
                                  throwM $ CapturedEx CapturedNew v
                               else
                                  return $ New v
        | (ChIn mt t) <- ac,  Lit (Var v) <-  viewTerm t =
                            if v `elem` dom subst && not ( "pat_" `isPrefixOf` lvarName' v) then
                                  -- t is a single variable that is captured by the let.
                                  -- This is likely unintended, so we warn, unless the variable starts with
                                  -- pat_
                                  throwM $ CapturedEx CapturedIn v
                            else
                                  return $ ChIn (apply subst mt) (apply subst t)
        | otherwise = return $ apply subst ac
    where lvarName' (SapicLVar v _ ) = lvarName v

instance Apply SapicSubst (LProcess ann) where
-- We are ignoring capturing here, use applyProcess below to get warnings.
    apply _ (ProcessNull ann) = ProcessNull ann
    apply subst (ProcessComb c ann pl pr) =
                ProcessComb (apply subst c) ann (apply subst pl) (apply subst pr)
    apply subst (ProcessAction ac ann p') =
                ProcessAction (apply subst ac) ann (apply subst p')

-- | Apply a substitution, but raise an error if necessary
applyProcess :: MonadThrow m => SapicSubst -> LProcess ann -> m (LProcess ann)
applyProcess _ (ProcessNull ann) = return $ ProcessNull ann
applyProcess subst (ProcessComb c ann pl pr) = do
                c' <- applyProcessCombinatorError subst c
                pl' <- applyProcess subst pl
                pr' <- applyProcess subst pr
                return $ ProcessComb c' ann pl' pr'
applyProcess subst (ProcessAction ac ann p) = do
                ac' <- applySapicActionError subst ac
                p' <- applyProcess subst p
                return $ ProcessAction ac' ann p'

-- | After parsing, the process is already annotated wth a list of process
--   identifiers. Any identifier in this in this list was inlined to give this
--   comment, e.g.,
--    let A = 0
--    let B = A | A
--    !B
--    has two Null-rules with annotation [A,B].
--  This will be helpful to recognise protocols roles and visualise them.

data ProcessParsedAnnotation =
  ProcessName String -- String used in annotation to identify processes
  | ProcessLoc SapicTerm -- additional information for Isolated Execution Environments feature
  | ProcessMatchVar (S.Set SapicLVar) -- Variables in in() or let-actions that are intended to match already bound variables
  deriving( Eq, Ord, Show, Data, Generic)
instance NFData ProcessParsedAnnotation
instance Binary ProcessParsedAnnotation
type ProcessAnnotation = [ProcessParsedAnnotation]
type PlainProcess = LProcess ProcessAnnotation
type ProcessPosition = [Int]

-- | Positions are to be read left-to-right, 1 is left, 2 is right.
lhsP :: [Int] -> ProcessPosition
lhsP p = (p++[1]) :: ProcessPosition

rhsP :: [Int] -> ProcessPosition
rhsP p = (p++[2]) :: ProcessPosition
-- rhs :: ProcessPosition = 2

descendant :: Eq a => [a] -> [a] -> Bool
descendant child parent = parent `isPrefixOf` child

-- | Add another element to the existing annotations, e.g., yet another identifier.
paddAnn :: PlainProcess -> ProcessAnnotation -> PlainProcess
paddAnn (ProcessNull ann) ann' = ProcessNull $ ann `mappend` ann'
paddAnn (ProcessComb c ann pl pr ) ann' = ProcessComb c (ann `mappend` ann')  pl pr
paddAnn (ProcessAction a ann p ) ann' = ProcessAction a (ann `mappend` ann')  p

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

prettyPosition:: ProcessPosition -> String
prettyPosition = foldl (\ s n -> s ++ show n ) ""

-- | Pretty print an @SapicTerm@.
prettySapicTerm :: Document d => SapicTerm -> d
prettySapicTerm = prettyTerm (text . show)

prettySapicFact :: Document d => Fact SapicTerm -> d
prettySapicFact = prettyFact prettySapicTerm

prettySyntacticSapicFormula :: HighlightDocument d => ProtoFormula SyntacticSugar (String, LSort) Name SapicLVar -> d
prettySyntacticSapicFormula = prettySyntacticLNFormula . toLFormula


-- | Printer for SAPIC actions.
-- Note: Need to give the pretty printer for rules as a parameter as otherwise
-- we would have circular dependencies.
-- Instantiated in Theory.Sapic.Print later
prettySapicAction' ::
                   ( [SapicLNFact] -> [SapicLNFact] -> [SapicLNFact] -> [SapicFormula] -> String)
                    -> SapicAction SapicLVar  -> String
prettySapicAction' _ (New n) = "new "++ show n
prettySapicAction' _ Rep  = "!"
prettySapicAction' _ (ChIn (Just t1) t2 )  = "in(" ++ render (prettySapicTerm t1) ++ "," ++ render ( prettySapicTerm t2) ++ ")"
prettySapicAction' _ (ChIn Nothing t2 )  = "in(" ++ render (prettySapicTerm t2) ++ ")"
prettySapicAction' _ (ChOut (Just t1) t2 )  = "out(" ++ render (prettySapicTerm t1) ++ "," ++ render (prettySapicTerm t2) ++ ")"
prettySapicAction' _ (ChOut Nothing t2 )  = "out(" ++ render (prettySapicTerm t2) ++ ")"
prettySapicAction' _ (Insert t1 t2)  = "insert " ++ render (prettySapicTerm t1) ++ "," ++ render (prettySapicTerm t2)
prettySapicAction' _ (Delete t )  = "delete " ++ render (prettySapicTerm t)
prettySapicAction' _ (Lock t )  = "lock " ++ render (prettySapicTerm t)
prettySapicAction' _ (Unlock t )  = "unlock " ++ render (prettySapicTerm t)
prettySapicAction' _ (Event a )  = "event " ++ render (prettySapicFact a)
prettySapicAction' prettyRule' (MSR (p,a,c,r)) = prettyRule' p a c r

prettySapicComb :: ProcessCombinator SapicLVar -> String
prettySapicComb Parallel = "|"
prettySapicComb NDC = "+"
prettySapicComb (Cond a) = "if "++ render (prettySyntacticSapicFormula a)
prettySapicComb (CondEq t t') = "if "++ p t ++ "=" ++ p t'
                                    where p = render . prettySapicTerm
prettySapicComb (Let t t') = "let "++ p t ++ "=" ++ p t'
                                    where p = render . prettySapicTerm
prettySapicComb (Lookup t v) = "lookup "++ p t ++ " as " ++ show v
                                    where p = render . prettySapicTerm
prettySapicComb (ProcessCall s _ ts) = s ++ "("++ p ts ++ ")"
                                    where p pts = render $
                                            fsep (punctuate comma (map prettySapicTerm pts))



-- | Printer for SAPIC processes..
-- TODO At the moment, the process structure is not used to properly print how
-- elements are associated.
-- Should do it, but then we cannot use pfoldMap anymore.
prettySapic' :: ([SapicLNFact] -> [SapicLNFact] -> [SapicLNFact] -> [SapicFormula] -> String) -> LProcess ann -> String
prettySapic' prettyRuleRestr = pfoldMap f
    where f (ProcessNull _) = "0"
          f (ProcessComb c _ _ _)  = prettySapicComb c
          f (ProcessAction Rep _ _)  = prettySapicAction' prettyRuleRestr Rep
          f (ProcessAction a _ _)  = prettySapicAction' prettyRuleRestr a ++ ";"

-- | Printer for the top-level process, used, e.g., for rule names.
prettySapicTopLevel' :: ([SapicLNFact] -> [SapicLNFact] -> [SapicLNFact] -> [SapicFormula] -> String) -> LProcess ann -> String
prettySapicTopLevel' _ (ProcessNull _) = "0"
prettySapicTopLevel' _ (ProcessComb c _ _ _)  = prettySapicComb c
prettySapicTopLevel' prettyRuleRestr (ProcessAction Rep _ _)  = prettySapicAction' prettyRuleRestr Rep
prettySapicTopLevel' prettyRuleRestr (ProcessAction a _ _)  = prettySapicAction' prettyRuleRestr a ++ ";"
