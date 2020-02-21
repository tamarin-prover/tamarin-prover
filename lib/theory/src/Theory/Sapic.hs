{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE StandaloneDeriving    #-}
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
    , applyProcess
    , pfoldMap
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
) where

import Data.Binary
import Data.Data
import Data.List
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
data SapicLVar = SapicLVar { slvar:: LVar, stype:: SapicType }
     deriving( Ord, Eq, Typeable, Data, Generic, NFData, Binary, IsVar )
type LNTTerm = VTerm Name SapicLVar
type SapicNTerm v = VTerm Name v
type SapicTerm = LNTTerm
type SapicNFact v = Fact (SapicNTerm v)
type SapicLNFact = Fact SapicTerm
type SapicNFormula v = ProtoFormula SyntacticSugar (String, LSort) Name v
type SapicFormula = ProtoFormula SyntacticSugar (String, LSort) Name SapicLVar

-- | Function symbol (f,l,r) with argument types l and return type r
type SapicFunSym = (FunSym, [SapicType], SapicType) 

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

instance Hinted SapicLVar where
    hint (SapicLVar v _) = hint v

-- conversion function
toLVar:: SapicLVar -> LVar
toLVar = slvar

toLNTerm:: SapicTerm -> LNTerm 
toLNTerm = fmap f 
    where 
        f (Con c) = Con c
        f (Var v) = Var $ toLVar v

toLNFact:: SapicLNFact -> LNFact 
toLNFact = fmap toLNTerm

-- toLFormua:: SapicFormula -> LFormula
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
        | CondEq (SapicNTerm v) (SapicNTerm v) | Lookup (SapicNTerm v) v
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
                
-- ProcessAction (mapTermsAction f ac) ann p'
-- foldProcess fNull fAct fComb a (ProcessComb c ann pl pr) = ProcessComb (mapTermsComb f c) ann pl pr

mapTerms _ (ProcessNull ann)  = ProcessNull ann 
mapTerms f (ProcessAction ac ann p') = ProcessAction (mapTermsAction f ac) ann p'
mapTerms f (ProcessComb c ann pl pr) = ProcessComb (mapTermsComb f c) ann pl pr

-- foldMapAction f ::  Monoid m => (SapicNTerm v -> m) -> SapicAction v -> m 
-- foldTermsAction f ac
--         | (New v) <- ac, v' <- termVar' (f (varTerm v)) = v'
--         | (ChIn  mt t) <- ac   = (fmap f mt) `mappend` (f t)
--         | (ChOut mt t) <- ac   = (fmap f mt) `mappend` (f t)
--         | (Insert t1 t2) <- ac = (f t1)  `mappend` (f t2)
--         | (Delete t) <- ac     = (f t)
--         | (Lock t) <- ac       = (f t)
--         | (Unlock t) <- ac     = (f t)
--         | (Event fa) <- ac      = Event (fmap f fa)
--         | (MSR (l,a,r,rest)) <- ac  = MSR $ (f2mapf l, f2mapf a, f2mapf r, fmap formulaMap rest)
--         | Rep <- ac            = Rep
--             where f2mapf = fmap $ fmap f
--                   -- something like
--                   -- formulaMap = mapAtoms $ const $ fmap $ fmap f
--                   formulaMap = undefined

mapTermsAction f ac 
        | (New v) <- ac, v' <- termVar' (f (varTerm v)) = New v'
        | (ChIn  mt t) <- ac   = ChIn (fmap f mt) (f t)
        | (ChOut mt t) <- ac   = ChOut (fmap f mt) (f t)
        | (Insert t1 t2) <- ac = Insert (f t1) (f t2)
        | (Delete t) <- ac     = Delete (f t)
        | (Lock t) <- ac       = Lock (f t)
        | (Unlock t) <- ac     = Unlock (f t)
        | (Event fa) <- ac      = Event (fmap f fa)
        | (MSR (l,a,r,rest)) <- ac  = MSR $ (f2mapf l, f2mapf a, f2mapf r, fmap formulaMap rest)
        | Rep <- ac            = Rep
            where f2mapf = fmap $ fmap f
                  -- something like
                  -- formulaMap = mapAtoms $ const $ fmap $ fmap f
                  formulaMap = undefined
    
mapTermsComb f c
        | (Cond fa) <- c = Cond $ undefined -- same problem as above
        | (CondEq t1 t2) <- c = CondEq (f t1) (f t2)
        | (Lookup t v) <- c = Lookup (f t) v
        | otherwise = c 

instance (IsVar v) => Apply (Subst Name v) (ProcessCombinator v) where
    apply subst c 
            = mapTermsComb (apply subst) c
        -- | (Cond f) <- c = Cond $ apply subst f
        -- | (CondEq t1 t2) <- c = CondEq (apply subst t1) (apply subst t2)
        -- | (Lookup t v) <- c = Lookup (apply subst t) v
        -- | otherwise = c 

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
        = mapTermsAction (apply subst) ac
    --     | (New v) <- ac        = New v
    --     | (ChIn  mt t) <- ac   = ChIn (apply subst mt) (apply subst t)
    --     | (ChOut mt t) <- ac   = ChOut (apply subst mt) (apply subst t)
    --     | (Insert t1 t2) <- ac = Insert (apply subst t1) (apply subst t2)
    --     | (Delete t) <- ac     = Delete (apply subst t)
    --     | (Lock t) <- ac       = Lock (apply subst t)
    --     | (Unlock t) <- ac     = Unlock (apply subst t)
    --     | (Event f) <- ac      = Event (apply subst f)
    --     | (MSR (l,a,r,rest)) <- ac  = MSR $ apply subst (l,a,r,rest)
    --     | Rep <- ac            = Rep

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
    where lvarName' (SapicLVar v _) = lvarName v

instance Apply SapicSubst (LProcess ann) where
-- We are ignoring capturing here, use applyProcess below to get warnings.
    apply _ (ProcessNull ann) = ProcessNull ann
    apply subst (ProcessComb c ann pl pr) =
                ProcessComb (apply subst c) ann (apply subst pl) (apply subst pr)
    apply subst (ProcessAction ac ann p') =
                ProcessAction (apply subst ac) ann (apply subst p')

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

type ProcessName = String -- String used in annotation to identify processes
type ProcessAnnotation = [ProcessName]
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
prettySapicComb (Lookup t v) = "lookup "++ p t ++ " as " ++ show v
                                    where p = render . prettySapicTerm

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

