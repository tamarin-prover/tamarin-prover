{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Terms with logical variables  and names.
module Term.LTerm (

  -- * Names
    Name(..)
  , NameTag(..)
  , NameId(..)

  , NTerm

  -- ** Queries
  , sortOfName

  -- ** Construction
  , freshTerm
  , pubTerm
  , natTerm

  -- * LVar
  , LSort(..)
  , LVar(..)
  , NodeId
  , LTerm
  , LNTerm

  , freshLVar
  , sortPrefix
  , sortSuffix
  , sortCompare
  , sortOfLTerm
  , sortOfLNTerm
  , sortOfLit
  , isMsgVar
  , isFreshVar
  , isPubVar
  , isNatVar
  , isPubConst
  , isSimpleTerm
  , getVar
  , getMsgVar
  , freshToConst
  , variableToConst
  , niFactors
  , flattenedACTerms
  , SubtermSplit(..)
  , splitSubterm
  , containsPrivate
  , containsNoPrivateExcept
  , neverContainsFreshPriv
  , sortTypename
  , sortFromString
  , isUserSort

  -- ** Destructors
  , ltermVar
  , ltermVar'
  , ltermNodeId
  , ltermNodeId'
  , bltermNodeId
  , bltermNodeId'


  -- ** Manging Free LVars

  , HasFrees(..)
  , MonotoneFunction(..)
  , occurs
  , freesList
  , frees
  , someInst
  , rename
  , renameIgnoring
  , eqModuloFreshnessNoAC
  , avoid
  , evalFreshAvoiding
  , evalFreshTAvoiding
  , renameAvoiding
  , renameAvoidingIgnoring
  , avoidPrecise
  , renamePrecise
  , renameDropNamehint
  , varOccurences

  -- * BVar
  , BVar(..)
  , BLVar
  , BLTerm
  , foldBVar
  , fromFree

  -- * Pretty-Printing
  , prettyLVar
  , prettyNodeId
  , prettyNTerm
  , prettyLNTerm
  , showLitName

  -- * Convenience exports
  , module Term.VTerm
) where

import           Text.PrettyPrint.Class

-- import           Control.Applicative
import           Control.Basics
import           Control.DeepSeq
import           Control.Monad.Bind
import           Control.Monad.Identity
import qualified Control.Monad.Trans.PreciseFresh as Precise

import           GHC.Generics                     (Generic)
import           Data.Binary
import qualified Data.List                        as L
import qualified Data.DList                       as D
import           Data.Foldable                    hiding (concatMap, elem, notElem, any)
import           Data.Data
import qualified Data.Map                         as M
import qualified Data.Map.Strict                  as M'
import           Data.Monoid
import qualified Data.Set                         as S
-- import           Data.Traversable
import qualified Data.ByteString.Char8            as BC

import           Safe                             (fromJustNote)

import           Extension.Data.Monoid
import           Extension.Prelude


import           Logic.Connectives

import           Term.Rewriting.Definitions
import           Term.VTerm

------------------------------------------------------------------------------
-- Sorts.
------------------------------------------------------------------------------

-- | Sorts for logical variables. They satisfy the following sub-sort relation:
--
-- >  LSortFresh < LSortMsg
-- >  LSortPub   < LSortMsg
-- >  LSortNat   < LSortMsg
-- >  LSortUser  < LSortMsg
--
data LSort = LSortPub   -- ^ Arbitrary public names.
           | LSortFresh -- ^ Arbitrary fresh names.
           | LSortMsg   -- ^ Arbitrary messages.
           | LSortNode         -- ^ Sort for variables denoting nodes of derivation graphs.
           | LSortNat          -- ^ Arbitrary natural numbers.
           | LSortUser String  -- ^ Arbitrary user-defined sort.
           deriving( Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary )

-- | @sortCompare s1 s2@ compares @s1@ and @s2@ with respect to the partial order on sorts.
-- Partial order:
--     Node
--
--     Msg
--     |-- Fresh
--     |-- User
--     |-- Pub
--
sortCompare :: LSort -> LSort -> Maybe Ordering  --TODO-MY take care that this is still correct; update the above figure 
sortCompare s1 s2 = case (s1, s2) of
    (a, b) | a == b          -> Just EQ
    -- Node is incomparable to all other sorts, invalid input
    (LSortNode,  _        )  -> Nothing
    (_,          LSortNode)  -> Nothing
    -- Msg is greater than all sorts except Node
    (LSortMsg,   _        )  -> Just GT
    (_,          LSortMsg )  -> Just LT
    -- The remaining combinations (Pub/Fresh) are incomparable
    _                        -> Nothing

-- | @sortPrefix s@ is the prefix we use for annotating variables of sort @s@.
sortPrefix :: LSort -> String
sortPrefix LSortMsg       = ""
sortPrefix LSortFresh     = "~"
sortPrefix LSortPub       = "$"
sortPrefix LSortNode      = "#"
sortPrefix LSortNat       = "%"
sortPrefix (LSortUser st) = "?" ++ st ++ "?"
--TODO-MY add LSortNum

-- | @sortSuffix s@ is the suffix we use for annotating variables of sort @s@.
sortSuffix :: LSort -> String
sortSuffix LSortMsg       = "msg"
sortSuffix LSortFresh     = "fresh"
sortSuffix LSortPub       = "pub"
sortSuffix LSortNode      = "node"
sortSuffix LSortNat       = "nat"
sortSuffix (LSortUser st) = st
--TODO-MY add LSortNum


------------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------------

-- | Type safety for names.
newtype NameId = NameId { getNameId :: String }
    deriving( Eq, Ord, Typeable, Data, Generic, NFData, Binary )

-- | Tags for names.
data NameTag = FreshName | PubName | NodeName | NatName  --TODO-MY add NumName
    deriving( Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary )

-- | Names.
data Name = Name {nTag :: NameTag, nId :: NameId}
    deriving( Eq, Ord, Typeable, Data, Generic, NFData, Binary)

-- | Terms with literals containing names and arbitrary variables.
type NTerm v = VTerm Name v


-- Instances
------------

instance IsConst Name where

instance Show Name where
  show (Name FreshName  n) = "~'" ++ show n ++ "'"  --TODO-MY-NONUM use sortPrefix
  show (Name PubName    n) = "'"  ++ show n ++ "'"
  show (Name NodeName   n) = "#'" ++ show n ++ "'"
  show (Name NatName   n) = "%'" ++ show n ++ "'"
--TODO-MY add NumName

instance Show NameId where
  show = getNameId

-- Construction of terms with names
-----------------------------------

-- | @freshTerm f@ represents the fresh name @f@.
freshTerm :: String -> NTerm v
freshTerm = lit . Con . Name FreshName . NameId

-- | @pubTerm f@ represents the pub name @f@.
pubTerm :: String -> NTerm v
pubTerm = lit . Con . Name PubName . NameId

-- | @natTerm f@ represents the nat name @f@.
natTerm :: String -> NTerm v
natTerm = lit . Con . Name NatName . NameId

-- | Return 'LSort' for given 'Name'.
sortOfName :: Name -> LSort
sortOfName (Name FreshName _) = LSortFresh
sortOfName (Name PubName   _) = LSortPub
sortOfName (Name NodeName  _) = LSortNode
sortOfName (Name NatName   _) = LSortNat

-- | Is a term a public constant?
isPubConst :: LNTerm -> Bool
isPubConst (viewTerm -> Lit (Con v)) = (sortOfName v == LSortPub)  --TODO-MY add LSortNum
isPubConst _                         = False


------------------------------------------------------------------------------
-- LVar: logical variables
------------------------------------------------------------------------------


-- | Logical variables. Variables with the same name and index but different
-- sorts are regarded as different variables.
data LVar = LVar
     { lvarName :: String
     , lvarSort :: !LSort     -- FIXME: Rename to 'sortOfLVar' for consistency
                              -- with the other 'sortOf' functions.
     , lvarIdx  :: !Integer
     }
     deriving( Typeable, Data, Generic, NFData, Binary )

-- | An alternative name for logical variables, which are intented to be
-- variables of sort 'LSortNode'.
type NodeId = LVar

-- | Terms used for proving; i.e., variables fixed to logical variables.
type LTerm c = VTerm c LVar

-- | Terms used for proving; i.e., variables fixed to logical variables
--   and constants to Names.
type LNTerm = VTerm Name LVar

-- | @freshLVar v@ represents a fresh logical variable with name @v@.
freshLVar :: MonadFresh m => String -> LSort -> m LVar
freshLVar n s = LVar n s <$> freshIdent n

-- | Returns the most precise sort of an 'LTerm'.
sortOfLTerm :: Show c => (c -> LSort) -> LTerm c -> LSort
sortOfLTerm sortOfConst t = case viewTerm2 t of
    Lit2 (Con c)                          -> sortOfConst c
    Lit2 (Var lv)                         -> lvarSort lv
    FAppNoEq (NoEqSym _ _ _ (Just sts)) _ -> sortFromString $ last sts
    FUserAC _ sort _                      -> sortFromString sort
    FNatPlus _                            -> LSortNat
    _                                     -> LSortMsg  --TODO-MY adapt because functions can return non-msg-sort!!!!!

-- | Returns the most precise sort of an 'LNTerm'.
sortOfLNTerm :: LNTerm -> LSort
sortOfLNTerm = sortOfLTerm sortOfName

-- | Returns the most precise sort of a 'Lit'.
sortOfLit :: Lit Name LVar -> LSort
sortOfLit (Con n) = sortOfName n
sortOfLit (Var v) = lvarSort v

-- | Is a term a message variable?
isMsgVar :: LNTerm -> Bool
isMsgVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortMsg)
isMsgVar _                         = False  --TODO-MY understand better how this is used - maybe something needs to be done?

-- | Is a term a public variable?
isPubVar :: LNTerm -> Bool
isPubVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortPub)
isPubVar _                         = False  --TODO-MY understand better how this is used - maybe something needs to be done?

-- | Is a term a number variable?
isNatVar :: LNTerm -> Bool
isNatVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortNat)
isNatVar _                         = False

-- | Is a term a fresh variable?
isFreshVar :: LNTerm -> Bool
isFreshVar (viewTerm -> Lit (Var v)) = (lvarSort v == LSortFresh)
isFreshVar _                         = False  --TODO-MY understand better how this is used - maybe something needs to be done?

--TODO-MY maybe isNumVar is needed?

-- | If the term is a variable, return it, nothing otherwise.
getVar :: LNTerm -> Maybe LVar
getVar (viewTerm -> Lit (Var v)) = Just v
getVar _                         = Nothing

-- | If the term is a message variable, return it, nothing otherwise.
getMsgVar :: LNTerm -> Maybe [LVar]
getMsgVar (viewTerm -> Lit (Var v)) | (lvarSort v == LSortMsg) = Just [v]
getMsgVar _                                                    = Nothing


-- Utility functions for constraint solving
-------------------------------------------

-- | The non-inverse factors of a term.
niFactors :: LNTerm -> [LNTerm]  --TODO-MY pay special attention to this!!
niFactors t = case viewTerm2 t of
                FMult ts -> concatMap niFactors ts
                FInv t1  -> niFactors t1
                _        -> [t]

-- | If @[term1, ..., termN]@ is returned, then @t = term1 + ... + termN@ where @+@ is the ACSymbol.
-- It is made sure that the length of the returned list is maximal (i.e., the + is flattened)
flattenedACTerms :: ACSym -> Term t -> [Term t]
flattenedACTerms f (viewTerm -> FApp (AC sym) ts)
  | sym == f = concatMap (flattenedACTerms f) ts
flattenedACTerms _ term = [term]


data SubtermSplit = SubtermD    (LNTerm, LNTerm)
                  | NatSubtermD (LNTerm, LNTerm, LVar)  -- small, big, newVar
                  | EqualD      (LNTerm, LNTerm)
                  | ACNewVarD   (LNTerm, LNTerm, LVar)  -- small+newVar, big, newVar
                  | TrueD
  deriving (Eq, Ord, Show, Typeable, Data, Generic, NFData, Binary)

-- | Deconstructs a subterm according to the CR-rules S_subterm-[ac-]recurse, S_invalid and stops destructing for S_nat / S_neg-nat
-- Returns @set@ such that @small ⊏ big@ is equivalent to the disjunction of @set@
-- If the subterm is trivially false, [] is returned as the empty disjunction
splitSubterm :: MonadFresh m => FunSig -> (LNTerm, LNTerm) -> m [SubtermSplit]
splitSubterm reducible subterm = S.toList <$> recurse (SubtermD subterm)
  where
    recurse :: MonadFresh m => SubtermSplit -> m (S.Set SubtermSplit)
    recurse std@(SubtermD st) = do
      res <- step st
      case res of
        Just entries -> S.unions <$> mapM recurse (S.toList entries)
        Nothing -> return $ S.singleton std
    recurse x = return $ S.singleton x  -- for everything except SubtermD we stop the recursion

    -- @step@ returns nothing if @small ⊏ big@ cannot be further destructed.
    -- Else it returns @Just list@ if @small ⊏ big@ can be replaced by the disjunction of the list.
    -- It especially returns @Just []@ if @small ⊏ big@ is trivially false.
    step :: MonadFresh m => (LNTerm, LNTerm) -> m (Maybe (S.Set SubtermSplit))
    step (small, big)
      | onlyOnes small && l small < l big && sortOfLNTerm big == LSortNat =  -- terms like 1+1 < x+y+z
        return $ Just $ S.singleton TrueD  -- true
      | (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat = do  -- CR-rule S_nat (delayed)
        ac <- processAC NatPlus (small, big)
        return $ case ac of
          Right False -> Just S.empty
          Right True -> Just $ S.singleton TrueD
          Left tuple -> Just $ S.singleton $ NatSubtermD tuple
      | big `redElem` small =  -- trivially false (big == small included)
        return $ Just S.empty  -- false
      | small `redElem` big =  -- trivially true
        return $ Just $ S.singleton TrueD  -- true
          where
            onlyOnes t = all (fAppNatOne ==) $ flattenedACTerms NatPlus t
            l t = length $ flattenedACTerms NatPlus t
    step (_, viewTerm -> Lit (Con _)) =  -- nothing can be a strict subterm of a constant
        return $ Just S.empty  -- false
    step (small, big@(viewTerm -> Lit (Var _)))
      | isPubVar big || isFreshVar big || (not (sortOfLNTerm small == LSortNat || isMsgVar small) && sortOfLNTerm big == LSortNat) =  -- CR-rule S_invalid
        return $ Just S.empty  -- false
    step (_, viewTerm -> Lit (Var _)) =  -- variable: do not recurse further
        return Nothing
    step (small, big@(viewTerm -> FApp (AC f) _))  -- apply CR-rule S_subterm-ac-recurse
      | AC f `S.notMember` reducible = do
        ac <- processAC f (small, big)
        return $ case ac of
          Right False -> Just S.empty
          Right True -> Just $ S.singleton TrueD
          Left (nSmall, nBig, newVar) ->
            let acSpecial = ACNewVarD (fAppAC f [nSmall, varTerm newVar], nBig, newVar)
            in Just $ acSpecial `S.insert` S.unions (map (eqOrSubterm small) (flattenedACTerms f big))
    step (small, viewTerm -> FApp (NoEq f) ts)  -- apply CR-rule S_subterm-recurse
      | NoEq f `S.notMember` reducible = do
        return $ Just $ S.unions (map (eqOrSubterm small) ts)
    step (_, viewTerm -> FApp (C _) _) =  -- we treat commutative but not associative symbols as reducible functions
        return Nothing
    step (_, viewTerm -> FApp List _) =  -- list seems to be unused (?)
        return Nothing
    step _ =  -- reducible function symbol observed (when applying subterm-[ac-]recurse)
        return Nothing

    redElem = elemNotBelowReducible reducible
    eqOrSubterm :: LNTerm -> LNTerm -> S.Set SubtermSplit
    eqOrSubterm s t = S.fromList [SubtermD (s, t), EqualD (s, t)]  -- the unifiers for the equation

    -- returns the triple @((nSmall, nBig), newVar, ac)@
    -- nSmall, nBig are small, big where terms are removed that were on both sides
    -- newVar is for the CR-rule S_neg-ac-recurse
    processAC :: MonadFresh m => ACSym -> (LNTerm, LNTerm) -> m (Either (LNTerm, LNTerm, LVar) Bool)
    processAC f (small, big) = do
        newVar <- freshLVar "newVar" (sortOfLNTerm big)  -- generate a new variable
        return $ case lists of
          (_, []) -> Right False
          ([], _) -> Right True
          (lSmall, lBig) -> Left (fAppAC f lSmall, fAppAC f lBig, newVar)
        --let term = fAppAC f [nSmall, varTerm newVar]  -- build the term = small + newVar
      where
        -- removes terms that are on both sides of the subterm
        -- lists have to be sorted before removeSame works
        removeSame (a:as, b:bs) | a == b = removeSame (as,   bs)
        removeSame (a:as, b:bs) | a < b  = first (a:) $ removeSame (as, b:bs)
        removeSame (a:as, b:bs) | a > b  = second (b:) $ removeSame (a:as, bs)
        removeSame x = x  -- one of the lists is empty

        lists = removeSame (L.sort $ flattenedACTerms f small, L.sort $ flattenedACTerms f big)


-- | @containsPrivate t@ returns @True@ if @t@ contains private function symbols.
containsPrivate :: Term t -> Bool  --NOT-TODO-MY this function is all-fine; nothing to do as non-Private is only diff
containsPrivate t = case viewTerm t of
    Lit _                                  -> False
    FApp (NoEq (NoEqSym _ _ Private _)) _  -> True
    FApp _                              as -> any containsPrivate as

-- | containsNoPrivateExcept t t2@ returns @True@ if @t2@ contains private function symbols other than @t@.
containsNoPrivateExcept :: [BC.ByteString] -> Term t -> Bool  --NOT-TODO-MY like the above
containsNoPrivateExcept funs t = case viewTerm t of
    Lit _                          -> True
    FApp (NoEq (NoEqSym f _ Private _)) as -> (elem f funs) && (all (containsNoPrivateExcept funs) as)
    FApp _                      as -> all (containsNoPrivateExcept funs) as

    
-- | A term is *simple* iff there is an instance of this term that can be
-- constructed from public names only. i.e., the term does not contain any
-- fresh names, fresh variables, or private function symbols.
isSimpleTerm :: LNTerm -> Bool  --NOT-TODO-MY should be fine like this
isSimpleTerm t =
    not (containsPrivate t) && 
    (getAll . foldMap (All . (LSortFresh /=) . sortOfLit) $ t)

-- | 'True' iff no instance of this term contains fresh names or private function symbols.
neverContainsFreshPriv :: LNTerm -> Bool  --TODO-MY probably nothing to change but double-check the WF-condition that uses this
neverContainsFreshPriv t =
    not (containsPrivate t) && 
    (getAll . foldMap (All . (`notElem` [LSortMsg, LSortFresh]) . sortOfLit) $ t)

-- | Replaces all Fresh variables with constants using toConst.
freshToConst :: LNTerm -> LNTerm  --NOT-TODO-MY
freshToConst t = case viewTerm t of
    Lit (Con _)                              -> t
    Lit (Var v) | (lvarSort v == LSortFresh) -> variableToConst v
    Lit _                                    -> t
    FApp f as                                -> termViewToTerm $ FApp f (map freshToConst as)


-- | Given a variable returns a constant containing its name and type
variableToConst :: LVar -> LNTerm
variableToConst cvar = constTerm (Name (nameOfSort cvar) (NameId ("constVar_" ++ toConstName cvar)))
  where
    toConstName (LVar name vsort idx) = (show vsort) ++ "_" ++ (show idx) ++ "_" ++ name

    nameOfSort (LVar _ LSortFresh _) = FreshName
    nameOfSort (LVar _ LSortPub   _) = PubName
    nameOfSort (LVar _ LSortNode  _) = NodeName  --TODO-MY add NumName
    nameOfSort (LVar _ LSortMsg   _) = error "Invalid sort Msg"

-- | @sortTypename s@ is the string used for representing sort @s@ in function
-- signatures (when defining custom functions).
sortTypename :: LSort -> String
sortTypename LSortMsg       = "Msg"
sortTypename LSortFresh     = "Fresh"
sortTypename LSortPub       = "Pub"
sortTypename LSortNat       = "Nat"
sortTypename (LSortUser st) = st
sortTypename LSortNode      = error "sortTypename: May not use sort 'Node'."

-- | @sortFromString t@ is the sort for a given typename @t@.
sortFromString :: String -> LSort
sortFromString "Msg"   = LSortMsg
sortFromString "Fresh" = LSortFresh
sortFromString "Pub"   = LSortPub
sortFromString "Nat"   = LSortNat
sortFromString "Node"  = error "sortFromString: May not use sort 'Node'."
sortFromString st      = LSortUser st

-- | Is this a user-defined sort?
isUserSort :: LSort -> Bool
isUserSort (LSortUser _) = True
isUserSort _             = False

-- Destructors
--------------

-- | Extract a variable of the given sort from a term that may be such a
-- variable. Use 'termVar', if you do not want to restrict the sort.
ltermVar :: LSort -> LTerm c -> Maybe LVar  --NOT-TODO-MY
ltermVar s t = do v <- termVar t; guard (s == lvarSort v); return v

-- | Extract a variable of the given sort from a term that must be such a
-- variable. Fails with an error, if that is not possible.
ltermVar' :: Show c => LSort -> LTerm c -> LVar  --NOT-TODO-MY
ltermVar' s t =
    fromJustNote err (ltermVar s t)
  where
    err = "ltermVar': expected variable term of sort " ++ show s ++ ", but got " ++ show t

-- | Extract a node-id variable from a term that may be a node-id variable.
ltermNodeId  :: LTerm c -> Maybe LVar  --NOT-TODO-MY
ltermNodeId = ltermVar LSortNode

-- | Extract a node-id variable from a term that must be a node-id variable.
ltermNodeId' :: Show c => LTerm c -> LVar  --NOT-TODO-MY
ltermNodeId' = ltermVar' LSortNode


-- BVar: Bound variables
------------------------

-- | Bound and free variables.
data BVar v = Bound Integer  -- ^ A bound variable in De-Brujin notation.
            | Free  v        -- ^ A free variable.
            deriving( Eq, Ord, Show, Data, Typeable, Generic, NFData, Binary, IsVar)

-- | 'LVar's combined with quantified variables. They occur only in 'LFormula's.
type BLVar = BVar LVar

-- | Terms built over names and 'LVar's combined with quantified variables.
type BLTerm = NTerm BLVar


-- | Fold a possibly bound variable.
{-# INLINE foldBVar #-}
foldBVar :: (Integer -> a) -> (v -> a) -> BVar v -> a
foldBVar fBound fFree = go
  where
    go (Bound i) = fBound i
    go (Free v)  = fFree v

instance Functor BVar where
    fmap f = foldBVar Bound (Free . f)

instance Foldable BVar where
    foldMap f = foldBVar mempty f

instance Traversable BVar where
    traverse f = foldBVar (pure . Bound) (fmap Free . f)

instance Applicative BVar where
   pure  = return
   (<*>) = ap

instance Monad BVar where
    return  = Free
    m >>= f = foldBVar Bound f m

-- | Extract the name of free variable under the assumption the variable is
-- guaranteed to be of the form @Free a@.
fromFree :: BVar v -> v
fromFree (Free v)  = v
fromFree (Bound i) = error $ "fromFree: bound variable '" ++ show i ++ "'"

-- | Extract a node-id variable from a term that may be a node-id variable.
bltermNodeId  :: BLTerm -> Maybe LVar
bltermNodeId t = do
    Free v <- termVar t; guard (LSortNode == lvarSort v); return v

-- | Extract a node-id variable from a term that must be a node-id variable.
bltermNodeId' :: BLTerm -> LVar
bltermNodeId' t =
    fromJustNote err (bltermNodeId t)
  where
    err = "bltermNodeId': expected free node-id variable term, but got " ++
           show t

-- Instances
------------

instance Eq LVar where
  (LVar n1 s1 i1) == (LVar n2 s2 i2) = i1 == i2 && s1 == s2 && n1 == n2

-- An ord instance that prefers the 'lvarIdx' over the 'lvarName'.
instance Ord LVar where
    compare (LVar x1 x2 x3) (LVar y1 y2 y3) =
        compare x3 y3 <> compare x2 y2 <> compare x1 y1

instance Show LVar where
    show (LVar v s i)
        | isUserSort s  = body ++ ":" ++ sortSuffix s
        | s == LSortNat = body ++ ":" ++ sortSuffix s
        | otherwise     = sortPrefix s ++ body
      where
        body | null v           = show i
--             | isDigit (last v) = v ++ "." ++ show i
             | i == 0           = v
             | otherwise        = v ++ "." ++ show i

instance IsVar LVar where

------------------------------------------------------------------------------
-- Managing bound and free LVars
------------------------------------------------------------------------------


-- | This type captures the occurence of a variable in a certain context.
type Occurence = [String]

-- | For performance reasons, we distinguish between monotone functions on
-- 'LVar's and arbitrary functions. For a monotone f, if @x <= y@, then
-- @f x <= f y@. This ensures that the AC-normal form does not have
-- to be recomputed. If you are unsure about what to use, then use the
-- 'Arbitrary' function.
data MonotoneFunction f = Monotone (LVar -> f LVar )
                        | Arbitrary (LVar -> f LVar )

-- | @HasFree t@ denotes that the type @t@ has free @LVar@ variables. They can
-- be collected using 'foldFrees' and 'foldFreesOcc' and mapped in the context
-- of an applicative functor using 'mapFrees'.
--
-- When defining instances of this class, you have to ensure that only the free
-- LVars are collected and mapped and no others. The instances for standard
-- Haskell types assume that all variables free in all type arguments are free.
-- The 'foldFreesOcc' is only used to define the function 'varOccurences'. See
-- below for required properties of the instance methods.
--
-- Once we need it, we can use type synonym instances to parameterize over the
-- variable type.
--
class HasFrees t where
    foldFrees  :: Monoid m      => (LVar -> m      ) -> t -> m
    foldFreesOcc :: Monoid m => (Occurence -> LVar -> m) -> Occurence -> t -> m
    mapFrees   :: Applicative f => MonotoneFunction f -> t -> f t

-- | @v `occurs` t@ iff variable @v@ occurs as a free variable in @t@.
occurs :: HasFrees t => LVar -> t -> Bool
occurs x = getAny . foldFrees (Any . (x ==))

-- | @freesDList t@ is the difference list of all free variables of @t@.
freesDList :: HasFrees t => t -> D.DList LVar
freesDList = foldFrees pure

-- | @freesList t@ is the list of all free variables of @t@.
freesList :: HasFrees t => t -> [LVar]
freesList = D.toList . freesDList

-- | @frees t@ is the sorted and duplicate-free list of all free variables in
-- @t@.
frees :: HasFrees t => t -> [LVar]
frees = sortednub . freesList

-- | Returns the variables occuring in @t@ together with the contexts they appear in.
-- Note that certain contexts (and variables only occuring in such contexts) are
-- ignored by this function.
-- The function is used to "guess" renamings of variables, i.e., if t is a renaming of s,
-- then variables that occur in equal contexts in t and s are probably renamings of
-- each other.
varOccurences :: HasFrees a => a -> [(LVar, S.Set Occurence)]
varOccurences t =
    map (\((v,ctx1):rest) -> (v, S.fromList (ctx1:(map snd rest)))) . groupOn fst . sortOn fst
    . foldFreesOcc (\ c v -> [(v,c)]) [] $ t

-- | @someInst t@ returns an instance of @t@ where all free variables whose
-- binding is not yet determined by the caller are replaced with fresh
-- variables.
someInst :: (MonadFresh m, MonadBind LVar LVar m, HasFrees t) => t -> m t
someInst = mapFrees (Arbitrary $ \x -> importBinding (`LVar` lvarSort x) x (lvarName x))

-- | @rename t@ replaces all variables in @t@ with fresh variables.
--   Note that the result is not guaranteed to be equal for terms that are
--   equal modulo changing the indices of variables.
rename :: (MonadFresh m, HasFrees a) => a -> m a
rename x = case boundsVarIdx x of
    Nothing                     -> return x
    Just (minVarIdx, maxVarIdx) -> do
      freshStart <- freshIdents (succ (maxVarIdx - minVarIdx))
      return . runIdentity . mapFrees (Monotone $ incVar (freshStart - minVarIdx)) $ x
  where
    incVar shift (LVar n so i) = pure $ LVar n so (i+shift)

-- | @renameIgnoring t vars@ replaces all variables in @t@ with fresh variables, excpet for the variables in @vars@.
--   Note that the result is not guaranteed to be equal for terms that are
--   equal modulo changing the indices of variables.
renameIgnoring :: (MonadFresh m, HasFrees a) => [LVar] -> a -> m a
renameIgnoring vars x = case boundsVarIdx x of
    Nothing                     -> return x
    Just (minVarIdx, maxVarIdx) -> do
      freshStart <- freshIdents (succ (maxVarIdx - minVarIdx))
      return . runIdentity . mapFrees (Monotone $ incVar (freshStart - minVarIdx)) $ x
  where
    incVar shift (LVar n so i) = pure $ if elem (LVar n so i) vars then (LVar n so i) else (LVar n so (i+shift))

    
-- | @eqModuloFreshness t1 t2@ checks whether @t1@ is equal to @t2@ modulo
-- renaming of indices of free variables. Note that the normal form is not
-- unique with respect to AC symbols.
eqModuloFreshnessNoAC :: (HasFrees a, Eq a) => a -> a -> Bool
eqModuloFreshnessNoAC t1 =
     -- this formulation shares normalisation of t1 among further calls to
     -- different t2.
    (normIndices t1 ==) . normIndices
  where
    normIndices = (`evalFresh` nothingUsed) . (`evalBindT` noBindings) .
                  mapFrees (Arbitrary $ \x -> importBinding (`LVar` lvarSort x) x "")

-- | The mininum and maximum index of all free variables.
boundsVarIdx :: HasFrees t => t -> Maybe (Integer, Integer)
boundsVarIdx = getMinMax . foldFrees (minMaxSingleton . lvarIdx)

-- | @avoid t@ computes a 'FreshState' that avoids generating
-- variables occurring in @t@.
avoid :: HasFrees t => t -> FreshState
avoid = maybe 0 (succ . snd) . boundsVarIdx

-- | @m `evalFreshAvoiding` t@ evaluates the monadic action @m@ with a
-- fresh-variable supply that avoids generating variables occurring in @t@.
evalFreshAvoiding :: HasFrees t => Fresh a -> t -> a
evalFreshAvoiding m a = evalFresh m (avoid a)

-- | @m `evalFreshTAvoiding` t@ evaluates the monadic action @m@ in the
-- underlying monad with a fresh-variable supply that avoids generating
-- variables occurring in @t@.
evalFreshTAvoiding :: (Monad m, HasFrees t) => FreshT m a -> t -> m a
evalFreshTAvoiding m = evalFreshT m . avoid

-- | @s `renameAvoiding` t@ replaces all free variables in @s@ by
--   fresh variables avoiding variables in @t@.
renameAvoiding :: (HasFrees s, HasFrees t) => s -> t -> s
renameAvoiding s t = evalFreshAvoiding (rename s) t

-- | @s `renameAvoiding` t@ replaces all free variables in @s@ by
--   fresh variables avoiding variables in @t@.
renameAvoidingIgnoring :: (HasFrees s, HasFrees t) => s -> t -> [LVar] -> s
renameAvoidingIgnoring s t vars = renameIgnoring vars s `evalFreshAvoiding` t


-- | @avoidPrecise t@ computes a 'Precise.FreshState' that avoids generating
-- variables occurring in @t@.
avoidPrecise :: HasFrees t => t -> Precise.FreshState
avoidPrecise =
    foldl' ins M.empty . frees
  where
    ins m v = M'.insertWith max (lvarName v) (lvarIdx v + 1) m

-- | @renamePrecise t@ replaces all variables in @t@ with fresh variables.
--   If 'Control.Monad.PreciseFresh' is used with non-AC terms and identical
--   fresh state, the same result is returned for two terms that only differ
--   in the indices of variables.
renamePrecise :: (MonadFresh m, HasFrees a) => a -> m a
renamePrecise x = evalBindT (someInst x) noBindings


renameDropNamehint :: (MonadFresh m, MonadBind LVar LVar m, HasFrees a) => a -> m a
renameDropNamehint =
    mapFrees (Arbitrary $ \x -> importBinding (`LVar` lvarSort x) x "")


-- Instances
------------

instance HasFrees LVar where
    foldFrees = id
    foldFreesOcc f c v = f c v
    mapFrees (Arbitrary f) = f
    mapFrees (Monotone f)  = f

instance HasFrees v => HasFrees (Lit c v) where
    foldFrees f (Var x) = foldFrees f x
    foldFrees _ _       = mempty

    foldFreesOcc f c (Var x) = foldFreesOcc f c x
    foldFreesOcc _ _ _       = mempty

    mapFrees f (Var x) = Var <$> mapFrees f x
    mapFrees _ l       = pure l

instance HasFrees v => HasFrees (BVar v) where
    foldFrees _ (Bound _) = mempty
    foldFrees f (Free v)  = foldFrees f v

    foldFreesOcc _ _ (Bound _) = mempty
    foldFreesOcc f c (Free v)  = foldFreesOcc f c v

    mapFrees _ b@(Bound _) = pure b
    mapFrees f   (Free v)  = Free <$> mapFrees f v

instance (HasFrees l, Ord l) => HasFrees (Term l) where
    foldFrees f = foldMap (foldFrees f)

    foldFreesOcc f c t = case viewTerm t of
        Lit  l             -> foldFreesOcc f c l
        FApp (NoEq o) as   -> foldFreesOcc f (noEqOp o:c) as
        FApp o        as   -> mconcat $ map (foldFreesOcc f (show o:c)) as
      where
        noEqOp (NoEqSym fs _ _ _) = BC.unpack fs
          -- AC or C symbols

    mapFrees f (viewTerm -> Lit l)                  = lit <$> mapFrees f l
    mapFrees f@(Arbitrary _) (viewTerm -> FApp o l) = fApp o <$> mapFrees f l
    mapFrees f@(Monotone _)  (viewTerm -> FApp o l) = unsafefApp o <$> mapFrees f l

instance HasFrees a => HasFrees (Equal a) where
    foldFrees    f               = foldMap (foldFrees f)
    foldFreesOcc f p (Equal a b) = foldFreesOcc f p (a,b)
    mapFrees     f               = traverse (mapFrees f)

instance HasFrees a => HasFrees (Match a) where
    foldFrees    f                       = foldMap (foldFrees f)
    foldFreesOcc _ _ NoMatch             = mempty
    foldFreesOcc f p (DelayedMatches ms) = foldFreesOcc f p ms
    mapFrees     f                       = traverse (mapFrees f)

instance HasFrees a => HasFrees (RRule a) where
    foldFrees    f               = foldMap (foldFrees f)
    foldFreesOcc f p (RRule a b) = foldFreesOcc f p (a,b)
    mapFrees     f               = traverse (mapFrees f)

instance HasFrees () where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Int where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Integer where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Bool where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees Char where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

instance HasFrees a => HasFrees (Maybe a) where
    foldFrees    f            = foldMap (foldFrees f)
    foldFreesOcc _ _ Nothing  = mempty
    foldFreesOcc f p (Just x) = foldFreesOcc f p x
    mapFrees     f            = traverse (mapFrees f)

instance (HasFrees a, HasFrees b) => HasFrees (Either a b) where
    foldFrees    f   = either (foldFrees f) (foldFrees f)
    foldFreesOcc f p = either (foldFreesOcc f ("0":p)) (foldFreesOcc f ("1":p))
    mapFrees     f   = either (fmap Left . mapFrees   f) (fmap Right . mapFrees   f)

instance (HasFrees a, HasFrees b) => HasFrees (a, b) where
    foldFrees    f   (x, y) = foldFrees f x `mappend` foldFrees f y
    foldFreesOcc f p (x, y) = foldFreesOcc f ("0":p) x `mappend` foldFreesOcc f ("1":p) y
    mapFrees     f   (x, y) = (,) <$> mapFrees   f x <*> mapFrees   f y

instance (HasFrees a, HasFrees b, HasFrees c) => HasFrees (a, b, c) where
    foldFrees    f (x, y, z)    = foldFrees f (x, (y, z))
    foldFreesOcc f p (x, y, z)  =
        foldFreesOcc f ("0":p) x `mappend` foldFreesOcc f ("1":p) y `mappend` foldFreesOcc f ("2":p) z
    mapFrees     f (x0, y0, z0) =
        (\(x, (y, z)) -> (x, y, z)) <$> mapFrees f (x0, (y0, z0))

instance (HasFrees a, HasFrees b, HasFrees c, HasFrees d) => HasFrees (a, b, c, d) where
    foldFrees    f (x, y, z, a)    = foldFrees f (x, (y, (z, a)))
    foldFreesOcc f p (x, y, z, a)  =
        foldFreesOcc f ("0":p) x `mappend` foldFreesOcc f ("1":p) y
          `mappend` foldFreesOcc f ("2":p) z `mappend` foldFreesOcc f ("3":p) a
    mapFrees     f (x0, y0, z0, a0) =
        (\(x, (y, (z, a))) -> (x, y, z, a)) <$> mapFrees f (x0, (y0, (z0, a0)))

instance HasFrees a => HasFrees [a] where
    foldFrees    f      = foldMap  (foldFrees f)
    foldFreesOcc f c xs = mconcat $ (map (\(i,x) -> foldFreesOcc f (show i:c) x)) $ zip [(0::Int)..] xs
    mapFrees     f      = traverse (mapFrees f)

instance HasFrees a => HasFrees (Disj a) where
    foldFrees    f     = foldMap  (foldFrees f)
    foldFreesOcc f p d = foldFreesOcc f p (getDisj d)
    mapFrees     f     = traverse (mapFrees f)

instance HasFrees a => HasFrees (Conj a) where
    foldFrees    f     = foldMap  (foldFrees f)
    foldFreesOcc f p c = foldFreesOcc f p (getConj c)
    mapFrees     f     = traverse (mapFrees f)

instance (Ord a, HasFrees a) => HasFrees (S.Set a) where
    foldFrees   f    = foldMap  (foldFrees f)
    foldFreesOcc f p = foldMap (foldFreesOcc f ("0":p))
    mapFrees     f   = fmap S.fromList . mapFrees f . S.toList

instance (Ord k, HasFrees k, HasFrees v) => HasFrees (M.Map k v) where
    foldFrees f = M.foldrWithKey combine mempty
      where
        combine k v m = foldFrees f k `mappend` (foldFrees f v `mappend` m)
    foldFreesOcc f p = M.foldrWithKey combine mempty
      where
        combine k v m = foldFreesOcc f p (k,v) `mappend` m
    mapFrees f = fmap M.fromList . mapFrees f . M.toList


------------------------------------------------------------------------------
-- Pretty Printing
------------------------------------------------------------------------------

-- | Pretty print a 'LVar'.
prettyLVar :: Document d => LVar -> d
prettyLVar = text . show

-- | Pretty print a 'NodeId'.
prettyNodeId :: Document d => NodeId -> d
prettyNodeId = text . show

-- | Pretty print an @NTerm@.
prettyNTerm :: (Show v, Document d) => NTerm v -> d
prettyNTerm = prettyTerm (text . show)

-- | Pretty print an @LTerm@.
prettyLNTerm :: Document d => LNTerm -> d
prettyLNTerm = prettyNTerm


-- | Pretty print a literal for case generation.
showLitName :: Lit Name LVar -> String
showLitName (Con (Name FreshName n)) = "Const_fresh_" ++ show n
showLitName (Con (Name PubName   n)) = "Const_pub_"   ++ show n
showLitName (Var (LVar v s i))       = "Var_" ++ sortSuffix s ++ "_" ++ body
      where
        body | null v           = show i
             | i == 0           = v
             | otherwise        = show i ++ "_" ++ v

