{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-# LANGUAGE FlexibleContexts, TupleSections, NamedFieldPuns #-}
-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Types for communicating with Maude.
module Term.Maude.Types where

import Term.Term
import Term.LTerm
import Term.Builtin.Rules
import Term.Substitution
import Term.SubtermRule

import Utils.Misc
import Extension.Prelude
import Control.Monad.Fresh
import Control.Monad.Bind

import Text.ParserCombinators.Parsec hiding (many, optional, (<|>))
import Control.Applicative
import Data.Traversable
import Data.List
import Data.Monoid
import Data.List.Split hiding (sepBy, oneOf)
import Data.Maybe
import qualified Data.Map as M
import Data.Map ( Map )

-- Maude Terms
----------------------------------------------------------------------

data MaudeLit = MaudeVar   Int LSort
              | FreshVar   Int LSort
              | MaudeConst Int LSort
  deriving (Eq, Ord, Show)

type MTerm = Term MaudeLit

type MSubst = [((LSort, Int), MTerm)]


-- Maude Signatures
----------------------------------------------------------------------

-- | The required information to define a @Maude functional module@.
data MaudeSig = MaudeSig
    { enableDH   :: Bool
    , enableXor  :: Bool
    , enableMSet :: Bool
    , funSig     :: FunSig  -- ^ function signature not including the function symbols for DH, Xor, MSet
    , stRules    :: [StRule]
    }
    deriving (Ord, Show, Eq)

-- | The empty maude signature.
emptyMaudeSig :: MaudeSig
emptyMaudeSig = MaudeSig False False False [] []

-- | A monoid instance to combine maude signatures.
instance Monoid MaudeSig where
    (MaudeSig dh xor mset funsig stRules) `mappend` (MaudeSig dh' xor' mset' funsig' stRules') =
        MaudeSig (dh || dh') (xor || xor')  (mset || mset')
                 (sortednub $ funsig ++ funsig')  (sortednub $ stRules ++ stRules')
    mempty = emptyMaudeSig

-- | Maude signatures for the AC symbols.
dhMaudeSig, xorMaudeSig, msetMaudeSig :: MaudeSig
dhMaudeSig   = emptyMaudeSig { enableDH   = True }
xorMaudeSig  = emptyMaudeSig { enableXor  = True }
msetMaudeSig = emptyMaudeSig { enableMSet = True }

-- | Maude signatures for the default subterm symbols.
pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, hashMaudeSig :: MaudeSig
pairMaudeSig      = emptyMaudeSig { funSig = pairFunSig,      stRules = pairRules   }
symEncMaudeSig    = emptyMaudeSig { funSig = symEncFunSig,    stRules = symEncRules }
asymEncMaudeSig   = emptyMaudeSig { funSig = asymEncFunSig,   stRules = asymEncRules }
signatureMaudeSig = emptyMaudeSig { funSig = signatureFunSig, stRules = signatureRules }
hashMaudeSig      = emptyMaudeSig { funSig = hashFunSig,      stRules = [] }

-- | The minimal maude signature.
minimalMaudeSig :: MaudeSig
minimalMaudeSig = pairMaudeSig

-- | Maude signatures with all builtin symbols.
allMaudeSig :: MaudeSig
allMaudeSig = mconcat
    [ dhMaudeSig, xorMaudeSig, msetMaudeSig
    , pairMaudeSig, symEncMaudeSig, asymEncMaudeSig, signatureMaudeSig, hashMaudeSig ]

-- | @rrulesForMaudeSig msig@ returns all rewriting rules including the rules
--   for xor, dh, and multiset.
rrulesForMaudeSig :: MaudeSig -> [RRule LNTerm]
rrulesForMaudeSig (MaudeSig {enableXor, enableDH, enableMSet, stRules}) =
    map stRuleToRRule stRules
    ++ (if enableDH   then dhRules   else [])
    ++ (if enableXor  then xorRules  else [])
    ++ (if enableMSet then msetRules else [])

-- | @funSigForMaudeSig msig@ returns all non-AC function symbols including the
--   function symbols for xor, dh, and multiset.
funSigForMaudeSig :: MaudeSig -> FunSig
funSigForMaudeSig (MaudeSig {enableXor, enableDH, enableMSet, funSig}) =
    funSig
    ++ (if enableDH   then dhFunSig   else [])
    ++ (if enableXor  then xorFunSig  else [])
    ++ (if enableMSet then msetFunSig else [])

-- Convert between MTerms and LNTerms
------------------------------------------------------------------------

-- | Convert an @LNTerm@ to an @MTerm@.
lTermToMTerm' :: (MonadBind (Lit Name LVar) MaudeLit m, MonadFresh m)
              => LNTerm -- ^ The term to translate.
              -> m MTerm
lTermToMTerm' = lTermToMTerm sortOfName

-- | Convert an @LNTerm@ with arbitrary names to an @MTerm@.
lTermToMTerm :: (MonadBind (Lit c LVar) MaudeLit m, MonadFresh m, Show (Lit c LVar), Ord c)
             => (c -> LSort) -- ^ A function that returns the sort of a constant.
             -> VTerm c LVar -- ^ The term to translate.
             -> m MTerm
lTermToMTerm sortOf =
  traverse exportLit
 where
  exportLit a@(Var lv) =
    importBinding (\_ i -> MaudeVar i (lvarSort lv)) a "x"
  exportLit a@(Con n) = importBinding (\_ i -> MaudeConst i (sortOf n)) a "a"

-- | Convert a 'MaudeTerm' to an 'LNTerm' under the assumption that the bindings
-- for the constants are already available.
--
-- Use @runBindCtxt@ with the inverted map from the @lTermtoMaudeTerm@ conversion to
-- ensure this.
mTermToLNTerm :: (MonadBind MaudeLit (Lit c LVar) m, MonadFresh m, Show (Lit c LVar), Ord c, Show c)
             => String -- ^ Name hint for freshly generated variables.
             -> MTerm  -- ^ The maude term to convert.
             -> m (VTerm c LVar)
mTermToLNTerm nameHint =
  traverse importLit
 where
  importLit a@(MaudeVar _ lsort) = importBinding (\n i -> Var (LVar n lsort i)) a nameHint
  importLit a@(FreshVar _ lsort) = importBinding (\n i -> Var (LVar n lsort i)) a nameHint
  importLit a = fromMaybe (error $ "fromMTerm: unknown constant `" ++ show a ++ "'") <$>
                  lookupBinding a


-- Back and forth conversions
------------------------------------------------------------------------

-- | Run a @BindT (Lit c LVar) MaudeLit Fresh@ computation
--   with an empty fresh supply and an empty binding map and return
--   the result and the resulting inverted binding map.
runConversion :: Ord c
              => BindT (Lit c LVar) MaudeLit Fresh a -- ^ Computation to execute.
              -> (a, Map MaudeLit (Lit c LVar))
runConversion to = (x, invertMap bindings)
 where (x, bindings) = runBindT to noBindings `evalFresh` nothingUsed

-- | Run a @BindT  MaudeLit (Lit c LVar) Fresh@ computation using the
--   supplied binding map and the corresponding fresh supply.
runBackConversion :: BindT MaudeLit (Lit c LVar) Fresh a -- ^ Computation to execute.
                  -> Map MaudeLit (Lit c LVar) -- ^ Binding map that should be used.
                  -> a
runBackConversion back bindings =
  evalBindT back bindings `evalFreshAvoiding` M.elems bindings

-- Conversion between Maude and standard substitutions
------------------------------------------------------------------------

-- | @msubstToLSubstVFresh bindings substMaude@ converts a substitution
--   returned by Maude to a 'VFresh' substitution. It expects that the
--   range of the maude substitution contains only fresh variables in its
--   range and raises an error otherwise.
msubstToLSubstVFresh :: (Ord c, Show (Lit c LVar), Show c)
                     => Map MaudeLit (Lit c LVar) -- ^ The binding map to use for constants.
                     -> MSubst -- ^ The maude substitution.
                     -> SubstVFresh c LVar
msubstToLSubstVFresh bindings substMaude
  | not $ null [i | (_,t) <- substMaude, MaudeVar _ i <- lits t] =
      error $ "msubstToLSubstVFresh: nonfresh variables in `"++show substMaude++"'"
  | otherwise = removeRenamings $ substFromListVFresh slist
 where
  slist = runBackConversion (traverse translate substMaude) bindings
  -- try to keep variable name for xi -> xj mappings
  -- commented out, seems wrong
  --  translate ((s,i), mt@(Lit (FreshVar _ _))) = do
  --    lv <- lookupVar s i
  --    (lv,)  <$> mTermToLNTerm (lvarName lv) mt
  translate ((s,i),mt) = (,) <$> lookupVar s i <*> mTermToLNTerm "x" mt
  lookupVar s i = do b <- lookupBinding (MaudeVar i s)
                     case b of
                       Just (Var lv) -> return lv
                       _ -> error $ "msubstToLSubstVFrsh: binding for maude variable `"
                                    ++show (s,i) ++"' not found in "++show bindings

-- | @msubstToLSubstVFree bindings substMaude@ converts a substitution
--   returned by Maude to a 'VFree' substitution. It expects that the
--   maude substitution contains no fresh variables in its range and raises an
--   error otherwise.
msubstToLSubstVFree ::  (Ord c, Show (Lit c LVar), Show c)
                    => Map MaudeLit (Lit c LVar) -> MSubst -> Subst c LVar
msubstToLSubstVFree bindings substMaude
  | not $ null [i | (_,t) <- substMaude, FreshVar _ i <- lits t] =
      error $ "msubstToLSubstVFree: fresh variables in `"++show substMaude
  | otherwise = substFromList slist
 where
  slist = evalBindT (traverse translate substMaude) bindings
          `evalFreshAvoiding` M.elems bindings
  translate ((s,i),mt) = (,) <$> lookupVar s i <*> mTermToLNTerm "x" mt
  lookupVar s i = do b <- lookupBinding (MaudeVar i s)
                     case b of
                       Just (Var lv) -> return lv
                       _ -> error $ "msubstToLSubstVFree: binding for maude variable `"
                                    ++show (s,i)++"' not found in "++show bindings


-- Pretty printing of Maude terms.
------------------------------------------------------------------------

-- | Pretty print an 'LSort'.
ppMSort :: LSort -> String
ppMSort LSortPub   = "Pub"
ppMSort LSortFresh = "Fresh"
ppMSort LSortMsg   = "Msg"
ppMSort LSortNode  = "Node"
ppMSort LSortMSet  = "MSet"

-- | Used to prevent clashes with predefined Maude function symbols
--   like @true@
funsymPrefix :: String
funsymPrefix = "tamX"

-- | Pretty print an AC symbol for Maude.
ppMaudeACSym :: ACSym -> String
ppMaudeACSym o =
    funsymPrefix
    ++ case o of
           Mult -> "mult"
           MUn  -> "mun"
           Xor  -> "xor"

-- | @ppMaude t@ pretty prints the term @t@ for Maude.
ppMaude :: Term MaudeLit -> String
ppMaude (Lit (MaudeVar i lsort))  = "x"++ show i ++":"++ppMSort lsort
ppMaude (Lit (MaudeConst i LSortFresh)) = "f("++ show i ++")"
ppMaude (Lit (MaudeConst i LSortPub))   = "p("++ show i ++")"
ppMaude (Lit (MaudeConst i LSortMsg))   = "c("++ show i ++")"
ppMaude (Lit (MaudeConst i LSortNode))  = "n("++ show i ++")"
ppMaude (Lit (MaudeConst i LSortMSet))  = "m("++ show i ++")"
ppMaude (Lit (FreshVar _ _))            = error "ppMaude: FreshVar not allowed"
ppMaude (FApp (NonAC (fsym,_)) [])      = funsymPrefix++fsym
ppMaude (FApp (NonAC (fsym,_)) as)      =
    funsymPrefix++fsym++"("++(intercalate "," (map ppMaude as))++")"
ppMaude (FApp (AC op) as)               =
    ppMaudeACSym op ++ "("++(intercalate "," (map ppMaude as))++")"
ppMaude (FApp List as)                  =
    funsymPrefix++"list(" ++ ppList as ++ ")"
  where
    ppList []     = funsymPrefix++"nil"
    ppList (x:xs) = funsymPrefix++"cons(" ++ ppMaude x ++ "," ++ ppList xs ++ ")"

-- Parser for Maude output
------------------------------------------------------------------------

-- | @parseSolutions reply@ takes a @reply@ to a unification query
--   returned by Maude and extracts the unifiers.
parseMaudeReply :: String -> [Either ParseError MSubst]
parseMaudeReply reply =
  case find (\s -> s `elem` ["No unifier.", "No match."]) linesReply of
    Just _  -> []
    Nothing -> map parseSolution $ splitOn [""] $
                 dropWhile (\s -> not ("Solution" `isPrefixOf` s)) linesReply
 where
  linesReply = lines reply

-- | @parseSolution l@ parses a single solution returned by Maude.
parseSolution :: [String] -> Either ParseError MSubst
parseSolution l = parse pSolution "" (unlines l)
 where
  pSolution = do
    string "Solution" <* space
    many1 digit <* newline
    (many1 pmap <|> (string "empty substitution" *> newline *> return []))
  pmap = (,) <$> (flip (,) <$> (char 'x' *> pNat <* string ":") <*> psort)
            <*> (space *> string "-->" *> space *> expr <* newline)

-- | Parse an 'MSort'.
psort :: GenParser Char st LSort
psort =  string "Pub"   *> return LSortPub
     <|> string "Fresh" *> return LSortFresh
     <|> try (string "Msg"   *> return LSortMsg)
     <|> string "MSet"  *> return LSortMSet
     <|> string "Node"  *> return LSortNode


-- | @expr@ is a parser for Maude Msg expressions.
--   We parse list, cons and nil as FreeSym. We therefore
--   have to fixup the term later on.
expr :: GenParser Char st MTerm
expr =  fixup <$> p
  where
    p = Lit <$> ( flip MaudeConst <$> try parseConstSym <*> pNat <* string ")")
     <|> Lit <$> (MaudeVar <$> (try (string "x" *> pNat <* string ":")) <*> psort)
     <|> Lit <$> (FreshVar <$> (string "#" *> pNat <* string ":") <*> psort)
     <|> do op <- try parseACSym
            args <- sepBy expr commaWS
            char ')'
            return $ FApp (AC op) args
     <|> do fsym <- try (parseFreeSym <* string "(")
            args <- sepBy expr commaWS
            string ")"
            return $ FApp (NonAC (fsym, length args)) args
     <|> do fsym <- parseFreeSym
            return $ FApp (NonAC (fsym, 0)) []

    parseConstSym =  (string "f(" *> pure LSortFresh)
                 <|> (string "p(" *> pure LSortPub)
                 <|> (string "c(" *> pure LSortMsg)
                 <|> (string "n(" *> pure LSortNode)
                 <|> (string "m(" *> pure LSortMSet)

    parseACSym =  try (string (ppMaudeACSym Mult++"(")) *> return Mult
              <|> try (string (ppMaudeACSym MUn++"("))  *> return MUn
              <|> (string (ppMaudeACSym Xor++"("))  *> return Xor

    parseFreeSym = string funsymPrefix *> many1 (oneOf (['a' .. 'z']++['A'..'Z']))
 
    fixup t@(Lit _)                     = t
    fixup (FApp (NonAC ("list",1)) [a]) = FApp List (collect a)
      where
        collect (FApp (NonAC ("cons",2)) [x,xs]) = fixup x:collect xs
        collect (FApp (NonAC ("nil",0))   [])    = []
        collect t                                =
          error $"MTerm.expr: fixup failed, Maude returned invalid term, "++show t
    fixup (FApp (NonAC ("list",_)) _)   =
        error "MTerm.expr: fixup failed, Maude returned invalid term, list not unary"
    fixup (FApp x ts)                   = FApp x $ map fixup ts

-- | @parseSolution l@ parses a single solution returned by Maude.
parseReduceSolution :: String -> Either ParseError MTerm
parseReduceSolution s = case lines s of
    [_,_,_,res] -> parse pReduceSolution "" res
    _           -> fail ("parseReduceSolution: invalid Maude output: " ++ s)
 where
  pReduceSolution = do
    string "result" <* space
    (psort <|> (string "TOP" *> pure LSortPub))
      -- FIXME: clean up, we use TOP for lists
    string ":" *> space *> expr
