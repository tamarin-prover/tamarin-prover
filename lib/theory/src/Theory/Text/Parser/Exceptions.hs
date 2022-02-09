{-# LANGUAGE FlexibleInstances #-}
-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
--               contributing in 2019: Robert Künnemann, Johannes Wocker
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Exceptions used in the parser

module Theory.Text.Parser.Exceptions(
      ParsingException(..)
    , liftMaybeToEx
    , liftEitherToEx
)
where

import           Prelude                    hiding (id, (.))
import           Data.Label
-- import           Data.Monoid                hiding (Last)
import qualified Control.Monad.Fail         as Fail
import qualified Control.Monad.Catch        as Catch
import           Text.PrettyPrint.Class     (render)
import           Term.Substitution
import           Theory

-- | Exception type for catching parsing errors
data ParsingException = UndefinedPredicate FactTag
                      | DuplicateItem OpenTheoryItem
                      | TryingToAddFreshRule

instance Show ParsingException where
    show (UndefinedPredicate facttag) = "undefined predicate "
                                         ++ showFactTagArity facttag
                                         -- ++ " in lemma: "
                                         -- ++ get lName lem
                                         -- ++ "."
    show (DuplicateItem (RuleItem ru)) = "duplicate rule: " ++ render (prettyRuleName $ get oprRuleE ru)
    show (DuplicateItem (LemmaItem lem)) =  "duplicate lemma: " ++ get lName lem
    show (DuplicateItem (RestrictionItem rstr)) =  "duplicate restriction: " ++ get rstrName rstr
    show (DuplicateItem (TextItem _)) =  undefined
    show (DuplicateItem (PredicateItem pr)) =  "duplicate predicate: " ++ render (prettyFact prettyLVar (get pFact pr))
    show (DuplicateItem (SapicItem (ProcessItem _))) =  undefined
    show (DuplicateItem (SapicItem (ProcessDefItem pDef))) =
        "duplicate process: " ++ get pName pDef
    show TryingToAddFreshRule = "The fresh rule is implicitely contained in the theory and does not need to be added."

instance Catch.Exception ParsingException
instance Fail.MonadFail (Either ParsingException) where
  fail = Fail.fail


liftEitherToEx :: (Catch.MonadThrow m, Catch.Exception e) => (t -> e) -> Either t a -> m a
liftEitherToEx _ (Right r)     = return r
liftEitherToEx constr (Left l) = Catch.throwM $ constr l

liftMaybeToEx :: (Catch.MonadThrow m, Catch.Exception e) => e -> Maybe a -> m a
liftMaybeToEx _      (Just r) = return r
liftMaybeToEx constr Nothing  = Catch.throwM constr