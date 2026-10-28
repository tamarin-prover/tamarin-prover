{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | Formula sets whose elements satisfy 'normaliseStoredFormula'.
-- The constructor is private: all ways to introduce or transform formulas
-- restore that invariant, so unchanged substitutions may skip normalization.
module Theory.Constraint.System.StoredFormulas
    ( StoredFormulas
    , empty, singleton, fromList, toList, null
    , insert, delete, member, notMember, union
    ) where

import Prelude hiding (null)
import Control.DeepSeq (NFData(..))
import Data.Binary (Binary(..))
import qualified Data.Set as S

import Theory.Constraint.System.Guarded
import Theory.Model

-- Do not derive Generic or expose an unchecked constructor: either would
-- allow callers to introduce unnormalized formulas.
newtype StoredFormulas = StoredFormulas (S.Set LNGuarded)
    deriving (Eq, Ord)

instance Show StoredFormulas where
    showsPrec n (StoredFormulas fs) = showsPrec n fs

instance NFData StoredFormulas where
    rnf (StoredFormulas fs) = rnf fs

-- Preserve the set's encoding, but normalize on reading, including old data.
instance Binary StoredFormulas where
    put (StoredFormulas fs) = put fs
    get = fromList . S.toList <$> get

empty :: StoredFormulas
empty = StoredFormulas S.empty

singleton :: LNGuarded -> StoredFormulas
singleton = StoredFormulas . S.singleton . normaliseStoredFormula

fromList :: [LNGuarded] -> StoredFormulas
fromList = StoredFormulas . S.fromList . map normaliseStoredFormula

toList :: StoredFormulas -> [LNGuarded]
toList (StoredFormulas fs) = S.toList fs

null :: StoredFormulas -> Bool
null (StoredFormulas fs) = S.null fs

insert :: LNGuarded -> StoredFormulas -> StoredFormulas
insert fm (StoredFormulas fs) =
    StoredFormulas (S.insert (normaliseStoredFormula fm) fs)

-- Queries and deletion use structural equality, as Data.Set does. A raw
-- query must be normalized first; values from 'toList' already are.
member :: LNGuarded -> StoredFormulas -> Bool
member fm (StoredFormulas fs) = S.member fm fs

notMember :: LNGuarded -> StoredFormulas -> Bool
notMember fm = not . member fm

delete :: LNGuarded -> StoredFormulas -> StoredFormulas
delete fm (StoredFormulas fs) = StoredFormulas (S.delete fm fs)

union :: StoredFormulas -> StoredFormulas -> StoredFormulas
union (StoredFormulas a) (StoredFormulas b) = StoredFormulas (S.union a b)

instance Apply LNSubst StoredFormulas where
    apply subst original@(StoredFormulas fs)
      | nullSubst subst = original
      | otherwise = StoredFormulas $ S.map
          (\fm -> normaliseChanged fm (apply subst fm)) fs

-- The original formula is known to be normalized by the opaque set invariant.
normaliseChanged :: LNGuarded -> LNGuarded -> LNGuarded
normaliseChanged original updated
    | updated == original = original
    | otherwise = normaliseStoredFormula updated

instance HasFrees StoredFormulas where
    foldFrees f (StoredFormulas fs) = foldFrees f fs
    foldFreesOcc f ctx (StoredFormulas fs) = foldFreesOcc f ctx fs
    -- An arbitrary variable map may identify previously distinct operands.
    -- Rebuild the set after normalization, which may also change its order.
    mapFrees f (StoredFormulas fs) = StoredFormulas . S.fromList <$>
        traverse (\fm -> normaliseChanged fm <$> mapFrees f fm) (S.toList fs)
