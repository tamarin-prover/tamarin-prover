{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
  -- spurious warnings for view patterns
-- |
-- Copyright   : (c) 2010-12 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Positions and replacement in terms.
module Term.Positions

where

import Term.VTerm
import Safe

-- Positions, subterm access, subterm replacement
----------------------------------------------------------------------

-- | A position in a term is a list of integers.
type Position = [Int]

-- | @t `atPos` p@ returns the subterm of term @t@ at position @p@.
--   The standard notation for @t `atPos` p@ is @t|_p@.
--   'atPos' accounts for AC symbols by interpreting n-ary operator
--   applications @*[t1,t2,..tk-1,tk]@ as binary applications
--   @t1*(t2*..(tk-1*tk)..)@.
atPos :: Ord a => Term a -> Position -> Term a
atPos t                                     []     = t
atPos (viewTerm -> FApp (AC _) (a:_))       (0:ps) =
    a `atPos` ps
atPos (viewTerm -> FApp (AC _) [_])         _      =
    error "Term.Positions.atPos: invalid position given"
atPos (viewTerm -> FApp fsym@(AC _) (_:as)) (1:ps) =
    (fApp fsym as) `atPos` ps
atPos (viewTerm -> FApp (AC _) [])          _      =
    error $ "Term.Positions.atPos: impossible, "
            ++"nullary AC symbol appliction"
atPos (viewTerm -> FApp  _ as)              (i:ps) = case atMay as i of
    Nothing -> error "Term.Positions.atPos: invalid position given"
    Just a  -> a `atPos` ps
atPos (viewTerm -> Lit _)                   (_:_)  =
    error "Term.Positions.atPos: invalid position given"

-- | @t `atPosMay` p@ returns Just the subterm of term @t@ at position @p@
--   if it exists, Nothing otherwise.
atPosMay :: Ord a => Term a -> Position -> Maybe (Term a)
atPosMay t                                     []     = Just t
atPosMay (viewTerm -> FApp (AC _) (a:_))       (0:ps) =
    a `atPosMay` ps
atPosMay (viewTerm -> FApp (AC _) [_])         _      = Nothing
atPosMay (viewTerm -> FApp fsym@(AC _) (_:as)) (1:ps) =
    (fApp fsym as) `atPosMay` ps
atPosMay (viewTerm -> FApp (AC _) [])          _      = Nothing
atPosMay (viewTerm -> FApp  _ as)              (i:ps) = do
  a <- as `atMay` i
  t <- a `atPosMay` ps
  return t
atPosMay (viewTerm -> Lit _)                   (_:_)  = Nothing

-- | @findPos t s@ returns the position of the term @s@ inside term @t@ if @s@
--  is a subterm, or Nothing otherwise.
findPos :: Ord a => Term a -> Term a -> Maybe [Position]
findPos t t' | t == t'            = Just [[]]
findPos t (viewTerm -> FApp _ ts) = foldr f Nothing $ zip [0..] $ map (findPos t) ts
  where
    f (_, Nothing) s        = s
    f (x, Just p)  Nothing  = Just (map (x:) p)
    f (x, Just p)  (Just s) = Just (s++(map (x:) p))
findPos _ (viewTerm -> Lit _)     = Nothing

-- | @t `replacePos` (s,p)@ returns the term @t'@ where the subterm at position @p@
--   is replaced by @s@. The standard notation for @t `replacePos` (s,p)@ is @t[s]_p@.
--   'replacePos' accounts for AC symbols in the same ways as 'atPos'.
--   FIXME: The AC can be optimized.
replacePos :: Ord a => Term a -> (Term a, Position) -> Term a
replacePos _                                     (s,[])   = s
replacePos (viewTerm -> FApp fsym@(AC _) (a:as)) (s,0:ps) =
    fApp fsym ((a `replacePos` (s,ps)):as)
replacePos (viewTerm -> FApp fsym@(AC _) (a:as)) (s,1:ps) =
    fApp fsym [a, (fApp fsym as) `replacePos` (s,ps)]
replacePos (viewTerm -> FApp      (AC _) _)        _      =
    error "Term.Positions.replacePos: invalid position given"
replacePos (viewTerm -> FApp fsym as)            (s,i:ps) =
    if 0 <= i && i < length as
    then fApp fsym ((take i as)++[as!!i `replacePos` (s,ps)]++(drop (i+1) as))
    else error "Term.Positions.replacePos: invalid position given"
replacePos (viewTerm -> Lit _)        (_,_:_)             =
    error "Term.Positions.replacePos: invalid position given"

-- | @positionsNonVar t@ returns all the non-variable positions in the term @t@.
--   'positionsNonVar' accounts for AC symbols in the same ways as 'atPos'.
positionsNonVar :: VTerm a b -> [Position]
positionsNonVar =
    go
  where
    go (viewTerm -> Lit  (Con _))    = [[]]
    go (viewTerm -> Lit  (Var _))    = []
    go (viewTerm -> FApp (AC _)  as) = []:concat (zipWith (\i a -> map ((position i len)++) (go a))
                                                          [0..] as)
        where len = length as
    go (viewTerm -> FApp _       as) = []:concat (zipWith (\i a -> map (i:) (go a)) [0..] as)

    position i len | i == len - 1 = replicate i 1
                   | otherwise    = replicate i 1 ++ [0]

-- | @positions t@ returns all the positions in the term @t@.
--   'positions' accounts for AC symbols in the same ways as 'atPos'.
positions :: (Show a, Show b) => VTerm a b -> [Position]
positions =
    go
  where
    go (viewTerm -> Lit  (Con _))    = [[]]
    go (viewTerm -> Lit  (Var _))    = [[]]
    go (viewTerm -> FApp (AC _)  as) = []:concat (zipWith (\i a -> map ((position i len)++) (go a))
                                                          [0..] as)
        where len = length as
    go (viewTerm -> FApp _       as) = []:concat (zipWith (\i a -> map (i:) (go a)) [0..] as)

    position i len | i == len - 1 = replicate i 1
                   | otherwise    = replicate i 1 ++ [0]

-- Return the deepest "protected" subterm with respect to a given position
-- NB: here anything but a pair or an AC symbol is an "encryption"!
deepestProtSubterm :: (Show a, Eq a) => Term a -> Position -> Maybe (Term a)
deepestProtSubterm term = f term term
  where
    f st _                         []
       | st == term && (isPair term || isAC term) = Nothing
       -- If there is no protected subterm, return Nothig!
    f st _                         []
       | otherwise                                = Just st
    f st t@(viewTerm -> FApp _ as) (i:is) = case atMay as i of
          Nothing -> error "deepestProtSubterm: invalid position given"
          Just a  -> f (if isPair t || isAC t then st else t) a is
