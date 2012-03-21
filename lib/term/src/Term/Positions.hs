-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Benedikt Schmidt <beschmi@gmail.com>
--
-- Positions and replacement in terms.
module Term.Positions where

import Term.Term
import Safe

-- Positions, subterm access, subterm replacement
----------------------------------------------------------------------

-- | A position in a term is a list of integers.
type Position = [Int]

-- | @t >* p@ returns the subterm of term @t@ at position @p@.
--   The standard notation for @t >* p@ is @t|_p@.
(>*) :: Term a -> Position -> Term a
t              >* [] = t
(FApp _ as)    >* (i:ps) = case atMay as i of
                             Nothing -> error "Term.Positions.(>*): invalid position given"
                             Just a  -> a >* ps
(Lit _)        >* (_:_)  =  error "Term.Positions.(>*): invalid position given"


-- | @t >=*(s,p)@ returns the term @t'@ where the subterm a position @p@
--   is replaced by @s@. The standard notation for @t >=*(s,p)@ is @t[s]_p@.
(>=*) :: Term a -> (Term a, Position) -> Term a
_              >=* (s,[]) = s
(FApp fsym as) >=* (s,i:ps) = if 0 <= i && i < length as
                                then FApp fsym ((take i as)++[as!!i >=* (s,ps)]++(drop (i+1) as))
                                else error "Term.Positions.(>=*): invalid position given"
(Lit _)        >=* (_,_:_)  =  error "Term.Positions.(>=*): invalid position given"

-- | @positionsNonVar t@ returns all the non-variable positions in the term @t@.
positionsNonVar :: VTerm a b -> [Position]
positionsNonVar t = go t
  where go (Lit (Con _))  = [[]]
        go (Lit (Var _))  = []
        go (FApp _    as) = []:concat (zipWith (\i a -> map (i:) (go a)) [0..] as)