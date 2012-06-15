-- |
-- Copyright   : (c) 2010 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Support functions for exploiting Unicode characters.
module Text.Unicode where


-- | Convert a subscriptable character to its subsript.
subscriptChar :: Char -> Char
subscriptChar c = case c of
    '0' -> '₀'
    '1' -> '₁'
    '2' -> '₂'
    '3' -> '₃'
    '4' -> '₄'
    '5' -> '₅'
    '6' -> '₆'
    '7' -> '₇'
    '8' -> '₈'
    '9' -> '₉'
    '+' -> '₊'
    '-' -> '₋'
    '=' -> '₌'
    '(' -> '₍'
    ')' -> '₎'
    _   -> c  -- FIXME: Add further characters from
              --   http://tlt.its.psu.edu/suggestions/international/bylanguage/mathchart.html#super

-- | Convert all subscriptable characters to subscripts.
subscript :: String -> String
subscript = map subscriptChar
