{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveDataTypeable         #-}
-- remove the two benign defaults

-- |
-- Copyright   : (c) 2010 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
--
-- A simple color module for handling RGB and HSV representations of colors.
module Data.Color (
  -- * Datatypes
    RGB(..)
  , HSV(..)
  , rgbToHex
  , hexToRGB
  , hsvToHex

  -- ** Predefined colors
  , red
  , green
  , blue

  -- ** Conversions
  , rgbToGray
  , hsvToGray
  , rgbToHSV
  , hsvToRGB

  -- * Color Palettes
  , colorGroups
  , lightColorGroups

) where

{- IDEA: Provide color datastructure together with nice and usable color
 -       palettes for reporting various data
 -}

import GHC.Generics     (Generic)
import Control.DeepSeq  (NFData)
import Data.Binary      (Binary)
import Data.Data        (Data)
import Numeric          (showHex, readHex)
import Safe             (headMay)

-- import Text.XHtml.Strict
-- import Text.XHtml.Table

data RGB a = RGB {
    rgbR :: !a
  , rgbG :: !a
  , rgbB :: !a
  }
  deriving( Eq, Ord, Generic, Data, NFData, Binary )

instance Show a => Show (RGB a) where
  show (RGB r g b) = "RGB("++show r++", "++show g++", "++show b++")"

instance Functor RGB where
  fmap f (RGB r g b) = RGB (f r) (f g) (f b)

red, green, blue :: Fractional t => RGB t
red   = RGB 1.0 0.0 0.0
green = RGB 0.0 1.0 0.0
blue  = RGB 0.0 0.0 1.0

data HSV a = HSV {
    hsvH :: !a
  , hsvS :: !a
  , hsvV :: !a
  }
  deriving( Eq, Ord )

instance Show a => Show (HSV a) where
  show (HSV h s v) = "HSV("++show h++", "++show s++", "++show v++")"

instance Functor HSV where
  fmap f (HSV h s v) = HSV (f h) (f s) (f v)


------------------------------------------------------------------------------
-- Colorspace conversion
------------------------------------------------------------------------------

-- | RGB to HSV conversion.
-- Pre: 0 <= r,g,b <= 1
-- (Source: http://de.wikipedia.org/wiki/HSV-Farbraum)
rgbToHSV :: (Fractional t, Ord t) => RGB t -> HSV t
rgbToHSV (RGB r g b) = HSV h' s v
  where
  ub = max r (max g b)
  lb = min r (min g b)

  h  | ub == lb  = 0
     | ub == r   = 60 * (    (g-b)/(ub-lb))
     | ub == g   = 60 * (2 + (b-r)/(ub-lb))
     | otherwise = 60 * (4 + (r-g)/(ub-lb))

  h' | h < 0 = h + 360
     | otherwise = h

  s  | ub == 0   = 0
     | otherwise = (ub-lb)/ub

  v  = ub

-- | HSV to RGB conversion.
-- Pre: 0 <= h <= 360 and 0 <= s,v <= 1
-- (Source: http://de.wikipedia.org/wiki/HSV-Farbraum)
hsvToRGB :: RealFrac t => HSV t -> RGB t
hsvToRGB (HSV h s v) = case hIdx of
  0 -> RGB v t p
  1 -> RGB q v p
  2 -> RGB p v t
  3 -> RGB p q v
  4 -> RGB t p v
  5 -> RGB v p q
  _ -> error "hsvToRGB: hue outside of range [0..360]"
  where
  hIdx = floor (h / 60)
  f    = h/60 - fromIntegral (hIdx::Int)
  p    = v*(1-s)
  q    = v*(1-s*f)
  t    = v*(1-s*(1-f))

hsvToGray :: Num t => HSV t -> HSV t
hsvToGray (HSV h _ v) = HSV h 0 v

rgbToGray :: Ord t => RGB t -> t
rgbToGray (RGB r g b) = max r (max g b)

------------------------------------------------------------------------------
-- String output
------------------------------------------------------------------------------

-- | Hexadecimal representation of an RGB value
rgbToHex :: RealFrac t => RGB t -> String
rgbToHex (RGB r g b) = ('#':) . showHex' r . showHex' g . showHex' b $ ""
  where showHex' f
          | i <= 15   = ('0':) . showHex i
          | otherwise = showHex i
          where
          i :: Int
          i = max 0 (min 255 (floor (256 * f)))

hexToRGB :: RealFrac t => String -> Maybe (RGB t)
hexToRGB [r1,r2,g1,g2,b1,b2] = do
    (r,_) <- headMay $ readHex [r1,r2]
    (g,_) <- headMay $ readHex [g1,g2]
    (b,_) <- headMay $ readHex [b1,b2]
    return (RGB (r / 255) (g / 255) (b / 255))
hexToRGB _ = Nothing

-- | Hexadecimal representation of an HSV value; i.e., of its corresponding RGB
-- value.
hsvToHex :: RealFrac t => HSV t -> [Char]
hsvToHex = rgbToHex . hsvToRGB


------------------------------------------------------------------------------
-- HSV Color Palettes
------------------------------------------------------------------------------

data ColorParams t = ColorParams {
    cpScale   :: !t
  , cpZeroHue :: !t
  , cpVBottom :: !t
  , cpVRange  :: !t
  , cpSBottom :: !t
  , cpSRange  :: !t
  }
  deriving( Eq, Ord, Show )

-- | From a list of group sizes build a function assigning every element a
-- unique color, nicely distributed such that they are well differentiated both
-- using color and monochrome displays.
genColorGroups :: RealFrac t =>
                  ColorParams t
               -> [Int]                -- ^ List of group sizes.
               -> [((Int,Int),(HSV t))]
genColorGroups (ColorParams {
              cpScale = scale
            , cpZeroHue = zeroHue
            , cpVBottom = vBot, cpVRange = vRan
            , cpSBottom = sBot, cpSRange = sRan
            }) groups =
  do
    (groupIdx, groupSize) <- zip [0.. ] groups
    elemIdx <- [0..groupSize - 1]
    let h = toShiftedGroupHue groupIdx (fromIntegral elemIdx / fromIntegral groupSize)
        v = vBot + vRan * toGroupHue groupIdx (fromIntegral elemIdx / fromIntegral groupSize)
        s = sBot + sRan * toGroupHue groupIdx (fromIntegral elemIdx / fromIntegral groupSize)
        color = HSV (360*h) s v
    return ((groupIdx, elemIdx), color)
  where
    nGroups :: Int
    nGroups = length groups

    toGroupHue g h = (
      fromIntegral g    + -- base position
      0.5 * (1 - scale) + -- left margin
            (h * scale)   -- position in margin
      ) / (fromIntegral nGroups)

    toShiftedGroupHue g h =
      snd . properFraction $ toGroupHue g h + 1 +
      (zeroHue/360) - toGroupHue 0 0.5


-- | A good default style for the 'genColorGroups' color palette function. The
-- parameter shifts the hue for the first group.
colorGroupStyle :: RealFrac t => t -> ColorParams t
colorGroupStyle zeroHue = ColorParams {
    cpScale   = 0.6
  , cpZeroHue = zeroHue
  , cpVBottom = 0.75, cpVRange = 0.2
  , cpSBottom = 0.4,  cpSRange = 0.00
  }

-- | Build color groups according to the list of group sizes using the default
-- 'colorGroupStyle' for the function 'genColorGroups'.
colorGroups :: RealFrac t => t -> [Int] -> [((Int, Int), HSV t)]
colorGroups zeroHue = genColorGroups (colorGroupStyle zeroHue)


-- | A good light color style for the @genColorGroups@ color palette
-- function. The parameter shifts the hue for the first group.
lightColorGroupStyle :: RealFrac t => t -> ColorParams t
lightColorGroupStyle zeroHue = ColorParams {
    cpScale   = 0.6
  , cpZeroHue = zeroHue
  , cpVBottom = 0.8, cpVRange = 0.15
  , cpSBottom = 0.3,  cpSRange = 0.00
  }

-- | Build color groups according to the list of group sizes using the
-- default light 'lightColorGroupStyle' for the function
-- 'genColorGroups'.
lightColorGroups :: RealFrac t => t -> [Int] -> [((Int, Int), HSV t)]
lightColorGroups zeroHue = genColorGroups (lightColorGroupStyle zeroHue)


------------------------------------------------------------------------------
-- Testing: Html Table with group colors
------------------------------------------------------------------------------

{-

colorTable :: Double -> (HSV Double -> HSV Double) -> [Int] -> Html
colorTable zeroHue conv groups =
  table . toHtml . besides $ map col [0..length groups-1]
  where
  col i = aboves [cell $ (td ! [getStyle i j]) (stringToHtml (show (i,j)))
                 | j <- [0..(groups !! i) - 1] ]
  color = colorGroups zeroHue groups
  getStyle i j = thestyle ("background-color: "++ hsvToHex (conv $ color i j))

colorFile :: Double -> FilePath -> [Int] -> IO ()
colorFile zeroHue outF groups = do
  let html = colorTable zeroHue id        groups +++
             colorTable zeroHue hsvToGray groups
  writeFile outF $ prettyHtml html

-}

