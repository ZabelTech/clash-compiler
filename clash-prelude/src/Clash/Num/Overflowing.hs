{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Clash.Num.Overflowing
  ( Overflowing(fromOverflowing, hasOverflowed)
  , toOverflowing
  , clearOverflow
  ) where

import Prelude hiding (even, odd)

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Function (on)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import GHC.TypeLits (KnownNat, type (+))

import Clash.Class.BitPack (BitPack(..))
import Clash.Class.Num (SaturationMode(SatWrap, SatZero), SaturatingNum(..))
import Clash.Class.Parity (Parity(..))
import Clash.XException (NFDataX, ShowX)

data Overflowing a = Overflowing
  { fromOverflowing :: a
  , hasOverflowed :: Bool
  }
  deriving stock (Generic, Show)
  deriving anyclass (Binary, Hashable, NFData, NFDataX, ShowX)

toOverflowing :: a -> Overflowing a
toOverflowing x = Overflowing x False

clearOverflow :: Overflowing a -> Overflowing a
clearOverflow x = x { hasOverflowed = False }

instance (Eq a) => Eq (Overflowing a) where
  (==) = (==) `on` fromOverflowing

instance (Ord a) => Ord (Overflowing a) where
  compare = compare `on` fromOverflowing

instance (BitPack a, KnownNat (BitSize a + 1)) => BitPack (Overflowing a) where
  type BitSize (Overflowing a) = BitSize a + 1

  -- Default instance, no explicit implementations.

instance (Parity a) => Parity (Overflowing a) where
  even = even . fromOverflowing
  odd = odd . fromOverflowing

instance (Bounded a, Ord a, SaturatingNum a) => Num (Overflowing a) where
  Overflowing x a + Overflowing y b
    -- Overflow
    | y > 0
    , x > satSub SatWrap maxBound y
    = withOverflow True

    -- Underflow
    | y < 0
    , x < satSub SatWrap minBound y
    = withOverflow True

    | otherwise
    = withOverflow (a || b)
   where
    withOverflow = Overflowing (satAdd SatWrap x y)

  Overflowing x a - Overflowing y b
    -- Overflow
    | y < 0
    , x > satAdd SatWrap maxBound y
    = withOverflow True

    -- Underflow
    | y > 0
    , x < satAdd SatWrap minBound y
    = withOverflow True

    | otherwise
    = withOverflow (a || b)
   where
    withOverflow = Overflowing (satSub SatWrap x y)

  Overflowing x a * Overflowing y b
    -- Checking bounds needs integer division, but if we re-use satMul then
    -- we can avoid adding an Integral constraint.
    | x /= 0
    , y /= 0
    , satMul SatZero x y == 0
    = withOverflow True

    | otherwise
    = withOverflow (a || b)
   where
    withOverflow = Overflowing (satMul SatWrap x y)

  negate n@(Overflowing x a)
    | 0 == x = n
    | 0 <= minBound @a = withOverflow True
    | x == minBound = withOverflow True
    | otherwise = withOverflow a
   where
    withOverflow = Overflowing (negate x)

  -- If the number is signed, the absolute may result in an overflow. This
  -- assumes a twos-complement representation, meaning negate minBound
  -- overflows and wraps back to itself.
  abs (Overflowing x a)
    | x == minBound && x < 0 = Overflowing x True
    | otherwise = Overflowing (abs x) a

  signum (Overflowing x a) =
    Overflowing (signum x) a

  fromInteger i =
    Overflowing (fromInteger i) False

instance (Bounded a) => Bounded (Overflowing a) where
  minBound = Overflowing minBound False
  maxBound = Overflowing maxBound False

instance (Enum a, Eq a, SaturatingNum a) => Enum (Overflowing a) where
  succ (Overflowing x a)
    | x == maxBound = withOverflow True
    | otherwise = withOverflow a
   where
    withOverflow = Overflowing (satSucc SatWrap x)

  pred (Overflowing x a)
    | x == minBound = withOverflow True
    | otherwise = withOverflow a
   where
    withOverflow = Overflowing (satPred SatWrap x)

  toEnum i =
    Overflowing (toEnum i) False

  fromEnum (Overflowing x _) =
    fromEnum x

instance (Real a, SaturatingNum a) => Real (Overflowing a) where
  toRational = toRational . fromOverflowing

instance (Integral a, SaturatingNum a) => Integral (Overflowing a) where
  quotRem (Overflowing x a) (Overflowing y b)
    -- minBound / -1 overflows to minBound
    | x == minBound && y < 0 && abs y == 1 =
        withOverflow True

    | otherwise =
        withOverflow (a || b)
   where
    withOverflow o =
      let (q, r) = quotRem x y
       in (Overflowing q o, Overflowing r o)

  toInteger (Overflowing x _) =
    toInteger x

instance (Fractional a, Ord a, SaturatingNum a) => Fractional (Overflowing a) where
  recip x =
    x { fromOverflowing = recip (fromOverflowing x) }

  fromRational i =
    Overflowing (fromRational i) False

instance (RealFrac a, SaturatingNum a) => RealFrac (Overflowing a) where
  properFraction (Overflowing x _) =
    let (n, f) = properFraction x
     in (n, Overflowing f False)
