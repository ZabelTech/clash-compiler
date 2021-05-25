{-
Copyright   : (C) 2021, QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Clash.Num.Zeroing
  ( Zeroing(fromZeroing)
  , toZeroing
  ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Bits (Bits, FiniteBits)
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
import Data.Hashable (Hashable)
import GHC.TypeLits (KnownNat, type (+))

import Clash.Class.BitPack (BitPack)
import Clash.Class.Num (SaturationMode(SatZero), SaturatingNum(..))
import Clash.Class.Parity (Parity)
import Clash.Class.Resize (Resize(..))
import Clash.XException (NFDataX, ShowX)

newtype Zeroing a =
  Zeroing { fromZeroing :: a }
  deriving newtype
    ( Binary
    , Bits
    , BitPack
    , Bounded
    , Eq
    , FiniteBits
    , Hashable
    , NFData
    , NFDataX
    , Ord
    , Parity
    , Show
    , ShowX
    )

toZeroing :: (SaturatingNum a) => a -> Zeroing a
toZeroing = Zeroing

instance (Resize f) => Resize (Compose Zeroing f) where
  resize
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Zeroing f a
    -> Compose Zeroing f b
  resize = coerce (resize @f @a @b)

  zeroExtend
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Zeroing f a
    -> Compose Zeroing f (b + a)
  zeroExtend = coerce (zeroExtend @f @a @b)

  truncateB
    :: forall a b
     . (KnownNat a)
    => Compose Zeroing f (a + b)
    -> Compose Zeroing f a
  truncateB = coerce (truncateB @f @a @b)

instance (Bounded a, Ord a, SaturatingNum a) => Num (Zeroing a) where
  (+) = coerce (satAdd @a SatZero)
  (-) = coerce (satSub @a SatZero)
  (*) = coerce (satMul @a SatZero)

  -- If the number is signed, negating may result in an overflow. This assumes
  -- a twos-complement representation, meaning negate minBound overflows to 0.
  negate x
    | 0 <= minBound @a = 0
    | x == minBound = 0
    | otherwise = coerce (negate @a) x

  -- If the number is signed, the absolute may result in an overflow. This
  -- assumes a twos-complement representation, meaning abs minBound overflows
  -- to 0.
  abs x
    | x == minBound && x < 0 = 0
    | otherwise = coerce (abs @a) x

  signum = coerce (signum @a)
  fromInteger = coerce (fromInteger @a)

instance (Enum a, SaturatingNum a) => Enum (Zeroing a) where
  -- Deliberately breaks the Enum law that succ maxBound ~> error
  succ = coerce (satSucc @a SatZero)

  -- Deliberately breaks the Enum law that pred minBound ~> error
  pred = coerce (satPred @a SatZero)

  toEnum = coerce (toEnum @a)
  fromEnum = coerce (fromEnum @a)

instance (Real a, SaturatingNum a) => Real (Zeroing a) where
  toRational = coerce (toRational @a)

instance (Integral a, SaturatingNum a) => Integral (Zeroing a) where
  -- minBound / -1 overflows to 0
  quotRem x y
    | x == minBound && y == -1 = (0, 0)
    | otherwise = coerce (quotRem @a) x y

  toInteger = coerce (toInteger @a)

instance (Fractional a, Ord a, SaturatingNum a) => Fractional (Zeroing a) where
  -- Overflow when dividing by 0
  recip x
    | x == 0 = x
    | otherwise = coerce (recip @a) x

  fromRational = coerce (fromRational @a)

instance (RealFrac a, SaturatingNum a) => RealFrac (Zeroing a) where
  properFraction :: forall b. (Integral b) => Zeroing a -> (b, Zeroing a)
  properFraction = coerce (properFraction @a @b)

