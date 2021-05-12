{-
Copyright   : (C) 2021, QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Clash.Num.Saturating
  ( Saturating(fromSaturating)
  , toSaturating
  ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Bits (Bits, FiniteBits)
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
import Data.Hashable (Hashable)
import GHC.TypeLits (KnownNat, type (+))

import Clash.Class.BitPack (BitPack)
import Clash.Class.Num (SaturationMode(SatBound), SaturatingNum(..))
import Clash.Class.Parity (Parity)
import Clash.Class.Resize (Resize(..))
import Clash.XException (NFDataX, ShowX)

-- | A saturating number type is one where all operations saturate at the
-- bounds of the underlying type, i.e. operations which overflow return
-- 'maxBound' and operations that underflow return 'minBound'.
--
-- Numbers can be converted to saturate by default using 'toSaturating'.
--
newtype Saturating a =
  Saturating { fromSaturating :: a }
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

toSaturating :: (SaturatingNum a) => a -> Saturating a
toSaturating = Saturating

-- The explicit type signatures are needed here, otherwise the type parameters
-- are ambiguous in the use of coerce.
--
-- TODO: It's possible to write instances of the form
--
--   instance (forall m. X (Saturating (f m))) => X (Compose Saturating f n)
--
-- where each member function is just coerce. Terrible to read and write, but
-- it means you can have the normal `Num` and friends instances on types like
-- Compose Saturating Signed, which also gets you this Resize instance.
instance (Resize f) => Resize (Compose Saturating f) where
  resize
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Saturating f a
    -> Compose Saturating f b
  resize = coerce (resize @f @a @b)

  zeroExtend
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Saturating f a
    -> Compose Saturating f (b + a)
  zeroExtend = coerce (zeroExtend @f @a @b)

  truncateB
    :: forall a b
     . (KnownNat a)
    => Compose Saturating f (a + b)
    -> Compose Saturating f a
  truncateB = coerce (truncateB @f @a @b)

instance (Ord a, SaturatingNum a) => Num (Saturating a) where
  (+) = coerce (satAdd @a SatBound)
  (-) = coerce (satSub @a SatBound)
  (*) = coerce (satMul @a SatBound)

  -- If the number is signed, negating may result in an overflow. This assumes
  -- a twos-complement representation, meaning negate minBound overflows and
  -- saturates to maxBound.
  negate x
    | 0 <= minBound @a = 0
    | x == minBound = maxBound
    | otherwise = coerce (negate @a) x

  -- If the number is signed, the absolute may result in an overflow. This
  -- assumes a twos-complement representation, meaning abs minBound overflows
  -- and saturates to maxBound.
  abs x
    | x == minBound && x < 0 = maxBound
    | otherwise = coerce (abs @a) x

  signum = coerce (signum @a)
  fromInteger = coerce (fromInteger @a)

instance (Enum a, SaturatingNum a) => Enum (Saturating a) where
  -- Deliberately breaks the Enum law that succ maxBound ~> error
  succ = coerce (satSucc @a SatBound)

  -- Deliberately breaks the Enum law that pred minBound ~> error
  pred = coerce (satPred @a SatBound)

  toEnum = coerce (toEnum @a)
  fromEnum = coerce (fromEnum @a)

instance (Real a, SaturatingNum a) => Real (Saturating a) where
  toRational = coerce (toRational @a)

instance (Integral a, SaturatingNum a) => Integral (Saturating a) where
  quotRem x y
    -- Division by 0, quotient and remainder overflow and saturate
    | y == 0 = (maxBound, maxBound)
    -- minBound / -1 overflows and saturates
    | x == minBound && y == -1 = (maxBound, 0)
    | otherwise = coerce (quotRem @a) x y

  toInteger = coerce (toInteger @a)

instance (Fractional a, Ord a, SaturatingNum a) => Fractional (Saturating a) where
  recip x
    -- Division by 0, overflow and saturate
    | x == 0 = maxBound
    | otherwise = coerce (recip @a) x

  fromRational = coerce (fromRational @a)

instance (Ord a, RealFrac a, SaturatingNum a) => RealFrac (Saturating a) where
  properFraction :: forall b. (Integral b) => Saturating a -> (b, Saturating a)
  properFraction = coerce (properFraction @a @b)
