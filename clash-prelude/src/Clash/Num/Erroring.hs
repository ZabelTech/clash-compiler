{-
Copyright   : (C) 2021, QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Clash.Num.Erroring
  ( Erroring(fromErroring)
  , toErroring
  ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Bits (Bits, FiniteBits)
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
import Data.Hashable (Hashable)
import GHC.TypeLits (KnownNat, type (+))

import Clash.Class.BitPack (BitPack)
import Clash.Class.Num (SaturationMode(SatError), SaturatingNum(..))
import Clash.Class.Parity (Parity)
import Clash.Class.Resize (Resize(..))
import Clash.XException (NFDataX, ShowX, errorX)

-- | An erroring number type is one where all operations return an 'XException'
-- if they would go out of bounds for the underlying type.
--
-- Numbers can be converted to error by default using 'toErroring'.
--
newtype Erroring a =
  Erroring { fromErroring :: a }
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

toErroring :: (SaturatingNum a) => a -> Erroring a
toErroring = Erroring

instance (Resize f) => Resize (Compose Erroring f) where
  resize
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Erroring f a
    -> Compose Erroring f b
  resize = coerce (resize @f @a @b)

  zeroExtend
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Erroring f a
    -> Compose Erroring f (b + a)
  zeroExtend = coerce (zeroExtend @f @a @b)

  truncateB
    :: forall a b
     . (KnownNat a)
    => Compose Erroring f (a + b)
    -> Compose Erroring f a
  truncateB = coerce (truncateB @f @a @b)

instance (Bounded a, Ord a, SaturatingNum a) => Num (Erroring a) where
  (+) = coerce (satAdd @a SatError)
  (-) = coerce (satSub @a SatError)
  (*) = coerce (satMul @a SatError)

  negate x
    | 0 == x = x
    | 0 <= minBound @a = errorX "Erroring.negate: underflow"
    | x == minBound = errorX "Erroring.negate: overflow"
    | otherwise = coerce (negate @a) x

  abs x
    | x == minBound && x < 0 = errorX "Erroring.abs: overflow"
    | otherwise = coerce (abs @a) x

  signum = coerce (signum @a)
  fromInteger = coerce (fromInteger @a)

instance (Enum a, SaturatingNum a) => Enum (Erroring a) where
  succ = coerce (satSucc @a SatError)
  pred = coerce (satPred @a SatError)
  toEnum = coerce (toEnum @a)
  fromEnum = coerce (fromEnum @a)

instance (Real a, SaturatingNum a) => Real (Erroring a) where
  toRational = coerce (toRational @a)

instance (Integral a, SaturatingNum a) => Integral (Erroring a) where
  quotRem x y
    | x == minBound && y == -1 = errorX "Erroring.quotRem: overflow"
    | otherwise = coerce (quotRem @a) x y

  toInteger = coerce (toInteger @a)

instance (Fractional a, Ord a, SaturatingNum a) => Fractional (Erroring a) where
  recip x
    | x == 0 = errorX "Erroring.recip: overflow"
    | otherwise = coerce (recip @a) x

  fromRational = coerce (fromRational @a)

instance (RealFrac a, SaturatingNum a) => RealFrac (Erroring a) where
  properFraction :: forall b. (Integral b) => Erroring a -> (b, Erroring a)
  properFraction = coerce (properFraction @a @b)

