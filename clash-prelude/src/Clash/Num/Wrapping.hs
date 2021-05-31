{-
Copyright   : (C) 2021, QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Clash.Num.Wrapping
  ( Wrapping(fromWrapping)
  , toWrapping
  ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Data.Bits (Bits, FiniteBits)
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
import Data.Hashable (Hashable)
import GHC.TypeLits (KnownNat, type (+))

import Clash.Class.BitPack (BitPack)
import Clash.Class.Num (SaturationMode(SatWrap), SaturatingNum(..))
import Clash.Class.Parity (Parity)
import Clash.Class.Resize (Resize(..))
import Clash.XException (NFDataX, ShowX)

newtype Wrapping a =
  Wrapping { fromWrapping :: a }
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

toWrapping :: (SaturatingNum a) => a -> Wrapping a
toWrapping = Wrapping

-- See note in Clash.Num.Saturating
instance (Resize f) => Resize (Compose Wrapping f) where
  resize
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Wrapping f a
    -> Compose Wrapping f b
  resize = coerce (resize @f @a @b)

  zeroExtend
    :: forall a b
     . (KnownNat a, KnownNat b)
    => Compose Wrapping f a
    -> Compose Wrapping f (b + a)
  zeroExtend = coerce (zeroExtend @f @a @b)

  truncateB
    :: forall a b
     . (KnownNat a)
    => Compose Wrapping f (a + b)
    -> Compose Wrapping f a
  truncateB = coerce (truncateB @f @a @b)

instance (SaturatingNum a) => Num (Wrapping a) where
  (+) = coerce (satAdd @a SatWrap)
  (-) = coerce (satSub @a SatWrap)
  (*) = coerce (satMul @a SatWrap)

  -- Assume the default behaviour is to wrap anyway.
  -- TODO This breaks with Index, because it has a bad instance for negate.
  negate = coerce (negate @a)
  abs = coerce (abs @a)
  signum = coerce (signum @a)
  fromInteger = coerce (fromInteger @a)

instance (Enum a, SaturatingNum a) => Enum (Wrapping a) where
  -- Deliberately breaks the Enum law that succ maxBound ~> error
  succ = coerce (satSucc @a SatWrap)

  -- Deliberately breaks the Enum law that pred minBound ~> error
  pred = coerce (satPred @a SatWrap)

  toEnum = coerce (toEnum @a)
  fromEnum = coerce (fromEnum @a)

instance (Real a, SaturatingNum a) => Real (Wrapping a) where
  -- Assume the default behaviour is to wrap anyway.
  toRational = coerce (toRational @a)

instance (Integral a, SaturatingNum a) => Integral (Wrapping a) where
  -- Assume the default behaviour is to wrap anyway.
  quotRem = coerce (quotRem @a)
  toInteger = coerce (toInteger @a)

instance (Fractional a, SaturatingNum a) => Fractional (Wrapping a) where
  -- Assume the default behaviour is to wrap anyway.
  recip = coerce (recip @a)

  -- TODO Fixed saturates in fromRational, so we can't assume wrapping here
  fromRational = coerce (fromRational @a)

instance (RealFrac a, SaturatingNum a) => RealFrac (Wrapping a) where
  -- Assume the default behaviour is to wrap anyway.
  properFraction :: forall b. (Integral b) => Wrapping a -> (b, Wrapping a)
  properFraction = coerce (properFraction @a @b)
