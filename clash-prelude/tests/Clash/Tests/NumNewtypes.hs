{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.KnownNat.Solver #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Clash.Tests.NumNewtypes (tests) where

import Control.Exception (ArithException, evaluate, try)
import Control.Monad.IO.Class (liftIO)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import GHC.TypeLits (KnownNat)
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Hedgehog.Extra
import Test.Tasty
import Test.Tasty.Hedgehog

import Clash.Class.Num
import Clash.Num.Erroring
import Clash.Num.Overflowing
import Clash.Num.Saturating
import Clash.Num.Wrapping
import Clash.Num.Zeroing
import Clash.Sized.Fixed (SFixed)
import Clash.Sized.Index (Index)
import Clash.Sized.Signed (Signed)

tests :: TestTree
tests = testGroup "Numeric Newtypes"
  [ testGroup "Erroring"
      [ testIntegral "Index 4" Error (genErroring (genIndex @4))
      , testIntegral "Signed 4" Error (genErroring (genSigned @4))
      , testRealFrac "SFixed 2 2" Error (genErroring (genSFixed @2 @2))
      ]
  , testGroup "Overflowing"
      [ testIntegral "Index 4" Over (genOverflowing (genIndex @4))
      , testIntegral "Signed 4" Over (genOverflowing (genSigned @4))
      , testRealFrac "SFixed 2 2" Over (genOverflowing (genSFixed @2 @2))
      ]
  , testGroup "Saturating"
      [ testIntegral "Index 4" Sat (genSaturating (genIndex @4))
      , testIntegral "Signed 4" Sat (genSaturating (genSigned @4))
      , testRealFrac "SFixed 2 2" Sat (genSaturating (genSFixed @2 @2))
      ]
  , testGroup "Wrapping"
      [ testIntegral "Index 4" Wrap (genWrapping (genIndex @4))
      , testIntegral "Signed 4" Wrap (genWrapping (genSigned @4))
      , testRealFrac "SFixed 2 2" Wrap (genWrapping (genSFixed @2 @2))
      ]
  , testGroup "Zeroing"
      [ testIntegral "Index 4" Zero (genZeroing (genIndex @4))
      , testIntegral "Signed 4" Zero (genZeroing (genSigned @4))
      , testRealFrac "SFixed 2 2" Zero (genZeroing (genSFixed @2 @2))
      ]
  ]

testIntegral
  :: (Bounded (f a), Integral (f a), Show (f a))
  => TestName
  -> Mode f
  -> Gen (f a)
  -> TestTree
testIntegral name mode gen =
  testGroup name
    [ testProperty "Addition" $ checkIntegral2 mode gen (+)
    , testProperty "Subtraction" $ checkIntegral2 mode gen (-)
    , testProperty "Multiplication" $ checkIntegral2 mode gen (*)
    , testProperty "Negation" $ checkIntegral mode gen negate
    , testProperty "Absolute" $ checkIntegral mode gen abs
    , testProperty "Successor" $ checkIntegral mode gen succ
    , testProperty "Predecessor" $ checkIntegral mode gen pred
--  , testProperty "Quotient" $ checkIntegral2 mode gen quot
    , testProperty "Remainder" $ checkIntegral2 mode gen rem
    ]

testRealFrac
  :: (Bounded (f a), Enum (f a), RealFrac (f a), Show (f a))
  => TestName
  -> Mode f
  -> Gen (f a)
  -> TestTree
testRealFrac name mode gen =
  testGroup name
    [ testProperty "Addition" $ checkRealFrac2 mode gen (+)
    , testProperty "Subtraction" $ checkRealFrac2 mode gen (-)
    , testProperty "Multiplication" $ checkRealFrac2 mode gen (*)
    , testProperty "Negation" $ checkRealFrac mode gen negate
    , testProperty "Absolute" $ checkRealFrac mode gen abs
    , testProperty "Successor" $ checkRealFrac mode gen succ
    , testProperty "Predecessor" $ checkRealFrac mode gen pred
--  , testProperty "Reciprocal" $ checkRealFrac mode gen recip
--  , testProperty "Division" $ checkRealFrac2 mode gen (/)
    ]

data Mode :: (Type -> Type) -> Type where
  Error :: Mode Erroring
  Over  :: Mode Overflowing
  Sat   :: Mode Saturating
  Wrap  :: Mode Wrapping
  Zero  :: Mode Zeroing

data BoundsCheck
  = Overflow | Underflow
  deriving (Show)

boundsIntegral
  :: forall a
   . (Bounded a, Integral a)
  => Proxy a
  -> Maybe Integer
  -> Maybe BoundsCheck
boundsIntegral Proxy (Just x)
  | toInteger (maxBound @a) < x = Just Overflow
  | x < toInteger (minBound @a) = Just Underflow
  | otherwise = Nothing

boundsIntegral Proxy Nothing = Just Overflow

boundsRealFrac
  :: forall a
   . (Bounded a, RealFrac a)
  => Proxy a
  -> Maybe Rational
  -> Maybe BoundsCheck
boundsRealFrac Proxy (Just x)
  | toRational (maxBound @a) < x = Just Overflow
  | x < toRational (minBound @a) = Just Underflow
  | otherwise = Nothing

boundsRealFrac Proxy Nothing = Just Overflow

-- Catch SomeException as we either want to catch ArithException or XException.
tryArithmetic :: (a -> a) -> a -> PropertyT IO (Maybe a)
tryArithmetic f x =
  either (const Nothing) Just
    <$> liftIO (try @ArithException (evaluate $ f x))

-- fromInteger wraps for most types, but not Index. So we need this to get the
-- wrapping behaviour we expect.
wrapIntegral
  :: forall a
   . (Bounded a, Integral a)
  => Integer
  -> a
wrapIntegral x =
  let minB = toInteger (minBound @a)
      maxB = toInteger (maxBound @a) + 1
   in fromInteger $! minB + (x - minB) `mod` (maxB - minB)

checkIntegral
  :: forall f a
   . (Bounded (f a), Enum (f a), Integral (f a), Show (f a))
  => Mode f
  -> Gen (f a)
  -> (forall b. Integral b => b -> b)
  -> Property
checkIntegral mode gen op =
  property $ do
    x <- forAll gen
    result <- tryArithmetic op (toInteger x)

    case boundsIntegral (Proxy @(f a)) result of
      Nothing -> do
        label "InBounds"
        goInBounds result x

      Just info -> do
        collect info
        goOutBounds info result x
 where
  goInBounds mInteger x =
    case mode of
      Over -> do
        let result = op x
        assert (not (hasOverflowed result))
        fmap fromInteger mInteger === Just result

      _ ->
        fmap fromInteger mInteger === Just (op x)

  goOutBounds info mInteger x =
    case mode of
      Error ->
        throwsException (op x)

      Over -> do
        case mInteger of
          Nothing -> throwsException (op x)
          Just i -> do
            let result = op x
            assert (hasOverflowed result)
            wrapIntegral i === result

      Sat ->
        case info of
          Overflow -> maxBound === op x
          Underflow -> minBound === op x

      Wrap ->
        case mInteger of
          Nothing -> throwsException (op x)
          Just i -> wrapIntegral i === op x

      Zero ->
        0 === op x

checkRealFrac
  :: forall f a
   . (Bounded (f a), Enum (f a), RealFrac (f a), Show (f a))
  => Mode f
  -> Gen (f a)
  -> (forall b. (Enum b, RealFrac b) => b -> b)
  -> Property
checkRealFrac mode gen op =
  property $ do
    x <- forAll gen
    result <- tryArithmetic op (toRational x)

    case boundsRealFrac (Proxy @(f a)) result of
      Nothing -> do
        label "InBounds"
        goInBounds result x

      Just info -> do
        collect info
        goOutBounds info result x
 where
  goInBounds mRational x =
    case mode of
      Over -> do
        let result = op x
        assert (not (hasOverflowed x))
        fmap fromRational mRational === Just result

      _ ->
        fmap fromRational mRational === Just (op x)

  goOutBounds info mRational x =
    case mode of
      Error ->
        throwsException (op x)

      Over ->
        case mRational of
          Nothing -> throwsException (op x)
          Just r -> do
            let result = op x
            assert (hasOverflowed result)
            fromRational r === result

      Sat ->
        case info of
          Overflow -> maxBound === op x
          Underflow -> minBound === op x

      Wrap ->
        case mRational of
          Nothing -> throwsException (op x)
          Just r -> fromRational r === op x

      Zero ->
        0.0 === op x

checkIntegral2
  :: forall f a
   . (Bounded (f a), Integral (f a), Show (f a))
  => Mode f
  -> Gen (f a)
  -> (forall b. Integral b => b -> b -> b)
  -> Property
checkIntegral2 mode gen op =
  property $ do
    x <- forAll gen
    y <- forAll gen
    result <- tryArithmetic (toInteger x `op`) (toInteger y)

    case boundsIntegral (Proxy @(f a)) result of
      Nothing -> do
        label "InBounds"
        goInBounds result x y

      Just info -> do
        collect info
        goOutBounds info result x y
 where
  goInBounds mInteger x y =
    case mode of
      Over -> do
        let result = op x y
        assert (not (hasOverflowed result))
        fmap fromInteger mInteger === Just result

      _ ->
        fmap fromInteger mInteger === Just (x `op` y)

  goOutBounds info mInteger x y =
    case mode of
      Error ->
        throwsException (op x y)

      Over ->
        case mInteger of
          Nothing -> throwsException (op x y)
          Just i -> do
            let result = op x y
            assert (hasOverflowed result)
            wrapIntegral i === result

      Sat ->
        case info of
          Overflow -> maxBound === op x y
          Underflow -> minBound === op x y

      Wrap ->
        case mInteger of
          Nothing -> throwsException (op x y)
          Just i -> wrapIntegral i === op x y

      Zero ->
        0 === op x y

checkRealFrac2
  :: forall f a
   . (Bounded (f a), RealFrac (f a), Show (f a))
  => Mode f
  -> Gen (f a)
  -> (forall b. RealFrac b => b -> b -> b)
  -> Property
checkRealFrac2 mode gen op =
  property $ do
    x <- forAll gen
    y <- forAll gen
    result <- tryArithmetic (toRational x `op`) (toRational y)

    case boundsRealFrac (Proxy @(f a)) result of
      Nothing -> do
        label "InBounds"
        goInBounds result x y

      Just info -> do
        collect info
        goOutBounds info result x y
 where
  goInBounds mRational x y =
    case mode of
      Over -> do
        let result = op x y
        assert (not (hasOverflowed result))
        fmap fromRational mRational === Just result

      _ ->
        fmap fromRational mRational === Just (op x y)

  goOutBounds info mRational x y =
    case mode of
      Error ->
        throwsException (op x y)

      Over ->
        case mRational of
          Nothing -> throwsException (op x y)
          Just r -> do
            let result = op x y
            assert (hasOverflowed result)
            fromRational r === result

      Sat ->
        case info of
          Overflow -> maxBound === op x y
          Underflow -> minBound === op x y

      Wrap ->
        case mRational of
          Nothing -> throwsException (op x y)
          Just r -> fromRational r === op x y

      Zero ->
        0.0 === op x y

genErroring :: forall a. (SaturatingNum a) => Gen a -> Gen (Erroring a)
genErroring = fmap toErroring

genOverflowing :: forall a. (SaturatingNum a) => Gen a -> Gen (Overflowing a)
genOverflowing = fmap toOverflowing

genSaturating :: forall a. (SaturatingNum a) => Gen a -> Gen (Saturating a)
genSaturating = fmap toSaturating

genWrapping :: forall a. (SaturatingNum a) => Gen a -> Gen (Wrapping a)
genWrapping = fmap toWrapping

genZeroing :: forall a. (SaturatingNum a) => Gen a -> Gen (Zeroing a)
genZeroing = fmap toZeroing

genBoundedIntegral :: forall a. (Bounded a, Integral a) => Gen a
genBoundedIntegral = Gen.frequency
  [ (10, pure minBound)
  , (10, pure 0)
  , (40, Gen.integral (Range.linear minBound maxBound))
  , (40, pure maxBound)
  ]

genIndex :: forall n. (KnownNat n) => Gen (Index n)
genIndex = genBoundedIntegral

genSigned :: forall n. (KnownNat n) => Gen (Signed n)
genSigned = genBoundedIntegral

genBoundedRealFrac :: forall a. (Bounded a, RealFrac a) => Gen a
genBoundedRealFrac = Gen.frequency
  [ (10, pure minBound)
  , (10, pure 0.0)
  , (40, fmap realToFrac
           . Gen.double
           . fmap realToFrac
           $ Range.linearFrac (minBound @a) (maxBound @a))
  , (40, pure maxBound)
  ]

genSFixed :: forall n m. (KnownNat n, KnownNat m) => Gen (SFixed n m)
genSFixed = genBoundedRealFrac
