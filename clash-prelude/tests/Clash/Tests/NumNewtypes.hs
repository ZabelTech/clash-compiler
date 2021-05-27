{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.KnownNat.Solver #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Clash.Tests.NumNewtypes (tests) where

import Control.Exception (ArithException(DivideByZero), evaluate, try)
import Control.Monad.IO.Class (liftIO)
import Data.Fixed (mod')
import Data.Kind (Type)
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

-- TODO Compare the other way in tests, i.e. calculate the exact result as
-- an Integer or Rational THEN convert that to the target type using
-- fromInteger / fromRational. WAIT... This may not work with Index...

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
    , testProperty "Quotient" $ checkIntegral2 mode gen quot
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
    , testProperty "Reciprocal" $ checkRealFrac mode gen recip
    , testProperty "Division" $ checkRealFrac2 mode gen (/)
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

boundsIntegral :: (Integral a) => Integer -> a -> a -> Maybe BoundsCheck
boundsIntegral x minB maxB
  | toInteger maxB < x = Just Overflow
  | x < toInteger minB = Just Underflow
  | otherwise = Nothing

boundsRealFrac :: (RealFrac a) => Rational -> a -> a -> Maybe BoundsCheck
boundsRealFrac x minB maxB
  | toRational maxB < x = Just Overflow
  | x < toRational minB = Just Underflow
  | otherwise = Nothing

tryArithmetic
  :: (Maybe a -> PropertyT IO ())
  -> a
  -> PropertyT IO ()
tryArithmetic check x = do
  exRes <- liftIO $! try @ArithException (evaluate x)

  case exRes of
    Left DivideByZero ->
      check Nothing

    Left ex ->
      footnote ("exception was " <> show ex) *> failure

    Right res ->
      check (Just res)

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
    let integerRes = op (toInteger x)
    let boundsCheck = boundsIntegral integerRes (minBound @(f a)) (maxBound @(f a))

    case boundsCheck of
      Nothing -> do
        label "InBounds"

        -- Check that no overflow flag was set if the type has it.
        case mode of
          Over ->
            let res = op x
             in (integerRes === toInteger res) *> assert (not (hasOverflowed res))

          _ -> integerRes === toInteger (op x)

      Just bounds -> do
        collect bounds
        checkResult bounds integerRes x
 where
  checkResult :: BoundsCheck -> Integer -> f a -> PropertyT IO ()
  checkResult bounds integer x =
    case mode of
      Error ->
        throwsException (op x)

      Over ->
        let minB = toInteger (minBound @(f a))
            maxB = toInteger (maxBound @(f a)) + 1
            wrap = minB + (integer - minB) `mod` (maxB - minB)
            res  = op x
         in (wrap === toInteger res) *> assert (hasOverflowed res)

      Sat | Overflow <- bounds ->
        maxBound === (op x)

      Sat | Underflow <- bounds ->
        minBound === (op x)

      Wrap ->
        let minB = toInteger (minBound @(f a))
            maxB = toInteger (maxBound @(f a)) + 1
            wrap = minB + (integer - minB) `mod` (maxB - minB)
         in wrap === toInteger (op x)

      Zero ->
        0 === (op x)

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
    let rationalRes = op (toRational x)
    let boundsCheck = boundsRealFrac rationalRes (minBound @(f a)) (maxBound @(f a))

    case boundsCheck of
      Nothing -> do
        label "InBounds"
        rationalRes === toRational (op x)

      Just bounds -> do
        collect bounds
        checkResult bounds rationalRes x
 where
  checkResult :: BoundsCheck -> Rational -> f a -> PropertyT IO ()
  checkResult bounds rational x =
    case mode of
      Error ->
        throwsException (op x)

      Over ->
        let minB = toRational (minBound @(f a))
            maxB = toRational (maxBound @(f a)) + 1
            wrap = minB + (rational - minB) `mod'` (maxB - minB)
            res  = op x
         in (wrap === toRational res) *> assert (hasOverflowed res)

      Sat | Overflow <- bounds ->
        maxBound === (op x)

      Sat | Underflow <- bounds ->
        minBound === (op x)

      Wrap ->
        let minB = toRational (minBound @(f a))
            maxB = toRational (maxBound @(f a)) + 1
            wrap = minB + (rational - minB) `mod'` (maxB - minB)
         in wrap === toRational (op x)

      Zero ->
        0.0 === (op x)

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

    let integerRes = toInteger x `op` toInteger y
    let boundsCheck = boundsIntegral integerRes (minBound @(f a)) (maxBound @(f a))

    case boundsCheck of
      Nothing -> do
        label "InBounds"

        case mode of
          Over ->
            let res = x `op` y
             in (integerRes === toInteger res) *> assert (not (hasOverflowed res))

          _ -> integerRes === toInteger (x `op` y)

      Just bounds -> do
        collect bounds
        checkResult bounds integerRes x y
 where
  checkResult :: BoundsCheck -> Integer -> f a -> f a -> PropertyT IO ()
  checkResult bounds integer x y =
    case mode of
      Error ->
        throwsException (x `op` y)

      Over ->
        let minB = toInteger (minBound @(f a))
            maxB = toInteger (maxBound @(f a)) + 1
            wrap = minB + (integer - minB) `mod` (maxB - minB)
            res  = x `op` y
         in (wrap === toInteger res) *> assert (hasOverflowed res)

      Sat | Overflow <- bounds ->
        maxBound === (x `op` y)

      Sat | Underflow <- bounds ->
        minBound === (x `op` y)

      Wrap ->
        let minB = toInteger (minBound @(f a))
            maxB = toInteger (maxBound @(f a)) + 1
            wrap = minB + (integer - minB) `mod` (maxB - minB)
         in wrap === toInteger (x `op` y)

      Zero ->
        0 === (x `op` y)

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

    let rationalRes = toRational x `op` toRational y
    let boundsCheck = boundsRealFrac rationalRes (minBound @(f a)) (maxBound @(f a))

    case boundsCheck of
      Nothing -> do
        label "InBounds"
        rationalRes === toRational (x `op` y)

      Just bounds -> do
        collect bounds
        checkResult bounds rationalRes x y
 where
  checkResult :: BoundsCheck -> Rational -> f a -> f a -> PropertyT IO ()
  checkResult bounds rational x y =
    case mode of
      Error ->
        throwsException (x `op` y)

      Over ->
        let minB = toRational (minBound @(f a))
            maxB = toRational (maxBound @(f a)) + 1
            wrap = minB + (rational - minB) `mod'` (maxB - minB)
            res  = x `op` y
         in (wrap === toRational res) *> assert (not (hasOverflowed res))

      Sat | Overflow <- bounds ->
        maxBound === (x `op` y)

      Sat | Underflow <- bounds ->
        minBound === (x `op` y)

      Wrap ->
        let minB = toRational (minBound @(f a))
            maxB = toRational (maxBound @(f a)) + 1
            wrap = minB + (rational - minB) `mod'` (maxB - minB)
         in wrap === toRational (x `op` y)

      Zero ->
        0.0 === (x `op` y)

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
