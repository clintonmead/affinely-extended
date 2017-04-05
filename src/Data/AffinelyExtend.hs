{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
This package has four ways to extend any numerical type to add infinities:

1) Both infinities with GADT: 'AffinelyExtendBoth', creation: 'affinelyExtendBoth'
2) Positive infinity only with GADT: 'AffinelyExtendPos', creation: 'affinelyExtendPos'
3) Both infinities with upper/lower bounds as infinity: 'AffinelyExtendBoundedBoth', creation: 'affinelyExtendBoundedBoth'
4) Positive infinities only with upper bound as infinity: 'AffinelyExtendBoundedPos', creation: 'affinelyExtendBoundedPos'

The function 'affinelyExtend' is a generic creation function that calls one of the above based on the derived type of the output.

A few notes. Firstly, option 3, the 'AffinelyExtendBoundedBoth' option, does not actually use 'maxBound' and 'minBound' as
positive and negative infinity respectively, it actually takes the smallest absolute value 'maxBound' and 'minBound' as
positive infinity and the negation of that as negative infinity.

This means, for example, on an 'Int8', +127 is positive infinity, but -127 is negative infinity, not -128. So the valid finite
range for the type becomes [-126..126].

Storable and unboxed instances for bounded types (i.e. 'AffinelyExtendBoundedBoth' and 'AffinelyExtendBoundedPos') should be
trivial to create.

This package refers to the first two types, namely 'AffinelyExtendBoth' and 'AffinelyExtendPos' as unpacked types. When they're used
directly, packing and unpacking is just 'id', but when the bounded types are used, they are unpacked into these types and packed back
into themselves.

For most operations, the bounded types simply unpack to the unbounded types, perform the unpacked operation, and then pack themselves.

But there's two optimisations to this process

1) For operations like 'negate', there is no need for special checking for infinities, so the unbounded types just apply negate directly
to their own representation.
2) There's rewrite rules that remove 'unpack . pack' sequences.

There's competing advantages to both formats. The bounded formats obviously take up less storage space, and can perform some operations
like 'negate' without a pattern match.

However, chains of operations on the  "packed" bounded types that do need to check for infinity will check everytime, because there's
no way for the compiler to disguish between and operation that has overflowed and "accidently" became infinity and actual infinity.

So the rewrite rules are intended to help chains of operations use the "unpacked" represenation, which hopefully should reduce the
infinity checks to the first operation in the sequence (as after that the compiler should be able to statically prove at compile time
that the latter operations are/are not infinities.

This package is currently without a test suite and needs more documentation, so if you find any bugs, please report them. 
-}
module Data.AffinelyExtend (
  AffinelyExtend(NegativeInfinity, Finite, PositiveInfinity), affinelyExtend,
  AffinelyExtendBoth, affinelyExtendBoth,
  AffinelyExtendPos, affinelyExtendPos,
  AffinelyExtendBoundedBoth, affinelyExtendBoundedBoth,
  AffinelyExtendBoundedPos, affinelyExtendBoundedPos,
  CanAffinelyExtend, isPos, isNegInf, isInf, isFinite, BaseType, UnpackType, affinelyExtend_c, unpack_c, unpackBoth_c,
  CanAffinelyExtendPos, unpackPos_c,
  HasPositiveInfinity, posInf,
  HasBothInfinities, negInf
) where

import Control.Exception.Base (assert)
import GHC.Exts (Constraint)
import Data.Maybe (maybeToList)
import Control.Applicative ((<|>))

data AffinelyExtend (hasNegativeInfinity :: Bool) a where
  NegativeInfinity :: AffinelyExtend True a
  Finite :: a -> AffinelyExtend h a
  PositiveInfinity :: AffinelyExtend h a

type AffinelyExtendBoth a = AffinelyExtend True a
type AffinelyExtendPos a = AffinelyExtend False a

newtype AffinelyExtendBoundedBoth a = AffinelyExtendBoundedBoth { getAffinelyExtendBounded :: a }
newtype AffinelyExtendBoundedPos a = AffinelyExtendBoundedPos { getAffinelyExtendBoundedPos :: a }

class HasPositiveInfinity a where
  posInf :: a

class HasPositiveInfinity a => HasBothInfinities a where
  negInf :: a

unwrappedPosInf :: (Bounded a, Ord a, Num a) => a
unwrappedPosInf = min maxBound (negate minBound)

unwrappedNegInf :: (Bounded a, Ord a, Num a) => a
unwrappedNegInf = negate unwrappedPosInf

unwrappedPosInfPos :: (Bounded a) => a
unwrappedPosInfPos = maxBound

instance HasPositiveInfinity (AffinelyExtendBoth a) where
  posInf = PositiveInfinity

instance HasBothInfinities (AffinelyExtendBoth a) where
  negInf = NegativeInfinity

instance HasPositiveInfinity (AffinelyExtendPos a) where
  posInf = PositiveInfinity

instance (Bounded a, Ord a, Num a) => HasPositiveInfinity (AffinelyExtendBoundedBoth a) where
  posInf = AffinelyExtendBoundedBoth unwrappedPosInf

instance (Bounded a, Ord a, Num a) => HasBothInfinities (AffinelyExtendBoundedBoth a) where
  negInf = AffinelyExtendBoundedBoth unwrappedNegInf

instance (Eq a, Bounded a) => HasPositiveInfinity (AffinelyExtendBoundedPos a) where
  posInf = AffinelyExtendBoundedPos unwrappedPosInfPos

instance HasPositiveInfinity Float where
  posInf = 1 / 0

instance HasBothInfinities Float where
  negInf = (-1) / 0

instance HasPositiveInfinity Double where
  posInf = 1 / 0

instance HasBothInfinities Double where
  negInf = (-1) / 0

unpackSameBaseType :: (Eq a, HasBothInfinities a, BaseType a ~ a) => a -> AffinelyExtendBoth (BaseType a)
unpackSameBaseType x = if
  | x == posInf -> PositiveInfinity
  | x == negInf -> NegativeInfinity
  | otherwise -> Finite x

class CanAffinelyExtend a where
  type BaseType a
  affinelyExtend_c :: BaseType a -> a

  type UnpackType a
  type UnpackType a = AffinelyExtendBoth (BaseType a)

  unpack_c :: a -> UnpackType a
  default unpack_c :: (UnpackType a ~ AffinelyExtendBoth (BaseType a)) => a -> UnpackType a
  unpack_c = unpackBoth_c

  unpackBoth_c :: a -> AffinelyExtendBoth (BaseType a)
  default unpackBoth_c :: (Eq a, HasBothInfinities a, BaseType a ~ a) => a -> AffinelyExtendBoth (BaseType a)
  unpackBoth_c = unpackSameBaseType

  isPos :: a -> Bool
  isPos x = case (unpackBoth x) of
    PositiveInfinity -> True
    _ -> False

  isNegInf :: a -> Bool
  isNegInf x = case (unpackBoth x) of
     NegativeInfinity -> True
     _ -> False

  isInf :: a -> Bool
  isInf x = isPos x || isNegInf x

  isFinite :: a -> Bool
  isFinite = not . isInf

instance CanAffinelyExtend (AffinelyExtendBoth a) where
  type BaseType (AffinelyExtendBoth a) = a
  affinelyExtend_c = Finite
  unpackBoth_c = id

instance CanAffinelyExtend (AffinelyExtendPos a) where
  type BaseType (AffinelyExtendPos a) = a
  type UnpackType (AffinelyExtendPos a) = AffinelyExtendPos a

  unpack_c = unpackPos_c

  affinelyExtend_c = Finite
  unpackBoth_c = \case
    Finite x -> Finite x
    PositiveInfinity -> PositiveInfinity

  isPos = \case
    PositiveInfinity -> True
    _ -> False
  isNegInf _ = False
  isInf = isPos
  isFinite = not . isInf


{-# INLINE [1] isPosBounded #-}
isPosBounded :: (Ord a, Num a, Bounded a) => AffinelyExtendBoundedBoth a -> Bool
isPosBounded = applyToBounded (== unwrappedPosInf)

{-# INLINE [1] isNegInfBounded #-}
isNegInfBounded :: (Ord a, Num a, Bounded a) => AffinelyExtendBoundedBoth a -> Bool
isNegInfBounded = applyToBounded (== unwrappedNegInf)

{-# INLINE [1] isInfBounded #-}
isInfBounded :: (Ord a, Num a, Bounded a) => AffinelyExtendBoundedBoth a -> Bool
isInfBounded = applyToBounded (\x -> abs x == unwrappedPosInf)

{-# INLINE [1] isFiniteBounded #-}
isFiniteBounded :: (Ord a, Num a, Bounded a) => AffinelyExtendBoundedBoth a -> Bool
isFiniteBounded = applyToBounded (\x -> abs x /= unwrappedPosInf)

{-# RULES
"isPosBounded/pack" forall x. isPosBounded (packBoth x) = isPos x
"isNegInfBounded/pack" forall x. isNegInfBounded (packBoth x) = isNegInf x
"isInfBounded/pack" forall x. isInfBounded (packBoth x) = isInf x
"isFiniteBounded/pack" forall x. isFiniteBounded (packBoth x) = isFinite x
#-}

instance (Ord a, Bounded a, Num a) => CanAffinelyExtend (AffinelyExtendBoundedBoth a) where
  type BaseType (AffinelyExtendBoundedBoth a) = a
  affinelyExtend_c = AffinelyExtendBoundedBoth
  unpackBoth_c (AffinelyExtendBoundedBoth x) = if
    | x == unwrappedPosInf -> PositiveInfinity
    | x == unwrappedNegInf -> NegativeInfinity
    | otherwise -> Finite x

  isPos = isPosBounded
  isNegInf = isNegInfBounded

  isInf = isInfBounded
  isFinite = isFiniteBounded

{-# INLINE [1] isPosInfBoundedPos #-}
isPosInfBoundedPos :: (Eq a, Bounded a) => AffinelyExtendBoundedPos a -> Bool
isPosInfBoundedPos = applyToBounded (== unwrappedPosInfPos)

{-# INLINE [1] isFiniteBoundedPos #-}
isFiniteBoundedPos :: (Eq a, Bounded a) => AffinelyExtendBoundedPos a -> Bool
isFiniteBoundedPos = applyToBounded (/= unwrappedPosInfPos)

{-# RULES
"isPosInfBoundedPos/pack" forall x. isPosInfBoundedPos (packPos x) = isPos x
"isFiniteBoundedPos/pack" forall x. isFiniteBoundedPos (packPos x) = isFinite x
#-}

instance (Eq a, Bounded a) => CanAffinelyExtend (AffinelyExtendBoundedPos a) where
  type BaseType (AffinelyExtendBoundedPos a) = a
  type UnpackType (AffinelyExtendBoundedPos a) = AffinelyExtendPos a

  unpack_c = unpackPos_c

  affinelyExtend_c = AffinelyExtendBoundedPos
  unpackBoth_c (AffinelyExtendBoundedPos x) = if
    | x == unwrappedPosInfPos -> PositiveInfinity
    | otherwise -> Finite x

  isPos = isPosInfBoundedPos

  isNegInf _ = False

  isInf = isPos
  isFinite = isFiniteBoundedPos

instance CanAffinelyExtendPos (AffinelyExtendPos a) where
  unpackPos_c = id

instance (Eq a, Bounded a) => CanAffinelyExtendPos (AffinelyExtendBoundedPos a) where
  unpackPos_c (AffinelyExtendBoundedPos x) = if
    | x == unwrappedPosInfPos -> PositiveInfinity
    | otherwise -> Finite x

instance CanAffinelyExtend Float where
  type BaseType Float = Float
  affinelyExtend_c = id
  unpackBoth_c = unpackSameBaseType

instance CanAffinelyExtend Double where
  type BaseType Double = Double
  affinelyExtend_c = id
  unpackBoth_c = unpackSameBaseType

-- Packing

{-# INLINE [1] affinelyExtend #-}
affinelyExtend :: CanAffinelyExtend a => BaseType a -> a
affinelyExtend = affinelyExtend_c

affinelyExtendBoth :: a -> AffinelyExtendBoth a
affinelyExtendBoth = affinelyExtend

affinelyExtendPos :: a -> AffinelyExtendPos a
affinelyExtendPos = affinelyExtend

affinelyExtendBoundedBoth :: (Ord a, Bounded a, Num a) => a -> AffinelyExtendBoundedBoth a
affinelyExtendBoundedBoth = affinelyExtend

affinelyExtendBoundedPos :: (Eq a, Bounded a) => a -> AffinelyExtendBoundedPos a
affinelyExtendBoundedPos = affinelyExtend

{-# INLINE unpack #-}
unpack :: CanAffinelyExtend a => a -> UnpackType a
unpack = unpack_c

{-# INLINE [1] unpackBoth #-}
unpackBoth :: CanAffinelyExtend a => a -> AffinelyExtendBoth (BaseType a)
unpackBoth = unpackBoth_c

class (CanAffinelyExtend a) => CanAffinelyExtendPos a where
  unpackPos_c :: a -> AffinelyExtendPos (BaseType a)

{-# INLINE [1] unpackPos #-}
unpackPos :: (CanAffinelyExtendPos a) => a -> AffinelyExtendPos (BaseType a)
unpackPos = unpackPos_c

{-# INLINE [1] packBoth #-}
packBoth :: (HasBothInfinities a, CanAffinelyExtend a) => AffinelyExtendBoth (BaseType a) -> a
packBoth = \case
  Finite x -> affinelyExtend x
  PositiveInfinity -> posInf
  NegativeInfinity -> negInf

{-# INLINE [1] packPos #-}
packPos :: (HasPositiveInfinity a, CanAffinelyExtend a) => AffinelyExtendPos (BaseType a)-> a
packPos = \case
  Finite x -> affinelyExtend x
  PositiveInfinity -> posInf

class CanAffinelyPack t where
  type CanAffinelyPackConstraint t a :: Constraint
  pack_c :: (CanAffinelyPackConstraint t a) => t (BaseType a) -> a

instance CanAffinelyPack (AffinelyExtend True) where
  type CanAffinelyPackConstraint (AffinelyExtend True) a = (HasBothInfinities a, CanAffinelyExtend a)
  pack_c = packBoth

instance CanAffinelyPack (AffinelyExtend False) where
  type CanAffinelyPackConstraint (AffinelyExtend False) a = (HasPositiveInfinity a, CanAffinelyExtend a)
  pack_c = packPos


{-# INLINE pack #-}
pack :: (CanAffinelyPack t, CanAffinelyPackConstraint t a) => t (BaseType a) -> a
pack = pack_c


{-# RULES
"unpackBoth/packBoth" forall x. unpackBoth (packBoth x) = x
"unpackPos/packPos" forall x. unpackPos (packPos x) = x
#-}

class GetRawVal a where
  getRawVal :: a -> BaseType a
  setRawVal :: BaseType a -> a

instance GetRawVal (AffinelyExtendBoundedBoth a) where
  getRawVal (AffinelyExtendBoundedBoth x) = x
  setRawVal = AffinelyExtendBoundedBoth

instance GetRawVal (AffinelyExtendBoundedPos a) where
  getRawVal (AffinelyExtendBoundedPos x) = x
  setRawVal = AffinelyExtendBoundedPos

applyThroughBounded :: GetRawVal a => (BaseType a -> BaseType a) -> a -> a
applyThroughBounded f = setRawVal . (applyToBounded f)

applyToBounded :: GetRawVal a => (BaseType a -> b) -> a -> b
applyToBounded f = f . getRawVal

apply2ThroughBounded :: GetRawVal a => (BaseType a -> BaseType a -> BaseType a) -> a -> a -> a
apply2ThroughBounded f x y = setRawVal (apply2ToBounded f x y)

apply2ToBounded :: GetRawVal a => (BaseType a -> BaseType a -> b) -> a -> a -> b
apply2ToBounded f x y = f (getRawVal x) (getRawVal y)


applyAffine :: (UnpackType a ~ b, b ~ t (BaseType a), CanAffinelyExtend a, CanAffinelyPack t, CanAffinelyPackConstraint t a) => (b -> b) -> a -> a
applyAffine f = pack . f . unpack

applyAffine2 :: (UnpackType a ~ b, b ~ t (BaseType a), CanAffinelyExtend a, CanAffinelyPack t, CanAffinelyPackConstraint t a) => (b -> b -> b) -> a -> a -> a
applyAffine2 f x y = pack (f (unpack x) (unpack y))

applyAffineOutPair2 :: (UnpackType a ~ b, b ~ t (BaseType a), CanAffinelyExtend a, CanAffinelyPack t, CanAffinelyPackConstraint t a) => (b -> b -> (b, b)) -> a -> a -> (a, a)
applyAffineOutPair2 f x y = let (x', y') = f (unpack x) (unpack y) in (pack x', pack y')

applyAffineNoPack :: (UnpackType a ~ b, b ~ t (BaseType a), CanAffinelyExtend a) => (b -> c) -> a -> c
applyAffineNoPack f = f . unpack


-- Eq

instance Eq a => Eq (AffinelyExtendBoth a) where
  x == y = case (x,y) of
    (Finite x, Finite y) -> x == y
    (PositiveInfinity, PositiveInfinity) -> True
    (NegativeInfinity, NegativeInfinity) -> True
    _ -> False

  x /= y = case (x,y) of
    (Finite x, Finite y) -> x /= y
    (PositiveInfinity, PositiveInfinity) -> False
    (NegativeInfinity, NegativeInfinity) -> False
    _ -> True

instance Eq a => Eq (AffinelyExtendPos a) where
  x == y = case (x,y) of
    (Finite x, Finite y) -> x == y
    (PositiveInfinity, PositiveInfinity) -> True
    _ -> False

  x /= y = case (x,y) of
    (Finite x, Finite y) -> x /= y
    (PositiveInfinity, PositiveInfinity) -> False
    _ -> True

{-# INLINE [1] eqBounded #-}
eqBounded :: (GetRawVal a, Eq (BaseType a)) => a -> a -> Bool
eqBounded = apply2ToBounded (==)

{-# RULES
"eqBounded/pack" forall x y. (packPos x) `eqBounded` (packPos y) = x == y
"eqBounded/pack" forall x y. (packBoth x) `eqBounded` (packBoth y) = x == y
#-}

{-# INLINE [1] neqBounded #-}
neqBounded :: (GetRawVal a, Eq (BaseType a)) => a -> a -> Bool
neqBounded = apply2ToBounded (/=)

{-# RULES
"neqBounded/pack" forall x y. (packPos x) `neqBounded` (packPos y) = x /= y
"neqBounded/pack" forall x y. (packBoth x) `neqBounded` (packBoth y) = x /= y
#-}

instance Eq a => Eq (AffinelyExtendBoundedBoth a) where
  (==) = eqBounded
  (/=) = neqBounded

instance Eq a => Eq (AffinelyExtendBoundedPos a) where
  (==) = eqBounded
  (/=) = neqBounded

-- Ord

instance Ord a => Ord (AffinelyExtendBoth a) where
  x `compare` y = case (x,y) of
    (Finite x, Finite y) -> x `compare` y
    (PositiveInfinity, PositiveInfinity) -> EQ
    (NegativeInfinity, NegativeInfinity) -> EQ
    (_, PositiveInfinity) -> LT
    (PositiveInfinity, _) -> GT
    (NegativeInfinity, _) -> LT
    (_, NegativeInfinity) -> GT

  x < y = case (x,y) of
    (Finite x, Finite y) -> x < y
    (PositiveInfinity, _) -> False
    (_, NegativeInfinity) -> False
    _ -> True

  x <= y = case (x,y) of
    (Finite x, Finite y) -> x <= y
    (_, PositiveInfinity) -> True
    (NegativeInfinity, _) -> True
    _ -> False

  x > y = case (x,y) of
    (Finite x, Finite y) -> x > y
    (_, PositiveInfinity) -> False
    (NegativeInfinity, _) -> False
    _ -> True

  x >= y = case (x,y) of
    (Finite x, Finite y) -> x >= y
    (PositiveInfinity, _) -> True
    (_, NegativeInfinity) -> True
    _ -> False

  min x y = case (x, y) of
    (Finite x, Finite y) -> Finite (min x y)
    (_, PositiveInfinity) -> x
    (PositiveInfinity, _) -> y
    _ -> NegativeInfinity

  max x y = case (x, y) of
    (Finite x, Finite y) -> Finite (max x y)
    (_, NegativeInfinity) -> x
    (NegativeInfinity, _) -> y
    _ -> PositiveInfinity

instance Ord a => Ord (AffinelyExtendPos a) where
  x `compare` y = case (x,y) of
    (Finite x, Finite y) -> x `compare` y
    (PositiveInfinity, PositiveInfinity) -> EQ
    (Finite _, PositiveInfinity) -> LT
    (PositiveInfinity, Finite _) -> GT

  x < y = case (x,y) of
    (Finite x, Finite y) -> x < y
    (PositiveInfinity, _) -> False
    _ -> True

  x <= y = case (x,y) of
    (Finite x, Finite y) -> x <= y
    (_, PositiveInfinity) -> True
    _ -> False

  x > y = case (x,y) of
    (Finite x, Finite y) -> x > y
    (_, PositiveInfinity) -> False
    _ -> True

  x >= y = case (x,y) of
    (Finite x, Finite y) -> x >= y
    (PositiveInfinity, _) -> True
    _ -> False

  min x y = case (x, y) of
    (Finite x, Finite y) -> Finite (min x y)
    (_, PositiveInfinity) -> x
    (PositiveInfinity, _) -> y

  max x y = case (x, y) of
    (Finite x, Finite y) -> Finite (max x y)
    _ -> PositiveInfinity

{-# INLINE [1] compareBounded #-}
compareBounded :: (GetRawVal a, Ord (BaseType a)) => a -> a -> Ordering
compareBounded = apply2ToBounded compare

{-# RULES
"compareBounded/pack" forall x y. (packPos x) `compareBounded` (packPos y) = x `compare` y
"compareBounded/pack" forall x y. (packBoth x) `compareBounded` (packBoth y) = x `compare` y
#-}

{-# INLINE [1] ltBounded #-}
ltBounded :: (GetRawVal a, Ord (BaseType a)) => a -> a -> Bool
ltBounded = apply2ToBounded (<)

{-# RULES
"ltBounded/pack" forall x y. (packPos x) `ltBounded` (packPos y) = x < y
"ltBounded/pack" forall x y. (packBoth x) `ltBounded` (packBoth y) = x < y
#-}

{-# INLINE [1] gtBounded #-}
gtBounded :: (GetRawVal a, Ord (BaseType a)) => a -> a -> Bool
gtBounded = apply2ToBounded (>)

{-# RULES
"gtBounded/pack" forall x y. (packPos x) `gtBounded` (packPos y) = x > y
"gtBounded/pack" forall x y. (packBoth x) `gtBounded` (packBoth y) = x > y
#-}

{-# INLINE [1] lteBounded #-}
lteBounded :: (GetRawVal a, Ord (BaseType a)) => a -> a -> Bool
lteBounded = apply2ToBounded (<=)

{-# RULES
"lteBounded/pack" forall x y. (packPos x) `lteBounded` (packPos y) = x <= y
"lteBounded/pack" forall x y. (packBoth x) `lteBounded` (packBoth y) = x <= y
#-}

{-# INLINE [1] gteBounded #-}
gteBounded :: (GetRawVal a, Ord (BaseType a)) => a -> a -> Bool
gteBounded = apply2ToBounded (>=)

{-# RULES
"gteBounded/pack" forall x y. (packPos x) `gteBounded` (packPos y) = x >= y
"gteBounded/pack" forall x y. (packBoth x) `gteBounded` (packBoth y) = x >= y
#-}

{-# INLINE [1] maxBounded #-}
maxBounded :: (GetRawVal a, Ord (BaseType a)) => a -> a -> a
maxBounded = apply2ThroughBounded max

{-# RULES
"maxBounded/pack" forall x y. maxBounded (packPos x) (packPos y) = max x y
"maxBounded/pack" forall x y. maxBounded (packBoth x) (packBoth y) = max x y
#-}

{-# INLINE [1] minBounded #-}
minBounded :: (GetRawVal a, Ord (BaseType a)) => a -> a -> a
minBounded = apply2ThroughBounded min

{-# RULES
"minBounded/pack" forall x y. minBounded (packPos x) (packPos y) = min x y
"minBounded/pack" forall x y. minBounded (packBoth x) (packBoth y) = min x y
#-}

instance Ord a => Ord (AffinelyExtendBoundedBoth a) where
  compare = compareBounded
  (<) = ltBounded
  (>) = gtBounded
  (<=) = lteBounded
  (>=) = gteBounded
  min = minBounded
  max = maxBounded

instance Ord a => Ord (AffinelyExtendBoundedPos a) where
  compare = compareBounded
  (<) = ltBounded
  (>) = gtBounded
  (<=) = lteBounded
  (>=) = gteBounded
  min = minBounded
  max = maxBounded

-- Show


showsPosInf :: ShowS
showsPosInf = shows (posInf :: Double)

showsNegInf :: ShowS
showsNegInf = shows (negInf :: Double)

strPosInf = showsPosInf ""
strNegInf = showsNegInf ""

instance Show a => Show (AffinelyExtendBoth a) where
  showsPrec _ = \case
    (Finite x) -> shows x
    PositiveInfinity -> showsPosInf
    NegativeInfinity -> showsNegInf

instance Show a => Show (AffinelyExtendPos a) where
  showsPrec _ = \case
    (Finite x) -> shows x
    PositiveInfinity -> showsPosInf

instance (Ord a, Bounded a, Num a, Show a) => Show (AffinelyExtendBoundedBoth a) where
  showsPrec _ x = if
    | isPos x -> showsPosInf
    | isNegInf x -> showsNegInf
    | otherwise -> shows x

instance (Eq a, Bounded a, Show a) => Show (AffinelyExtendBoundedPos a) where
  showsPrec _ x = if
    | isFinite x -> shows x
    | otherwise -> showsPosInf

-- Read

readsPrecInfGeneric :: forall a. (CanAffinelyExtend a, Read (BaseType a)) => (ReadS a) -> Int -> ReadS a
readsPrecInfGeneric infParse n s =
  let
    ordinaryParse :: [(BaseType a, String)]
    ordinaryParse = readsPrec n s
  in
    case ordinaryParse of
      (_:_) -> map (\(x,y) -> (affinelyExtend x, y)) ordinaryParse
      _ -> infParse s

maybeTake :: Eq a => [a] -> [a] -> Maybe [a]
maybeTake findStr str =
  let
    (toCheck, rest) = splitAt (length findStr) str
  in
    if (toCheck == findStr) then Just rest else Nothing

maybeTakeVal :: Eq a => b -> [a] -> [a] -> Maybe (b, [a])
maybeTakeVal v findStr str = do
  r <- maybeTake findStr str
  return (v, r)

maybeParseShow :: Show a => a -> String -> Maybe (a, String)
maybeParseShow v str = maybeTakeVal v (show v) str

maybeParsePosInf :: (HasPositiveInfinity a, Show a) => String -> Maybe (a, String)
maybeParsePosInf = maybeParseShow posInf

maybeParseNegInf :: (HasBothInfinities a, Show a) => String -> Maybe (a, String)
maybeParseNegInf = maybeParseShow negInf

parseBothInf :: (CanAffinelyExtend a, HasBothInfinities a, Show a) => ReadS a
parseBothInf s = maybeToList (maybeParsePosInf s <|> maybeParseNegInf s)

parsePosInf :: (CanAffinelyExtend a, HasPositiveInfinity a, Show a) => ReadS a
parsePosInf = maybeToList . maybeParsePosInf

readBothInf :: (Read (BaseType a), CanAffinelyExtend a, HasBothInfinities a, Show a) => Int -> ReadS a
readBothInf = readsPrecInfGeneric parseBothInf

readPosInf :: (Read (BaseType a), CanAffinelyExtend a, HasPositiveInfinity a, Show a) => Int -> ReadS a
readPosInf = readsPrecInfGeneric parsePosInf

instance (Show a, Read a) => Read (AffinelyExtendBoth a) where
  readsPrec = readBothInf

instance (Show a, Read a) => Read (AffinelyExtendPos a) where
  readsPrec = readPosInf

instance (Bounded a, Ord a, Num a, Read a, Show a) => Read (AffinelyExtendBoundedBoth a) where
  readsPrec = readBothInf

instance (Bounded a, Eq a, Read a, Show a) => Read (AffinelyExtendBoundedPos a) where
  readsPrec = readPosInf

-- Enum

toEnum' :: (CanAffinelyExtend a, Enum (BaseType a)) => Int -> a
toEnum' x = affinelyExtend (toEnum x)

fromEnum' :: (CanAffinelyExtend a, Enum (BaseType a)) => a -> Int
fromEnum' x = case (unpackBoth x) of
  Finite x -> fromEnum x
  _ -> error "Can't 'fromEnum' an infinity"

succ' :: (CanAffinelyExtend a, Enum (BaseType a)) => a -> a
succ' x = case unpackBoth x of
  Finite x -> affinelyExtend (succ x)
  _ -> x

pred' :: (CanAffinelyExtend a, Enum (BaseType a)) => a -> a
pred' x = case unpackBoth x of
  Finite x -> affinelyExtend (pred x)
  _ -> x

enumFrom' :: (CanAffinelyExtend a, Enum (BaseType a)) => a -> [a]
enumFrom' x = case unpackBoth x of
  Finite x -> map affinelyExtend (enumFrom x)
  _ -> repeat x

enumFromThen' :: (CanAffinelyExtend a, Enum (BaseType a)) => a -> a -> [a]
enumFromThen' x y = case (unpackBoth x, unpackBoth y) of
  (Finite x, Finite y) -> map affinelyExtend (enumFromThen x y)
  _ -> error "Can't enumFromThen an infinity."

enumFromTo' :: (CanAffinelyExtend a, Enum (BaseType a)) => a -> a -> [a]
enumFromTo' x y = case (unpackBoth x, unpackBoth y) of
  (Finite x, Finite y) -> map affinelyExtend (enumFromTo x y)
  (Finite x, PositiveInfinity) -> map affinelyExtend (enumFrom x)
  (Finite _, NegativeInfinity) -> []
  (NegativeInfinity, Finite _) -> repeat x
  (NegativeInfinity, PositiveInfinity) -> repeat x
  (PositiveInfinity, NegativeInfinity) -> []
  (PositiveInfinity, Finite _) -> []
  _ -> error "Can't enumFromTo identical infinities."

enumFromThenTo' :: (CanAffinelyExtend a, Enum (BaseType a), Ord (BaseType a)) => a -> a -> a -> [a]
enumFromThenTo' x y z = case (unpackBoth x, unpackBoth y, unpackBoth z) of
  (Finite x, Finite y, Finite z) -> map affinelyExtend (enumFromThenTo x y z)
  (Finite x, Finite y, PositiveInfinity) -> if (x <= y) then map affinelyExtend (enumFromThen x y) else []
  (Finite x, Finite y, NegativeInfinity) -> if (x >= y) then map affinelyExtend (enumFromThen x y) else []
  _ -> error "Can't enumFromThen infinity."

instance (Ord a, Enum a) => Enum (AffinelyExtendBoth a) where
  toEnum = toEnum'
  fromEnum = fromEnum'
  succ = succ'
  pred = pred'
  enumFrom = enumFrom'
  enumFromThen = enumFromThen'
  enumFromThenTo = enumFromThenTo'

instance (Ord a, Enum a) => Enum (AffinelyExtendPos a) where
  toEnum = toEnum'
  fromEnum = fromEnum'
  succ = succ'
  pred = pred'
  enumFrom = enumFrom'
  enumFromThen = enumFromThen'
  enumFromThenTo = enumFromThenTo'

instance (Bounded a, Ord a, Enum a, Num a) => Enum (AffinelyExtendBoundedBoth a) where
  toEnum = toEnum'
  fromEnum = fromEnum'
  succ = succ'
  pred = pred'
  enumFrom = enumFrom'
  enumFromThen = enumFromThen'
  enumFromThenTo = enumFromThenTo'

instance (Bounded a, Ord a, Enum a, Num a) => Enum (AffinelyExtendBoundedPos a) where
  toEnum = toEnum'
  fromEnum = fromEnum'
  succ = succ'
  pred = pred'
  enumFrom = enumFrom'
  enumFromThen = enumFromThen'
  enumFromThenTo = enumFromThenTo'
-- Num


signToInf :: (Ord a, Num a, Num b, HasBothInfinities b) => a -> b
signToInf x = case (x `compare` 0) of
  GT -> posInf
  LT -> negInf
  EQ -> 0

signToNegInf :: (Ord a, Num a, Num b, HasBothInfinities b) => a -> b
signToNegInf x = case (x `compare` 0) of
  GT -> negInf
  LT -> posInf
  EQ -> 0

signToInfPos :: (Ord a, Num a, Num b, HasPositiveInfinity b) => a -> b
signToInfPos x = case (x `compare` 0) of
  GT -> posInf
  EQ -> 0
  LT -> error "Operation produced negative infinity for type with only positive infinity."

signToInfDivide :: (Ord a, Num a, Num b, HasBothInfinities b) => a -> b
signToInfDivide x = case (x `compare` 0) of
  GT -> posInf
  LT -> negInf
  EQ -> error "Can't divide by 0"

signToNegInfDivide :: (Ord a, Num a, Num b, HasBothInfinities b) => a -> b
signToNegInfDivide x = case (x `compare` 0) of
  GT -> negInf
  LT -> posInf
  EQ -> error "Can't divide by 0"

signToInfDividePos :: (Ord a, Num a, Num b, HasPositiveInfinity b) => a -> b
signToInfDividePos x =  case (x `compare` 0) of
  GT -> posInf
  LT -> error "Operation produced negative infinity for type with only positive infinity."
  EQ -> error "Can't divide by 0"


instance (Ord a, Num a) => Num (AffinelyExtendBoth a) where
  x + y = case (x,y) of
    (Finite x, Finite y) -> Finite (x + y)
    (_, Finite _) -> x
    (Finite _, _) -> y
    (PositiveInfinity, PositiveInfinity) -> PositiveInfinity
    (NegativeInfinity, NegativeInfinity) -> NegativeInfinity
    _ -> error "Can't add positive and negative infinity"

  x - y = case (x,y) of
    (Finite x, Finite y) -> Finite (x - y)
    (_, Finite _) -> x
    (Finite _, _) -> negate y
    (PositiveInfinity, NegativeInfinity) -> PositiveInfinity
    (NegativeInfinity, PositiveInfinity) -> NegativeInfinity
    _ -> error "Can't subtract identical infinities"

  x * y = case (x,y) of
    (Finite x, Finite y) -> Finite (x * y)
    (Finite x, PositiveInfinity) -> signToInf x
    (PositiveInfinity, Finite y) -> signToInf y
    (Finite x, NegativeInfinity) -> signToNegInf x
    (NegativeInfinity, Finite y) -> signToNegInf y
    (PositiveInfinity, PositiveInfinity) -> PositiveInfinity
    (PositiveInfinity, NegativeInfinity) -> NegativeInfinity
    (NegativeInfinity, PositiveInfinity) -> NegativeInfinity
    (NegativeInfinity, NegativeInfinity) -> PositiveInfinity

  signum = \case
    Finite x -> Finite (signum x)
    PositiveInfinity -> 1
    NegativeInfinity -> -1

  fromInteger = Finite . fromInteger

  negate = \case
    Finite x -> Finite (negate x)
    PositiveInfinity -> NegativeInfinity
    NegativeInfinity -> PositiveInfinity

  abs = \case
    Finite x -> Finite (abs x)
    _ -> PositiveInfinity

instance (Ord a, Num a) => Num (AffinelyExtendPos a) where
  x + y = case (x,y) of
    (Finite x, Finite y) -> Finite (x + y)
    _ -> PositiveInfinity

  x - y = case (x,y) of
    (Finite x, Finite y) -> Finite (x - y)
    (_, Finite _) -> PositiveInfinity
    (_, PositiveInfinity) -> error "Can't subtract positive infinity from type with no negative infinity"

  x * y = case (x,y) of
    (Finite x, Finite y) -> Finite (x * y)
    (Finite x, PositiveInfinity) -> signToInfPos x
    (PositiveInfinity, Finite y) -> signToInfPos y
    (PositiveInfinity, PositiveInfinity) -> PositiveInfinity

  signum = \case
    Finite x -> Finite (signum x)
    PositiveInfinity -> 1

  fromInteger = Finite . fromInteger

  negate x = case x of
    Finite x -> Finite (negate x)
    PositiveInfinity -> error "Can't negate positive infinity with type with no negative infinity"

  abs = \case
    Finite x -> Finite (abs x)
    PositiveInfinity -> PositiveInfinity

{-# INLINE [1] fromIntegerGeneric #-}
fromIntegerGeneric :: (Ord (BaseType a), Num (BaseType a), CanAffinelyExtend a) => Integer -> a
fromIntegerGeneric = affinelyExtend . fromInteger

{-# INLINE [1] negateBounded #-}
negateBounded :: (Ord (BaseType a), Num (BaseType a), CanAffinelyExtend a, GetRawVal a) => a -> a
negateBounded = applyThroughBounded negate

{-# INLINE [1] signumBounded #-}
signumBounded :: (Ord (BaseType a), Num (BaseType a), CanAffinelyExtend a, GetRawVal a) => a -> a
signumBounded = applyThroughBounded signum

{-# INLINE [1] absBounded #-}
absBounded :: (Ord (BaseType a), Num (BaseType a), CanAffinelyExtend a, GetRawVal a) => a -> a
absBounded = applyThroughBounded abs

instance (Ord a, Num a, Bounded a) => Num (AffinelyExtendBoundedBoth a) where
  (+) = applyAffine2 (+)
  (*) = applyAffine2 (*)
  (-) = applyAffine2 (-)

  negate = negateBounded
  signum = signumBounded

  fromInteger = fromIntegerGeneric

  abs = absBounded

instance (Ord a, Num a, Bounded a) => Num (AffinelyExtendBoundedPos a) where
  (+) = applyAffine2 (+)
  (*) = applyAffine2 (*)
  (-) = applyAffine2 (-)

  negate = negateBounded
  signum = signumBounded

  fromInteger = fromIntegerGeneric

  abs = absBounded

{-# RULES
"negate/packBoth" forall x. negateBounded (packBoth x) = packBoth (negate x)
"negate/packBoth" forall x. negateBounded (packPos x) = packPos (negate x)
"signum/packBoth" forall x. signumBounded (packBoth x) = packBoth (signum x)
"signum/packBoth" forall x. signumBounded (packPos x) = packPos (signum x)
"abs/packBoth" forall x. absBounded (packBoth x) = packBoth (abs x)
"abs/packBoth" forall x. absBounded (packPos x) = packPos (abs x)
"unpackBoth/fromInteger" forall x. unpackBoth (fromIntegerGeneric x) = fromInteger x
"unpackBoth/fromInteger" forall x. unpackPos (fromIntegerGeneric x) = fromInteger x
#-}

-- Real

instance (Real a) => Real (AffinelyExtendBoth a) where
  toRational x = case x of
    Finite x -> toRational x
    _ -> error "Can't toRational an infinite number"

instance (Real a) => Real (AffinelyExtendPos a) where
  toRational x = case x of
    Finite x -> toRational x
    _ -> error "Can't toRational an infinite number"

instance (Real a, Bounded a) => Real (AffinelyExtendBoundedBoth a) where
  toRational = applyAffineNoPack toRational

instance (Real a, Bounded a) => Real (AffinelyExtendBoundedPos a) where
  toRational = applyAffineNoPack toRational

-- Fractional

instance (Ord a, Fractional a) => Fractional (AffinelyExtendBoth a) where
  x / y = case (x,y) of
    (Finite x, Finite y) -> Finite (x / y)
    (Finite _, _) -> 0
    (PositiveInfinity, Finite y) -> signToInfDivide y
    (NegativeInfinity, Finite y) -> signToNegInfDivide y
    _ -> error "Can't divide infinities"

  recip = \case
    (Finite x) -> (Finite (recip x))
    _ -> 0

  fromRational = affinelyExtend . fromRational

instance (Ord a, Fractional a) => Fractional (AffinelyExtendPos a) where
  x / y = case (x,y) of
    (Finite x, Finite y) -> Finite (x / y)
    (Finite _, PositiveInfinity) -> 0
    (PositiveInfinity, Finite y) -> signToInfDividePos y
    (PositiveInfinity, PositiveInfinity) -> error "Can't divide infinities"

  recip = \case
    (Finite x) -> (Finite (recip x))
    _ -> 0

  fromRational = affinelyExtend . fromRational

instance (Ord a, Bounded a, Fractional a) => Fractional (AffinelyExtendBoundedBoth a) where
  (/) = applyAffine2 (/)
  recip = applyAffine recip
  fromRational = fromRationalGeneric

instance (Ord a, Bounded a, Fractional a) => Fractional (AffinelyExtendBoundedPos a) where
  (/) = applyAffine2 (/)
  recip = applyAffine recip
  fromRational = fromRationalGeneric

{-# INLINE [1] fromRationalGeneric #-}
fromRationalGeneric :: (Ord (BaseType a), Num (BaseType a), Fractional (BaseType a), CanAffinelyExtend a) => Rational -> a
fromRationalGeneric = affinelyExtend . fromRational

{-# RULES
"unpackBoth/fromRational" forall x. unpackBoth (fromRationalGeneric x) = fromRational x
#-}


instance Integral a => Integral (AffinelyExtendBoth a) where
  quot x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `quot` y)
    (Finite _, _) -> 0
    (PositiveInfinity, Finite y) -> signToInfDivide y
    (NegativeInfinity, Finite y) -> signToNegInfDivide y
    _ -> error "Can't 'quot' two infinities"

  rem x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `rem` y)
    (Finite _, _) -> x
    _ -> error "Can't have infinity as first argument of 'rem'"

  div x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `div` y)
    (Finite _, _) -> 0
    (PositiveInfinity, Finite y) -> signToInfDivide y
    (NegativeInfinity, Finite y) -> signToNegInfDivide y
    _ -> error "Can't 'div' two infinities"

  mod x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `mod` y)
    (Finite x', PositiveInfinity) -> if (x' >= 0) then x else error "Can't 'mod' with mixed signs and one infinity."
    (Finite x', NegativeInfinity) -> if (x' <= 0) then x else error "Can't 'mod' with mixed signs and one infinity."
    _ -> error "Can't have infinity as first argument of 'mod'"

  quotRem x y = case (x,y) of
    (Finite x, Finite y) -> let (x', y') = (x `quotRem` y) in (Finite x', Finite y')
    (Finite _, _) -> (0, x)
    (PositiveInfinity, Finite y) -> (signToInfDivide y, error "Can't have infinity as first argument of 'rem'")
    (NegativeInfinity, Finite y) -> (signToNegInfDivide y, error "Can't have infinity as first argument of 'rem'")
    _ -> error "Can't 'quotRem' two infinities"

  divMod x y = case (x,y) of
    (Finite x, Finite y) -> let (x', y') = (x `divMod` y) in (Finite x', Finite y')
    (Finite x', PositiveInfinity) -> (0, if (x' >= 0) then x else error "Can't 'mod' with mixed signs and one infinity.")
    (Finite x', NegativeInfinity) -> (0, if (x' <= 0) then x else error "Can't 'mod' with mixed signs and one infinity.")
    (PositiveInfinity, Finite y) -> (signToInfDivide y, error "Can't have infinity as first argument of 'mod'")
    (NegativeInfinity, Finite y) -> (signToNegInfDivide y, error "Can't have infinity as first argument of 'mod'")
    _ -> error "Can't 'divMod' two infinities"

  toInteger = \case
    (Finite x) -> toInteger x
    _ -> error "Can't 'toInteger' infinity"

instance Integral a => Integral (AffinelyExtendPos a) where
  quot x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `quot` y)
    (Finite _, PositiveInfinity) -> 0
    (PositiveInfinity, Finite y) -> signToInfDividePos y
    (PositiveInfinity, PositiveInfinity) -> error "Can't 'quot' two infinities"

  rem x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `rem` y)
    (Finite _, PositiveInfinity) -> x
    (PositiveInfinity, _) -> error "Can't have infinity as first argument of 'rem'"

  div x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `div` y)
    (Finite _, PositiveInfinity) -> 0
    (PositiveInfinity, Finite y) -> signToInfDividePos y
    (PositiveInfinity, PositiveInfinity) -> error "Can't 'div' two infinities"

  mod x y = case (x,y) of
    (Finite x, Finite y) -> Finite (x `mod` y)
    (Finite _, PositiveInfinity) -> x
    (PositiveInfinity, _) -> error "Can't have infinity as first argument of 'mod'"

  quotRem x y = case (x,y) of
    (Finite x, Finite y) -> let (x', y') = (x `quotRem` y) in (Finite x', Finite y')
    (Finite _, PositiveInfinity) -> (0, x)
    (PositiveInfinity, Finite y) -> (signToInfDividePos y, error "Can't have infinity as first argument of 'rem'")
    (PositiveInfinity, PositiveInfinity) -> error "Can't 'quotRem' two infinities"

  divMod x y = case (x,y) of
    (Finite x, Finite y) -> let (x', y') = (x `divMod` y) in (Finite x', Finite y')
    (Finite x', PositiveInfinity) -> (0, if (x' >= 0) then x else error "Can't 'mod' with mixed signs and one infinity.")
    (PositiveInfinity, Finite y) -> (signToInfDividePos y, error "Can't have infinity as first argument of 'mod'")
    (PositiveInfinity, PositiveInfinity) -> error "Can't 'divMod' two infinities"

  toInteger = \case
    (Finite x) -> toInteger x
    PositiveInfinity -> error "Can't 'toInteger' infinity"

{-# INLINE [1] remBounded #-}
remBounded :: (GetRawVal a, CanAffinelyExtend a, Integral (BaseType a)) => a -> a -> a
remBounded x y = assert (isFinite x) (apply2ThroughBounded rem x y)

{-# INLINE [1] modBounded #-}
modBounded :: (GetRawVal a, CanAffinelyExtend a, Integral (BaseType a)) => a -> a -> a
modBounded x y = assert (isFinite x) (apply2ThroughBounded mod x y)

{-# INLINE [1] toIntegerBounded #-}
toIntegerBounded :: (GetRawVal a, CanAffinelyExtend a, Integral (BaseType a)) => a -> Integer
toIntegerBounded x = assert (isFinite x) (toInteger (getRawVal x))

instance (Bounded a, Integral a) => Integral (AffinelyExtendBoundedBoth a) where
  quot = applyAffine2 quot

  rem = remBounded

  div = applyAffine2 div

  mod = modBounded

  quotRem = applyAffineOutPair2 quotRem
  divMod = applyAffineOutPair2 divMod

  toInteger = toIntegerBounded

instance (Bounded a, Integral a) => Integral (AffinelyExtendBoundedPos a) where
  quot = applyAffine2 quot

  rem = remBounded

  div = applyAffine2 div

  mod = modBounded

  quotRem = applyAffineOutPair2 quotRem
  divMod = applyAffineOutPair2 divMod

  toInteger = toIntegerBounded

{-# RULES
"rem/packBoth" forall x y. remBounded (packBoth x) (packBoth y) = packBoth (rem x y)
"rem/packPos" forall x y. remBounded (packPos x) (packPos y) = packPos (rem x y)
"mod/packBoth" forall x y. modBounded (packBoth x) (packBoth y) = packBoth (mod x y)
"mod/packPos" forall x y. modBounded (packPos x) (packPos y) = packPos (mod x y)
"toInteger/packBoth" forall x. toIntegerBounded (packBoth x) = toInteger x
"toInteger/packPos" forall x. toIntegerBounded (packPos x) = toInteger x
#-}
