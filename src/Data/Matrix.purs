module Data.Matrix where

import Prelude
import Data.Array as Array
import Data.Foldable (foldl, foldr, foldMap, class Foldable)
import Data.Maybe (Maybe(..), fromJust)
import Data.Traversable (traverse, sequence, class Traversable)
import Data.Tuple (Tuple(Tuple))
import Data.String (joinWith)
import Data.Typelevel.Num (class Min, class Sub, class LtEq, class Pred, class Lt)
import Data.Typelevel.Num.Ops (class Add, class Succ, class Max)
import Data.Typelevel.Num.Reps (D3, D2, D1, D0, d0, d1)
import Data.Typelevel.Num.Sets (toInt, class Pos, class Nat)
import Data.Typelevel.Undefined (undefined)
import Data.Unfoldable (class Unfoldable)
import Data.CommutativeRing (class CommutativeRing)
import Partial.Unsafe (unsafePartial)
import Data.Vec as Vec
import Data.Vec ((+>))

-- stored as Vec of rows
newtype Matrix h w a = Matrix (Vec.Vec h (Vec.Vec w a))

empty :: ∀a. Matrix D0 D0 a
empty = Matrix Vec.empty

consRowVec :: ∀h h' w w' a. Succ h h' => Nat w =>
  Vec.Vec w a -> Matrix h w a -> Matrix h' w a
consRowVec vec (Matrix m) = Matrix $ Vec.cons vec m

infixr 4 consRowVec as ⤓

consColVec :: ∀h w w' a. Succ w w' => Nat h => Vec.Vec h a -> Matrix h w a -> Matrix h w' a
consColVec vec (Matrix m) = Matrix $ Vec.zipWithE (Vec.cons) vec m

infixr 5 consColVec as ⇥

singleton :: ∀a. a -> Matrix D1 D1 a
singleton x = Vec.singleton x ⤓ Vec.empty ⇥ empty

matrix2d :: ∀a. a -> a -> a -> a -> Matrix D2 D2 a
matrix2d x11 x12 x21 x22 =
  Vec.vec2 x11 x12
  ⤓
  Vec.singleton x21 ⇥ (singleton x22)

fill :: ∀h w ih iw a. Nat h => Nat w =>  (Int -> Int -> a) -> Matrix h w a
fill f = Matrix $ Vec.fill (\y -> Vec.fill (\x -> f x y))


replicate' :: ∀w h a. Nat w => Nat h => a -> Matrix h w a
replicate' a = Matrix $ Vec.replicate' (Vec.replicate' a)

zipWithE :: ∀w h a b c. Nat w => Nat h =>
  (a -> b -> c) -> Matrix h w a -> Matrix h w b -> Matrix h w c
zipWithE f (Matrix a) (Matrix b) = Matrix $ Vec.zipWithE (Vec.zipWithE f) a b


instance showMatrix :: (Nat h, Nat w, Show a) => Show (Matrix h w a) where
  show (Matrix m) = "  " <> (joinWith "\n  " $ Vec.toArray $ map show m)

instance functorMatrix :: (Nat h, Nat w) => Functor (Matrix h w) where
  map f (Matrix m) = Matrix $ map (map f) m

-- Matrix Ring over CommutativeRing a

add :: ∀h w a. Nat h => Nat w =>CommutativeRing a => Matrix h w a -> Matrix h w a -> Matrix h w a
add a  b = zipWithE (+) a b

negate :: ∀h w a. Nat h => Nat w => CommutativeRing a => Matrix h w a -> Matrix h w a
negate = map (\v -> zero - v)

columnVec :: ∀h w a x. Nat x => Lt x w => Nat h => Matrix h w a -> x -> Vec.Vec h a
columnVec (Matrix m) i = map (\row -> row `Vec.index` (undefined :: x) ) m

rowVec :: ∀h w a y. Nat y => Lt y h => Nat w => Matrix h w a -> y -> Vec.Vec w a
rowVec (Matrix m) i = m `Vec.index` (undefined :: y)

rowVecUnsafe :: ∀h w a. Nat h => Nat w => Matrix h w a -> Int -> Vec.Vec w a
rowVecUnsafe (Matrix m) i =  unsafePartial $ Array.unsafeIndex (Vec.toArray m) i

columnVecUnsafe :: ∀h w a. Nat h => Nat w => Matrix h w a -> Int -> Vec.Vec h a
columnVecUnsafe (Matrix m) i = map (\row -> unsafePartial $ Array.unsafeIndex (Vec.toArray row) i) m

mul :: ∀s a. Nat s => CommutativeRing a => Matrix s s a -> Matrix s s a -> Matrix s s a
mul a b = fill (\x y -> rowVecUnsafe a y `Vec.scalarMul` columnVecUnsafe b x)


instance semiringMatrix :: (Nat s, CommutativeRing a) => Semiring (Matrix s s a) where
  add = add
  zero = replicate' zero
  mul = mul
  one = fill (\x y -> if (x==y) then one else zero)

instance ringMatrix :: (Nat s, CommutativeRing a) => Ring (Matrix s s a) where
  sub a b = add a (negate b)

m = matrix2d 1 2 3 4
