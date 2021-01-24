{-# LANGUAGE StandaloneKindSignatures, TypeFamilies, FunctionalDependencies, DeriveFoldable, UndecidableSuperClasses #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}
module Lib where

import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy(..))

-- Some utilities
type (.==) :: (a -> Constraint) -> a -> Constraint
type f .== a = f a

infix 4 .==

data Some (c :: x -> Constraint)
  where
  Some :: c v => Proxy c -> Proxy v -> Some c

type ($) :: (a -> b -> Constraint) -> a -> b -> Constraint
class (f x .== y) => (f $ x) y | f x -> y
  where
  (^$) :: Proxy f -> Proxy x -> Proxy y
  Proxy ^$ Proxy = Proxy

class (forall x y. f x y => (f $ x) .== y) => Function f

evaluate :: Function f => Proxy f -> Proxy x -> Some (f x)
evaluate f x = Some Proxy (f x)

type Reflect :: Type -> Constraint
class Reflect k
  where
  type Rep k :: k -> *
  reflect :: Rep k v -> k
  promote :: (forall x. c x) => Proxy c -> (forall x. c x => Rep k x -> r) -> k -> r
  -- promoteF :: Function f => Proxy f -> (forall x y. f x y => Rep k x -> r) -> k -> r

-- Natural numbers
data Nat = Z | S Nat

type N0 = 'Z
type N1 = 'S 'Z
type N2 = 'S N1
type N3 = 'S N2
type N4 = 'S N3
type N5 = 'S N4
type N6 = 'S N5
type N7 = 'S N6
type N8 = 'S N7
type N9 = 'S N8
type N10 = 'S N9
type N11 = 'S N10
type N12 = 'S N11
type N13 = 'S N12
type N14 = 'S N13
type N15 = 'S N14
type N16 = 'S N15

-- Natural numbers singletons
data SNat n
  where
  SZ :: SNat N0
  SS :: SNat n -> SNat ('S n)

instance Reflect Nat
  where
  type Rep Nat = SNat
  reflect SZ = Z
  reflect (SS n) = S $ reflect n

  promote _ f Z = f SZ
  promote p f (S n) = promote p (\v -> f $ SS v) n

n0 = SZ
n1 = SS n0
n2 = SS n1
n3 = SS n2
n4 = SS n3
n5 = SS n4
n6 = SS n5
n7 = SS n6
n8 = SS n7
n9 = SS n8
n10 = SS n9
n11 = SS n10
n12 = SS n11
n13 = SS n12
n14 = SS n13
n15 = SS n14
n16 = SS n15

-- We're going to do all our type level computation with typeclasses
-- Induction for all the "binary operators" will be on the right term

-- Addition
type (+) :: Nat -> Nat -> Nat -> Constraint
class (n + m) r | n m -> r

infixl 6 +

instance (n + N0) n
-- instance (N0 + m) m
instance (n + m .== r) => (n + 'S m) ('S r)
-- instance (n + m .== r) => ('S n + m) ('S r)

-- Multiplication
type (×) :: Nat -> Nat -> Nat -> Constraint
class (n × m) r | n m -> r

infixl 7 ×

instance (n × N0) N0
-- instance (N0 × m) N0
instance (n × m .== r, n + r .== r') => (n × 'S m) r'
-- instance (n × m .== r, m + r .== r') => ('S n × m) r'

-- Exponentiation
type (^) :: Nat -> Nat -> Nat -> Constraint
class (n ^ e) r | n e -> r

infixr 8 ^

instance (n ^ N0) N1
instance (n ^ e .== r, n × r .== r') => (n ^ 'S e) r'

-- Vectors
data Vec n a
  where
  VNil :: Vec N0 a
  VCons :: a -> Vec n a -> Vec ('S n) a

deriving instance Functor (Vec n)
deriving instance Foldable (Vec n)

class (n1 + n2 .== n3) => VAppend n1 n2 n3 | n1 n2 -> n3
  where
  vappend :: Vec n1 a -> Vec n2 a -> Vec n3 a

instance VAppend n N0 n
  where
  vappend v VNil = v

-- instance VAppend N0 n n
--   where
--   vappend VNil v = v

instance VAppend n m r => VAppend n ('S m) ('S r)
  where
  vappend v1 (VCons a v2) = VCons a $ vappend v1 v2

-- instance VAppend n m r => VAppend ('S n) m ('S r)
--   where
--   vappend (VCons a v1) v2 = VCons a $ vappend v1 v2

-- Produce a feature matrix
class (N2 ^ n .== r) => Toggles n r | n -> r
  where
  toggles :: SNat n -> Vec r (Vec n Bool)

instance Toggles n r => (Toggles $ n) r
instance Function Toggles

instance Toggles N0 N1 
  where
  toggles SZ = VNil `VCons` VNil

instance (Toggles n r, VAppend r r r', (N2 × r) .== r') => Toggles ('S n) r'
  where
  toggles (SS n) =
    let
      rest = toggles n
    in (VCons False <$> rest) `vappend` (VCons True <$> rest)

-- Tests
foo = Proxy @Toggles ^$ Proxy @N4


test :: Vec N16 (Vec N4 Bool)
test = toggles n4

-- toggleTable :: Nat -> [String]
-- toggleTable = promote _ _

message :: String
message = "Ready? Get set... GO!"
