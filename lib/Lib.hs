{-# LANGUAGE StandaloneKindSignatures, TypeFamilies, FunctionalDependencies, DeriveFoldable, UndecidableSuperClasses #-}
-- {-# OPTIONS_GHC -freduction-depth=0 #-}
module Lib where

import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy(..))
import Data.Foldable (toList)
import Data.List (intercalate, intersperse)
import Data.Bifunctor (first)
import Control.Applicative (liftA2)

-- Some utilities
type (.==) :: (a -> Constraint) -> a -> Constraint
type f .== a = f a

infix 4 .==

class (forall x. c x) => Total c

data Some (c :: x -> Constraint)
  where
  Some :: c v => Proxy c -> Proxy v -> Some c

type ($) :: (a -> b -> Constraint) -> a -> b -> Constraint
class (f x .== y) => (f $ x) y | f x -> y
  where
  (^$) :: Proxy f -> Proxy x -> Proxy y
  Proxy ^$ Proxy = Proxy

class (forall x y. f x y => (f $ x) .== y) => Function f

-- evaluate :: Function f => Proxy f -> Proxy x -> Some (f x)
-- evaluate f x = Some Proxy (f x)

type Reflect :: Type -> Constraint
class Reflect k
  where
  type Rep k :: k -> *
  reflect :: Rep k v -> k
  promote :: Total c => Proxy c -> (forall x. c x => Rep k x -> r) -> k -> r
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

-- Upper-bounded natural numbers
data Fin n
  where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

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
-- Induction for all the "binary operators" will be on the left term

-- Addition
type (+) :: Nat -> Nat -> Nat -> Constraint
class (n + m) r | n m -> r

infixl 6 +

-- instance (n + N0) n
instance (N0 + m) m
-- instance (n + m .== r) => (n + 'S m) ('S r)
instance (n + m .== r) => ('S n + m) ('S r)

-- Multiplication
type (×) :: Nat -> Nat -> Nat -> Constraint
class (n × m) r | n m -> r

infixl 7 ×

-- instance (n × N0) N0
instance (N0 × m) N0
-- instance (n × m .== r, n + r .== r') => (n × 'S m) r'
instance (n × m .== r, m + r .== r') => ('S n × m) r'

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

deriving instance Show a => Show (Vec n a)
deriving instance Foldable (Vec n)
deriving instance Functor (Vec n)

instance Applicative (Vec N0)
  where
  pure _ = VNil
  liftA2 _ VNil VNil = VNil

instance Applicative (Vec n) => Applicative (Vec ('S n))
  where
  pure a = VCons a $ pure a
  liftA2 f (VCons a v1) (VCons b v2) = VCons (f a b) $ liftA2 f v1 v2

vlength :: Vec n a -> SNat n
vlength VNil = SZ
vlength (VCons _ v) = SS $ vlength v

vindex :: Fin n -> Vec n a -> a
vindex FZ (VCons a _) = a
vindex (FS n) (VCons _ v) = vindex n v

vindexed :: Vec n a -> Vec n (Fin n, a)
vindexed VNil = VNil
vindexed (VCons a v) = (FZ, a) `VCons` fmap (first FS) (vindexed v)

class (n1 + n2 .== n3) => VAppend n1 n2 n3 | n1 n2 -> n3
  where
  vappend :: Vec n1 a -> Vec n2 a -> Vec n3 a

-- instance VAppend n N0 n
--   where
--   vappend v VNil = v

instance VAppend N0 n n
  where
  vappend VNil v = v

-- instance VAppend n m r => VAppend n ('S m) ('S r)
--   where
--   vappend v1 (VCons a v2) = VCons a $ vappend v1 v2

instance VAppend n m r => VAppend ('S n) m ('S r)
  where
  vappend (VCons a v1) v2 = VCons a $ vappend v1 v2

-- Produce a feature matrix
class (N2 ^ n .== r) => Flags n r | n -> r
  where
  flags :: SNat n -> Vec r (Vec n Bool)

instance Flags n r => (Flags $ n) r
instance Function Flags

instance Flags N0 N1 
  where
  flags SZ = VNil `VCons` VNil

instance (Flags n r, VAppend r r r', (N2 × r) .== r') => Flags ('S n) r'
  where
  flags (SS n) =
    let
      rest = flags n
    in (VCons False <$> rest) `vappend` (VCons True <$> rest)

padToWidth :: Int -> String -> String
padToWidth i s
  | length s > i  = error "length of string to pad must be <= padded length"
  | otherwise = s <> replicate (i - length s) ' '

displayFlag :: Bool -> String
displayFlag False = " "
displayFlag True = "✔" 

delimit :: Foldable f => f String -> String
delimit cs = "| " <> intercalate " | " (toList cs) <> " |"

separator :: Vec n String -> String
separator cols = "-" <> foldMap (\s -> replicate (length s + 3) '-') cols

flagTable :: (Flags n r, Applicative (Vec n)) => Vec n String -> [String]
flagTable columns =
  let
    ncols = vlength columns
    widths = length <$> columns
    header = delimit columns
    rows = toList $ fmap delimit $ fmap (liftA2 padToWidth widths) $ (fmap . fmap) displayFlag $ flags ncols
  in
    intersperse (separator columns) $ header : rows

-- Tests
message :: String
message = unlines $ flagTable $ VCons "foo" $ VCons "bar" $ VCons "baz" $ VNil
