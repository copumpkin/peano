{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, EmptyDataDecls, ImplicitParams, GeneralizedNewtypeDeriving, 
             TypeOperators, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, OverlappingInstances, 
             UndecidableInstances, StandaloneDeriving, RebindableSyntax #-}
module Structures where

import qualified Prelude
import Prelude (Show, Maybe(..), Integer, id, (.), Bool(..), undefined)

infix 4 ==
infixl 6 +
infixl 7 *
infixr 3 &&
infixr 2 ||
infix 3 ==>


newtype Nat = Nat Integer
  deriving (Show)

class Literal n where
  fromInteger :: Integer -> n

instance Literal Nat where
  fromInteger = Nat

type family Truth n :: *
type instance Truth Nat = Bool

class BooleanAlgebra a where
  true  :: a
  false :: a
  not   :: a -> a
  (&&)  :: a -> a -> a
  (||)  :: a -> a -> a

(==>) :: BooleanAlgebra a => a -> a -> a
x ==> y = not x || y 

instance BooleanAlgebra Bool where
  true  = True
  false = False
  not   = Prelude.not
  (&&)  = (Prelude.&&)
  (||)  = (Prelude.||)


 
class (BooleanAlgebra (Truth n)) => Eq n where
  (==) :: n -> n -> Truth n
  (/=) :: n -> n -> Truth n
  
  x == y = not (x /= y)
  x /= y = not (x == y)

class Eq n => Ord n where
  (<)  :: n -> n -> Truth n
  (<=) :: n -> n -> Truth n
  (>=) :: n -> n -> Truth n
  (>)  :: n -> n -> Truth n

  x <= y = x < y || x == y
  x >= y = y < x || x == y
  x > y = y < x

instance Eq Nat where
  Nat x == Nat y = x Prelude.== y

instance Ord Nat where
  Nat x < Nat y = x Prelude.<  y

class Semiring n where
  type Multiply n :: *
  zero :: n
  one  :: n
  (+)  :: n -> n -> n
  (*)  :: n -> n -> Multiply n

instance Semiring Nat where
  type Multiply Nat = Nat
  zero = 0
  one  = 1
  Nat x + Nat y = Nat (x Prelude.+ y)
  Nat x * Nat y = Nat (x Prelude.* y)