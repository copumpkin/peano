{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, EmptyDataDecls, ImplicitParams, GeneralizedNewtypeDeriving, 
             TypeOperators, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, OverlappingInstances, 
             UndecidableInstances, StandaloneDeriving, RebindableSyntax #-}
module Structures where

import qualified Prelude
import Prelude (Show, Maybe(..), Integer, id, (.), Bool(..), undefined, otherwise, (>>=), (>>), fail)

infix 4 ==
infixl 6 +
infixl 7 *
infixr 3 &&
infixr 2 ||
infix 1 ==>
infix 4 <
infix 4 <=
infix 4 >=
infix 4 >


newtype Natural = Natural Integer
  deriving (Show)

class Literal n where
  fromInteger :: Integer -> n

instance Literal Integer where
  fromInteger = id

instance Literal Natural where
  fromInteger = Natural

type family Truth n :: *
type instance Truth Natural = Bool
type instance Truth Integer = Bool

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

instance Eq Integer where
  x == y = x Prelude.== y

instance Eq Natural where
  Natural x == Natural y = x Prelude.== y


class Eq n => Ord n where
  (<)  :: n -> n -> Truth n
  (<=) :: n -> n -> Truth n
  (>=) :: n -> n -> Truth n
  (>)  :: n -> n -> Truth n

  x <= y = x < y || x == y
  x >= y = y < x || x == y
  x > y = y < x

instance Ord Integer where
  (<) = (Prelude.<)

instance Ord Natural where
  Natural x < Natural y = x Prelude.<  y



class Semiring n where
  zero :: n
  one  :: n
  (+)  :: n -> n -> n
  (*)  :: n -> n -> n

instance Semiring Natural where
  zero = 0
  one  = 1
  Natural x + Natural y = Natural (x Prelude.+ y)
  Natural x * Natural y = Natural (x Prelude.* y)



data Z = Z
newtype S n = S n

data Nat n where
  Zero :: Nat Z
  Suc  :: Natural -> Nat (S n)

withInteger :: (forall n. Nat n -> r) -> Integer -> Maybe r
withInteger f 0 = Just (f Zero)
withInteger f n | n > 0 = Just (f (Suc (Natural (n Prelude.- 1))))
                | otherwise = Nothing

withNatural :: (forall n. Nat n -> r) -> Natural -> r
withNatural f (Natural 0) = f Zero
withNatural f (Natural n) = f (Suc (Natural (n Prelude.- 1)))

withPositive :: (forall n. Maybe (Nat (S n)) -> r) -> Natural -> r
withPositive = undefined

deriving instance Show (Nat n)

data Fin n where
  Fz :: Fin (S n)
  Fs :: Fin n -> Fin (S n)

deriving instance Show (Fin n)

class (:<=) m n where
  finj :: Fin m -> Fin n

instance (:<=) n n where
  finj = id

instance (o ~ S n, m :<= n) => m :<= o where
  finj = Fs . finj