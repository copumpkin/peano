{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, EmptyDataDecls, ImplicitParams, GeneralizedNewtypeDeriving, 
             TypeOperators, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, OverlappingInstances, 
             UndecidableInstances, StandaloneDeriving, RebindableSyntax #-}
module PeanoTyped where

import qualified Prelude
import Prelude (Show, Maybe(..), Integer, id, (.), Bool(..), undefined)

import Structures


infix 4 :==
infixl 6 :+
infixl 7 :*



data Zero
data Multiplicative

data Z = Z
newtype S n = S n

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


data Expr m n where
  Var  :: Fin n -> Expr m n
  Con  :: Nat -> Expr m n
  (:+) :: Expr m n -> Expr m n -> Expr m n
  (:*) :: Expr m n -> Expr m n -> Expr Multiplicative n

deriving instance Show (Expr m n)

instance Literal (Expr m n) where
  fromInteger = Con . Nat

instance Semiring (Expr m n) where
  type Multiply (Expr m n) = Expr Multiplicative n
  zero = Con zero
  one  = Con one
  (+)  = (:+)
  (*)  = (:*)

data Rel m n where
  (:==)  :: Expr m n -> Expr m n -> Rel m n
  (:<)   :: Expr m n -> Expr m n -> Rel m n
  
  (:&&)  :: Rel m n -> Rel m n -> Rel m n
  (:||)  :: Rel m n -> Rel m n -> Rel m n
  Not    :: Rel m n -> Rel m n
  (:|)   :: Nat -> Expr m n -> Rel m n
  
  Exists :: Rel m (S n) -> Rel m n
  Forall :: Rel m (S n) -> Rel m n

deriving instance Show (Rel m n)

type instance Truth (Expr m n) = Rel m n

instance BooleanAlgebra (Rel m n) where
  -- I should probably just make primitive constructors here...
  true  = exists (\x -> x == 0)
  false = forall (\x -> x == 0)
  
  (&&) = (:&&)
  (||) = (:||)
  not  = Not

instance Eq (Expr m n) where
  (==) = (:==)

instance Ord (Expr m n) where
  (<) = (:<)
  x <= y = x :< (y + 1)
  x >= y = y :< (x + 1)
  x > y = y < x


cough :: (Fin (S n) -> Rel q n) -> Rel q n
cough f = f Fz

binder :: (Rel q (S m) -> Rel q m) -> ((forall n. (S m :<= n) => Expr q n) -> Rel q (S m)) -> Rel q m
binder b p = cough (\fz -> b (p (Var (finj fz))))

forall = binder Forall
forall2 p = forall (\x -> forall (\y -> p x y))
forall3 p = forall (\x -> forall2 (\y z -> p x y z))
forall4 p = forall (\x -> forall3 (\y z a -> p x y z a))
forall5 p = forall (\x -> forall4 (\y z a b -> p x y z a b))

exists = binder Exists
exists2 p = exists (\x -> exists (\y -> p x y))
exists3 p = exists (\x -> exists2 (\y z -> p x y z))
exists4 p = exists (\x -> exists3 (\y z a -> p x y z a))
exists5 p = exists (\x -> exists4 (\y z a b -> p x y z a b))



presburger :: Rel () Z -> Bool
presburger = undefined

prove :: Rel m Z -> Maybe Bool
prove = undefined


-- TODO: figure out how to make multiplication by a constant presburger-possible, but not multiplication by a variable


plusComm  = forall2 (\x y -> x + y == y + x)
timesComm = forall2 (\x y -> x * y == y * x)

plusAssoc  = forall3 (\x y z -> x + (y :+ z) == (x + y) + z)
timesAssoc = forall3 (\x y z -> x * (y :* z) == (x * y) * z)

plusLeftIdentity     = forall (\x -> 0 + x == x)
timesLeftIdentity    = forall (\x -> 1 * x == x)
timesLeftAnnihilator = forall (\x -> 0 * x == 0)

plusTimesDistrib = forall3 (\x y z -> x * (y + z) == x * y + x * z)

presburger1 = not (exists (\x -> 0 == x + 1))
presburger2 = forall2 (\x y -> x + 1 == y + 1 ==> x == y)
presburger3 = forall (\x -> x + 0 == x)
presburger4 = forall2 (\x y -> (x + y) + 1 == x + (y + 1))
  
zeroInitial = forall (\x -> 0 <= x)