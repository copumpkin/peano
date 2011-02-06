{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, EmptyDataDecls, ImplicitParams, GeneralizedNewtypeDeriving, 
             TypeOperators, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, OverlappingInstances, 
             UndecidableInstances, StandaloneDeriving, RebindableSyntax, PatternGuards #-}
module Peano where

import qualified Prelude
import Prelude (Show, Maybe(..), Integer, id, (.), Bool(..), undefined, (>>=), (>>), fail, error, fmap)

import Structures
import qualified PeanoTyped as T

import Control.Applicative

data Expr n where
  Var  :: Fin n -> Expr n
  Con  :: Natural -> Expr n
  (:+) :: Expr n -> Expr n -> Expr n
  (:*) :: Expr n -> Expr n -> Expr n

typedExpr :: (forall t. T.Expr t n -> r) -> Expr n -> r
typedExpr f (Var n) = f (T.Var n)
typedExpr f (Con n) = withNatural (f . T.Con) n
typedExpr f (x :+ y) = typedExpr (\x -> typedExpr (\y -> f (x T.:+ y)) y) x
typedExpr f (x :* y) = typedExpr (\x -> typedExpr (\y -> f (x T.:* y)) y) x


deriving instance Show (Expr n)

data Rel n where
  Top    :: Rel n
  Bottom :: Rel n
  
  (:==)  :: Expr n -> Expr n -> Rel n
  (:<)   :: Expr n -> Expr n -> Rel n
  
  (:&&)  :: Rel n -> Rel n -> Rel n
  (:||)  :: Rel n -> Rel n -> Rel n
  (:|)   :: Natural -> Expr n -> Rel n

  Not    :: Rel n -> Rel n  
  Exists :: Rel (S n) -> Rel n
  Forall :: Rel (S n) -> Rel n

deriving instance Show (Rel n)

typedRel :: (forall t. Maybe (T.Rel t n) -> r) -> Rel n -> r
typedRel f (x :== y)  = typedExpr    (\x -> typedExpr (\y -> f (pure (x T.:== y))) y) x
typedRel f (x :<  y)  = typedExpr    (\x -> typedExpr (\y -> f (pure (x T.:<  y))) y) x
typedRel f (x :&& y)  = typedRel     (\x -> typedRel  (\y -> f (liftA2 (T.:&&) x y)) y) x
typedRel f (x :|| y)  = typedRel     (\x -> typedRel  (\y -> f (liftA2 (T.:||) x y)) y) x
typedRel f (x :|  y)  = withPositive (\x -> typedExpr (\y -> f (fmap (T.:| y) x)) y) x
typedRel f (Not x)    = typedRel (f . fmap T.Not) x
typedRel f (Exists x) = typedRel (f . fmap T.Exists) x
typedRel f (Forall x) = typedRel (f . fmap T.Forall) x

instance Literal (Expr n) where
  fromInteger = Con . fromInteger

instance Semiring (Expr n) where
  zero = 0
  one  = 1
  (+)  = (:+)
  (*)  = (:*)

type instance Truth (Expr n) = Rel n

instance BooleanAlgebra (Rel n) where
  true  = Top
  false = Bottom
  
  (&&) = (:&&)
  (||) = (:||)
  not  = Not

instance Eq (Expr n) where
  (==) = (:==)

instance Ord (Expr n) where
  (<) = (:<)
  x <= y = x :< (y + 1)
  x >= y = y :< (x + 1)
  x > y = y < x


cough :: (Fin (S n) -> Rel n) -> Rel n
cough f = f Fz

binder :: (Rel (S m) -> Rel m) -> ((forall n. (S m :<= n) => Expr n) -> Rel (S m)) -> Rel m
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








-- Basic algebraic properties
plusComm  = forall2 (\x y -> x + y == y + x)
timesComm = forall2 (\x y -> x * y == y * x)

plusAssoc  = forall3 (\x y z -> x + (y + z) == (x + y) + z)
timesAssoc = forall3 (\x y z -> x * (y * z) == (x * y) * z)

plusLeftIdentity     = forall (\x -> 0 + x == x)
timesLeftIdentity    = forall (\x -> 1 * x == x)
timesLeftAnnihilator = forall (\x -> 0 * x == 0)

plusTimesDistrib = forall3 (\x y z -> x * (y + z) == x * y + x * z)
  
-- Order properties
lteRefl    = forall  (\x -> x <= x)
lteTrans   = forall3 (\x y z -> x <= y && y <= z ==> x <= z)
lteTotal   = forall2 (\x y -> x <= y || y <= x)
lteAntisym = forall2 (\x y -> x <= y && y <= x ==> x == y)


ltNotRefl = forall  (\x -> not (x < x))
ltTrans   = forall3 (\x y z -> x < y && y < z ==> x < z)
lt        = forall2 (\x y -> not (x < y && y < x))

-- Hybrid properties
timesPositive = forall2 (\x y -> x > 0 && y > 0 ==> x * y > 0)
timesZero     = forall2 (\x y -> x * y == 0 ==> x == 0 || y == 0)

{-
-- <Saizan> pumpkin: i mean that in forall (\x y -> ..) x and y could be of type Var n where newtype Var n = Var (forall m. Leq (S n) m => Expr m), so you can't use them directly as Expr's
-}