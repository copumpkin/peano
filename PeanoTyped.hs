{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, EmptyDataDecls, ImplicitParams, GeneralizedNewtypeDeriving, 
             TypeOperators, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, OverlappingInstances, 
             UndecidableInstances, StandaloneDeriving, RebindableSyntax, PatternGuards #-}
module PeanoTyped where

import qualified Prelude
import Prelude (Show, Maybe(..), Integer, id, (.), Bool(..), undefined, (>>=), (>>), fail, error, const)

import Structures


infix 4 :==
infixl 6 :+
infixl 7 :*

-- Unnecessary but makes things simpler
type family IsZero n :: *
type instance IsZero Z = Zero
type instance IsZero (S n) = Nonzero

data Zero
data Nonzero
data Variable
data MVariable


-- The two theories we know about, and which is harder
data Presburger
data Peano

type family Difficulty a :: *
type instance Difficulty Zero = Presburger
type instance Difficulty Nonzero = Presburger
type instance Difficulty Variable = Presburger
type instance Difficulty MVariable = Peano

-- Whether a given Presburger relation is normalized or not
data Normal
data Unnormal

-- "Difficulty" semilattices
type family Harder a b :: *
type instance Harder Presburger Presburger = Presburger
type instance Harder Presburger Peano = Peano
type instance Harder Peano Presburger = Peano
type instance Harder Peano Peano = Peano

type family Plus n m :: *
type instance Plus Zero Zero = Zero
type instance Plus Zero Nonzero = Nonzero
type instance Plus Zero Variable = Variable
type instance Plus Zero MVariable = MVariable
type instance Plus Nonzero Zero = Nonzero
type instance Plus Nonzero Nonzero = Nonzero
type instance Plus Nonzero Variable = Variable
type instance Plus Nonzero MVariable = MVariable
type instance Plus Variable Zero = Variable
type instance Plus Variable Nonzero = Variable
type instance Plus Variable Variable = Variable
type instance Plus Variable MVariable = MVariable
type instance Plus MVariable Zero = MVariable
type instance Plus MVariable Nonzero = MVariable
type instance Plus MVariable Variable = MVariable
type instance Plus MVariable MVariable = MVariable

type family Times n m :: *
type instance Times Zero Zero = Zero
type instance Times Zero Nonzero = Zero
type instance Times Zero Variable = Zero
type instance Times Zero MVariable = Zero
type instance Times Nonzero Zero = Zero
type instance Times Nonzero Nonzero = Nonzero
type instance Times Nonzero Variable = Variable
type instance Times Nonzero MVariable = MVariable
type instance Times Variable Zero = Zero
type instance Times Variable Nonzero = Variable
type instance Times Variable Variable = MVariable
type instance Times Variable MVariable = MVariable
type instance Times MVariable Zero = Zero
type instance Times MVariable Nonzero = MVariable
type instance Times MVariable Variable = MVariable
type instance Times MVariable MVariable = MVariable

type Relation a b = Harder (Difficulty a) (Difficulty b)


data Expr t n where
  Var  :: Fin n -> Expr Variable n
  Con  :: Nat q -> Expr (IsZero q) n
  (:+) :: Expr t n -> Expr t' n -> Expr (Plus t t') n
  (:*) :: Expr t n -> Expr t' n -> Expr (Times t t')  n

deriving instance Show (Expr t n)

data Rel t n where
  (:==)  :: Expr t n -> Expr t' n -> Rel (Relation t t') n
  (:<)   :: Expr t n -> Expr t' n -> Rel (Relation t t') n
  (:<=)  :: Expr t n -> Expr t' n -> Rel (Relation t t') n
  (:>=)  :: Expr t n -> Expr t' n -> Rel (Relation t t') n
  (:>)   :: Expr t n -> Expr t' n -> Rel (Relation t t') n
  
  (:&&)  :: Rel t n -> Rel t' n -> Rel (Harder t t') n
  (:||)  :: Rel t n -> Rel t' n -> Rel (Harder t t') n
  (:==>) :: Rel t n -> Rel t' n -> Rel (Harder t t') n
  Xor    :: Rel t n -> Rel t' n -> Rel (Harder t t') n
  
  (:|)   :: Nat (S x) -> Expr t n -> Rel t n

  Not    :: Rel t n -> Rel t n  
  Exists :: Rel t (S n) -> Rel t n
  Forall :: Rel t (S n) -> Rel t n

deriving instance Show (Rel q n)



cough :: (Fin (S n) -> Rel t n) -> Rel t n
cough f = f Fz

binder :: (Rel t (S m) -> Rel t m) -> ((forall n. (S m :<= n) => Expr Variable n) -> Rel t (S m)) -> Rel t m
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



cooper :: Rel Presburger Z -> Bool
cooper (x :== y)  = undefined
cooper (x :<  y)  = undefined
cooper (x :&& y)  = undefined
cooper (x :|| y)  = undefined
cooper (x :|  y)  = undefined
cooper (Not    x) = undefined
cooper (Exists q) = undefined
cooper (Forall q) = undefined


data TheoryWitness t where
  Presburger :: TheoryWitness Presburger
  Peano      :: TheoryWitness Peano

class Theory t where
  witness :: TheoryWitness t

instance Theory Presburger where
  witness = Presburger
  
instance Theory Peano where
  witness = Peano
  
theory :: Theory t => Rel t Z -> TheoryWitness t
theory = const witness

prove :: Theory m => Rel m Z -> Maybe Bool
prove r | Presburger <- theory r = Just (cooper r)
prove r = Nothing


plusComm  = forall2 (\x y -> x :+ y :== y :+ x)
timesComm = forall2 (\x y -> x :* y :== y :* x)


plusAssoc  = forall3 (\x y z -> x :+ (y :+ z) :== (x :+ y) :+ z)
timesAssoc = forall3 (\x y z -> x :* (y :* z) :== (x :* y) :* z)

plusLeftIdentity     = forall (\x -> Con Zero :+ x :== x)
timesLeftIdentity    = forall (\x -> Con (Suc 0) :* x :== x)
timesLeftAnnihilator = forall (\x -> Con Zero :* x :== Con Zero)

plusTimesDistrib = forall3 (\x y z -> x :* (y :+ z) :== x :* y :+ x :* z)
  
