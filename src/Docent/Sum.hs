{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitNamespaces #-}
module Docent.Sum
  ( type (:+:) (..)
  , Term (..)
  , var
  , type (:<:) (..)
  , inject
  , HBind (..)
  ) where

import Data.Kind (Type)

infixr 6 :+:

type (:+:) :: ((Type -> Type) -> Type -> Type)
          -> ((Type -> Type) -> Type -> Type)
          -> (Type -> Type) -> Type -> Type
data (f :+: g) t a = InL (f t a) | InR (g t a)

type Term :: ((Type -> Type) -> Type -> Type) -> Type -> Type
data Term f a = Var a | In (f (Term f) a)

var :: a -> Term s a
var = Var

class f :<: g where
  inj :: f t a -> g t a
  prj :: g t a -> Maybe (f t a)

instance {-# OVERLAPPING #-} f :<: f where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-} f :<: (f :+: g) where
  inj = InL
  prj (InL x) = Just x
  prj (InR _) = Nothing

instance (f :<: g) => f :<: (h :+: g) where
  inj = InR . inj
  prj (InR x) = prj x
  prj (InL _) = Nothing

inject :: (f :<: s) => f (Term s) a -> Term s a
inject = In . inj

class HBind f where
  hbind :: HBind s => (a -> Term s b) -> f (Term s) a -> f (Term s) b

instance (HBind f, HBind g) => HBind (f :+: g) where
  hbind k (InL x) = InL (hbind k x)
  hbind k (InR y) = InR (hbind k y)

instance HBind s => Functor (Term s) where
  fmap f m = m >>= (Var . f)

instance HBind s => Applicative (Term s) where
  pure = Var
  mf <*> mx = mf >>= \f -> fmap f mx

instance HBind s => Monad (Term s) where
  Var a >>= k = k a
  In t  >>= k = In (hbind k t)
  {-# NOINLINE (>>=) #-}
