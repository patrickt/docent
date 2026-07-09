{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Docent.Algebra
  ( TypeableF (..)
  , typecheck
  , EqAlg (..)
  , eqTerm
  , PrettyAlg (..)
  , prettyTerm
  , hasType
  ) where

import Data.Stream (Stream)
import Prettyprinter (Doc, Pretty (..))

import Docent.Ident (Ident)
import Docent.Sum
import Docent.Type

-- Typechecking ---------------------------------------------------------------

class TypeableF f where
  tcAlg :: (TypeableF s, HBind s)
        => (a -> Ty) -> f (Term s) a -> Either TypeError Ty

typecheck :: (TypeableF s, HBind s)
          => (a -> Ty) -> Term s a -> Either TypeError Ty
typecheck ctx (Var a) = Right (ctx a)
typecheck ctx (In t)  = tcAlg ctx t

instance (TypeableF f, TypeableF g) => TypeableF (f :+: g) where
  tcAlg ctx (InL x) = tcAlg ctx x
  tcAlg ctx (InR y) = tcAlg ctx y

-- Alpha-equivalence ----------------------------------------------------------

class EqAlg f where
  eqAlg :: (EqAlg s, HBind s, Eq a)
        => f (Term s) a -> f (Term s) a -> Bool

eqTerm :: (EqAlg s, HBind s, Eq a) => Term s a -> Term s a -> Bool
eqTerm (Var x) (Var y) = x == y
eqTerm (In s)  (In t)  = eqAlg s t
eqTerm _       _       = False

instance (EqAlg f, EqAlg g) => EqAlg (f :+: g) where
  eqAlg (InL a) (InL b) = eqAlg a b
  eqAlg (InR a) (InR b) = eqAlg a b
  eqAlg _       _       = False

-- Pretty-printing --------------------------------------------------------------

class PrettyAlg f where
  prettyAlg :: (PrettyAlg s, HBind s) => Stream Ident -> f (Term s) Ident -> Doc ann

prettyTerm :: (PrettyAlg s, HBind s) => Stream Ident -> Term s Ident -> Doc ann
prettyTerm _   (Var x) = pretty x
prettyTerm sup (In t)  = prettyAlg sup t

instance (PrettyAlg f, PrettyAlg g) => PrettyAlg (f :+: g) where
  prettyAlg sup (InL x) = prettyAlg sup x
  prettyAlg sup (InR y) = prettyAlg sup y
