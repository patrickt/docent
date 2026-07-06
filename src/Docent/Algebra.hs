{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Docent.Algebra
  ( TypeableF (..)
  , typecheck
  , EqAlg (..)
  , eqTerm
  , TextShowAlg (..)
  , textShow
  , textShowTy
  ) where

import Data.Text (Text)
import Data.Stream (Stream)

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

-- Text decomposition ------------------------------------------------------------

class TextShowAlg f where
  textShowAlg :: (TextShowAlg s, HBind s) => Stream Text -> f (Term s) Text -> Text

textShow :: (TextShowAlg s, HBind s) => Stream Text -> Term s Text -> Text
textShow _   (Var x) = x
textShow sup (In t)  = textShowAlg sup t

instance (TextShowAlg f, TextShowAlg g) => TextShowAlg (f :+: g) where
  textShowAlg sup (InL x) = textShowAlg sup x
  textShowAlg sup (InR y) = textShowAlg sup y

textShowTy :: Ty -> Text
textShowTy TString    = "string"
textShowTy (TFun a b) = "(" <> textShowTy a <> " -> " <> textShowTy b <> ")"
