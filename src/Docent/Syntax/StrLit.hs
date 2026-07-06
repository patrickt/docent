{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Docent.Syntax.StrLit
  ( StrF (..)
  , eString
  , concat_
  ) where

import Data.Text (Text)

import Docent.Sum
import Docent.Type
import Docent.Algebra

data StrF t a
  = EString Text
  | Concat (t a) (t a)

instance HBind StrF where
  hbind _ (EString s)  = EString s
  hbind k (Concat a b) = Concat (a >>= k) (b >>= k)

instance TypeableF StrF where
  tcAlg _   (EString _)  = Right TString
  tcAlg ctx (Concat a b) = do
    ta <- typecheck ctx a
    tb <- typecheck ctx b
    case (ta, tb) of
      (TString, TString) -> Right TString
      (TString, other)   -> Left (TypeError TString other)
      (other, _)         -> Left (TypeError TString other)

instance EqAlg StrF where
  eqAlg (EString a)  (EString b)  = a == b
  eqAlg (Concat a b) (Concat c d) = eqTerm a c && eqTerm b d
  eqAlg _            _            = False

eString :: (StrF :<: s) => Text -> Term s a
eString s = inject (EString s)

concat_ :: (StrF :<: s) => Term s a -> Term s a -> Term s a
concat_ a b = inject (Concat a b)

instance TextShowAlg StrF where
  textShowAlg _   (EString s)  = "\"" <> s <> "\""
  textShowAlg sup (Concat a b) = textShow sup a <> " + " <> textShow sup b
