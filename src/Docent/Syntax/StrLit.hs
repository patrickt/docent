{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Docent.Syntax.StrLit
  ( StrF (..)
  , _EString
  , _Concat
  , eString
  , concat_
  ) where

import Data.Text (Text)
import Prettyprinter (Pretty (..), (<+>))
import Prettyprinter qualified as P

import Docent.Sum
import Docent.Type
import Docent.Algebra
import Docent.Typecheck
import Docent.FreeVars
import Optics (makePrisms)

data StrF t a
  = EString Text
  | Concat (t a) (t a)

makePrisms ''StrF

instance HBind StrF where
  hbind _ (EString s)  = EString s
  hbind k (Concat a b) = Concat (a >>= k) (b >>= k)

instance TypeableF StrF where
  tcAlg _   (EString _)  = pure TString
  tcAlg ctx (Concat a b) = do
    ta <- typecheck ctx a
    tb <- typecheck ctx b
    case (ta, tb) of
      (TString, TString) -> pure TString
      (TString, other)   -> typeError TString other
      (other, _)         -> typeError TString other

instance EqAlg StrF where
  eqAlg (EString a)  (EString b)  = a == b
  eqAlg (Concat a b) (Concat c d) = eqTerm a c && eqTerm b d
  eqAlg _            _            = False

instance FreeVarsAlg StrF where
  freeVarsAlg _ = mempty

eString :: (StrF :<: s) => Text -> Term s a
eString s = inject (EString s)

concat_ :: (StrF :<: s) => Term s a -> Term s a -> Term s a
concat_ a b = inject (Concat a b)

instance PrettyAlg StrF where
  prettyAlg _   (EString s)  = P.dquotes (pretty s)
  prettyAlg sup (Concat a b) = prettyTerm sup a <+> "+" <+> prettyTerm sup b
