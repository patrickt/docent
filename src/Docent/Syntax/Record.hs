{-# LANGUAGE OverloadedStrings #-}
module Docent.Syntax.Record
  ( RecF (..)
  , record_
  , project_
  ) where

import Data.Map.Ordered (OMap)
import Data.Map.Ordered qualified as Map
import Prettyprinter (Pretty (..), (<+>))
import Prettyprinter qualified as P

import Docent.Ident (Ident)
import Docent.Sum
import Docent.Type
import Docent.Typecheck
import Docent.Algebra
import GHC.Exts

data RecF t a
  = Record (OMap Ident (t a))
  | Project (t a) Ident

instance HBind RecF where
  hbind k (Record fields) = Record (fmap (>>= k) fields)
  hbind k (Project t a) = Project (t >>= k) a

instance TypeableF RecF where
  tcAlg ctx (Record fields) = do
    fs <- traverse (typecheck ctx) fields
    pure (TRecord fs)
  tcAlg ctx (Project t a) = do
    rec_ <- typecheck ctx t
    fields <- assertType _TRecord (TRecord Map.empty) rec_
    case Map.lookup a fields of
      Just ty -> pure ty
      Nothing -> typeError (TRecord Map.empty) rec_

instance EqAlg RecF where
  eqAlg (Record as) (Record bs) = do
    let aFields = Map.assocs as
    let bFields = Map.assocs bs
    let go (n, t) (n', t') = n == n' && eqTerm t t'
    length aFields == length bFields && all id (zipWith go aFields bFields)
  eqAlg (Project a f) (Project b g) = eqTerm a b && f == g
  eqAlg _ _ = False

record_ :: (IsList l, Item l ~ (Ident, Term s a), RecF :<: s) => l -> Term s a
record_ fields = inject (Record (Map.fromList (toList fields)))

project_ :: (RecF :<: s) => Term s a -> Ident -> Term s a
project_ t f = inject (Project t f)

instance PrettyAlg RecF where
  prettyAlg sup (Record fields) =
    P.braces (P.hsep (P.punctuate "," [pretty n <+> "=" <+> prettyTerm sup t | (n, t) <- Map.assocs fields]))
  prettyAlg sup (Project t f) = prettyTerm sup t <> "." <> pretty f
