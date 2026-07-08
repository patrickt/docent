{-# LANGUAGE OverloadedStrings #-}
module Docent.Syntax.Record
  ( RecF (..)
  , record
  , project
  ) where

import Data.Foldable hiding (toList)
import Data.Text qualified as T
import Data.Map.Ordered (OMap)
import Data.Map.Ordered qualified as Map

import Docent.Ident (Ident)
import Docent.Ident qualified as Ident
import Docent.Sum
import Docent.Type
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
    Right (TRecord fs)
  tcAlg ctx (Project t a) = do
    rec_ <- typecheck ctx t
    case rec_ of
      TRecord fields | Just ty <- Map.lookup a fields -> Right ty
      other -> Left (TypeError (TRecord Map.empty) other)

instance EqAlg RecF where
  eqAlg (Record as) (Record bs) = do
    let aFields = Map.assocs as
    let bFields = Map.assocs bs
    let go (n, t) (n', t') = n == n' && eqTerm t t'
    all id (zipWith go aFields bFields)
  eqAlg (Project a f) (Project b g) = eqTerm a b && f == g
  eqAlg _ _ = False

record :: (IsList l, Item l ~ (Ident, Term s a), RecF :<: s) => l -> Term s a
record fields = inject (Record (Map.fromList (toList fields)))

project :: (RecF :<: s) => Term s a -> Ident -> Term s a
project t f = inject (Project t f)

instance TextShowAlg RecF where
  textShowAlg sup (Record fields) =
    "{" <> T.intercalate ", " [Ident.toText n <> " = " <> textShow sup t | (n, t) <- Map.assocs fields] <> "}"
  textShowAlg sup (Project t f) = textShow sup t <> "." <> Ident.toText f
