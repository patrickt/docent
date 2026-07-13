{-# LANGUAGE OverloadedStrings #-}
module Docent.Syntax.Variant
  ( VntF (..)
  , Branch (..)
  , inject_
  , case_
  ) where

import Bound
import Bound.Var (unvar)
import Data.List (find)
import Data.Map.Ordered (OMap)
import Data.Map.Ordered qualified as OMap
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as P
import Control.Monad
import Data.Stream (Stream(..))

import Docent.Sum
import Docent.Type
import Docent.Algebra
import Docent.Typecheck
import Docent.Ident (Ident)

data VntF t a
  = Inject Ident (Ty Ident) (t a)
  | Case (t a) (OMap Ident (Scope () t a))

data Branch s a = Branch Ident a (Term s a)

instance HBind VntF where
  hbind k (Inject i ty term) = Inject i ty (term >>= k)
  hbind k (Case term cases) = Case (term >>= k) (fmap (>>>= k) cases)

instance PrettyAlg VntF where
  prettyAlg sup (Inject i ty term) = P.hsep ["inject", prettyTerm sup term,
                                             "at", pretty i,
                                             "as", prettyTy sup ty
                                            ]
  prettyAlg c@(Cons n rest) (Case term branches) = "case" <+> prettyTerm c term <+> P.braces (P.vsep body) where
    body = fmap (uncurry go) (OMap.assocs branches)
    go ident bod = pretty ident <> P.parens (pretty n) <+> "⇒" <+> prettyTerm rest (instantiate1 (var n) bod)

instance TypeableF VntF where
  tcAlg ctx (Inject ident ty expr) = do
    ty' <- resolve ty
    case ty' of
      TVariant fields | Just found <- OMap.lookup ident fields -> do
                          given <- typecheck ctx expr
                          if given == found
                            then pure ty'
                            else typeError found given
      other -> typeError other ty'

  tcAlg ctx (Case term branches) = do
    ty <- typecheck ctx term
    fields <- case ty of
      TVariant fields -> pure fields
      other -> typeError (TVariant OMap.empty) other
    when (OMap.size branches /= OMap.size fields) $
      typeError ty (TVariant OMap.empty)
    checked <- traverse
      (\(l, tl) -> case OMap.lookup l branches of
          Just b -> typecheck (unvar (const tl) ctx) (fromScope b)
          Nothing -> typeError ty (TVariant OMap.empty))
      (OMap.assocs fields)
    case checked of
      [] -> pure TVoid
      (t : ts) -> case find (/= t) ts of
        Just bad -> typeError t bad
        Nothing -> pure t

instance EqAlg VntF where
  eqAlg (Inject i t term) (Inject i' t' term') = i == i' && t == t' && eqTerm term term'
  eqAlg (Case t ms) (Case t' ms') = eqTerm t t' && sameSize && containsSameKeys && containsSameValues where
    sameSize = OMap.size ms == OMap.size ms'
    containsSameKeys = OMap.null (ms OMap.\\ ms')
    containsSameValues = all id (OMap.intersectionWith equal ms ms')
    equal _lab m m' = eqTerm (fromScope m) (fromScope m')
  eqAlg _ _ = False

inject_ :: (VntF :<: s) => Ident -> Ty Ident -> Term s a -> Term s a
inject_ i ty term = inject (Inject i ty term)

case_ :: (VntF :<: s, HBind s, Eq a) => Term s a -> [Branch s a] -> Term s a
case_ t cases = inject (Case t new)
  where new = OMap.fromList [(l, abstract1 x b) | Branch l x b <- cases ]
