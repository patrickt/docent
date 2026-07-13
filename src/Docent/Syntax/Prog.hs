{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Docent.Syntax.Prog
  ( LamF (..)
  , lam
  , app
  , let_
  ) where

import Bound
import Bound.Var (unvar)
import Data.Stream (Stream (..))
import Prettyprinter (Pretty (..), (<+>))
import Prettyprinter qualified as P

import Docent.Ident (Ident)
import Docent.Sum
import Docent.Type
import Docent.Algebra
import Docent.Typecheck

data LamF t a
  = Lam (Ty Ident) (Scope () t a)
  | App (t a) (t a)
  | Let (t a) (Scope () t a)

instance PrettyAlg LamF where
  prettyAlg (Cons n rest) (Lam ty b) =
    "fun" <+> P.parens (pretty n <+> ":" <+> prettyTy rest ty) <> "." <+> P.nest 2 (prettyTerm rest (instantiate1 (var n) b))
  prettyAlg sup (App f x) = prettyTerm sup f <+> prettyTerm sup x
  prettyAlg (Cons n rest) (Let e b) =
    "let" <+> pretty n <+> "=" <+> prettyTerm rest e <+> "in" <+> P.nest 2 (prettyTerm rest (instantiate1 (var n) b))

instance HBind LamF where
  hbind k (Lam ty b) = Lam ty (b >>>= k)
  hbind k (App f x)  = App (f >>= k) (x >>= k)
  hbind k (Let e b)  = Let (e >>= k) (b >>>= k)

instance TypeableF LamF where
  tcAlg ctx (App f x) = do
    tf <- typecheck ctx f
    tx <- typecheck ctx x
    (arg, res) <- assertType _TFun (TFun TString TString) tf
    if arg == tx
      then pure res
      else typeError arg tx
  tcAlg ctx (Lam ty b) = do
    ty' <- resolve ty
    tb <- typecheck (unvar (const ty') ctx) (fromScope b)
    pure (TFun ty' tb)
  tcAlg ctx (Let e b) = do
    te <- typecheck ctx e
    typecheck (unvar (const te) ctx) (fromScope b)

instance EqAlg LamF where
  eqAlg (Lam t1 b1) (Lam t2 b2) = t1 == t2 && eqTerm (fromScope b1) (fromScope b2)
  eqAlg (App f x)   (App g y)   = eqTerm f g && eqTerm x y
  eqAlg (Let e1 b1) (Let e2 b2) = eqTerm e1 e2 && eqTerm (fromScope b1) (fromScope b2)
  eqAlg _           _           = False

lam :: (LamF :<: s, HBind s, Eq a) => a -> Ty Ident -> Term s a -> Term s a
lam x ty body = inject (Lam ty (abstract1 x body))

app :: (LamF :<: s) => Term s a -> Term s a -> Term s a
app f x = inject (App f x)

let_ :: (LamF :<: s, HBind s, Eq a) => a -> Term s a -> Term s a -> Term s a
let_ x e body = inject (Let e (abstract1 x body))
