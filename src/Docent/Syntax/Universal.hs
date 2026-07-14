{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Docent.Syntax.Universal
  ( UniF (..),
    _TyLam,
    _TyApp,
    tyLam,
    tyApp,
  )
where

import Bound
import Docent.Algebra
import Docent.FreeVars
import Docent.Ident (Ident)
import Docent.Sum
import Docent.Type
import Docent.Typecheck
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as P
import Optics (makePrisms)

data UniF t a
  = TyLam Ident (t a) -- Λα. e; α is a named type variable scoping over e's annotations
  | TyApp (t a) (Ty Ident) -- e [σ]

makePrisms ''UniF

instance HBind UniF where
  hbind k (TyLam n e) = TyLam n (e >>= k)
  hbind k (TyApp e ty) = TyApp (e >>= k) ty

instance TypeableF UniF where
  tcAlg ctx (TyLam name body) = do
    sk <- freshTyVar name
    tb <- withTyVar name sk (typecheck ctx body)
    pure (forall_ sk tb)
  tcAlg ctx (TyApp e sigma) = do
    sigma' <- resolve sigma
    given <- typecheck ctx e
    body <- assertType _TForall (TForall (toScope TVoid)) given
    pure (instantiate1 sigma' body)

instance EqAlg UniF where
  eqAlg (TyLam n e) (TyLam n' e') = n == n' && eqTerm e e'
  eqAlg (TyApp e ty) (TyApp e' ty') = eqTerm e e' && ty == ty'
  eqAlg _ _ = False

instance PrettyAlg UniF where
  prettyAlg sup (TyLam n e) = "Λ" <> pretty n <> "." <+> prettyTerm sup e
  prettyAlg sup (TyApp e ty) = prettyTerm sup e <+> P.brackets (prettyTy sup ty)

instance FreeVarsAlg UniF where
  freeVarsAlg (TyLam _ e) = freeVars e
  freeVarsAlg (TyApp e _ty) = freeVars e

tyLam :: (UniF :<: s) => Ident -> Term s a -> Term s a
tyLam n e = inject (TyLam n e)

tyApp :: (UniF :<: s) => Term s a -> Ty Ident -> Term s a
tyApp e ty = inject (TyApp e ty)
