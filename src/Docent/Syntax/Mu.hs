{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Docent.Syntax.Mu
  ( MuF (..),
    _Fold,
    _Unfold,
    fold_,
    unfold_,
  )
where

import Bound
import Docent.Algebra
import Docent.FreeVars
import Docent.Ident (Ident)
import Docent.Sum
import Docent.Type
import Docent.Typecheck
import Docent.Util
import Optics (makePrisms)
import Prettyprinter ((<+>))
import Prettyprinter qualified as P

-- fold [μα.τ] e rolls e : τ[α ↦ μα.τ] up into μα.τ; unfold unrolls it again.
-- this is like Fix/Unfix but works on the type-level to provide access to the
-- self-recursive part of a recursive data definition like `list`.
data MuF t a
  = Fold (Ty Ident) (t a)
  | Unfold (t a)

makePrisms ''MuF

instance HBind MuF where
  hbind k (Fold ty e) = Fold ty (e >>= k)
  hbind k (Unfold e) = Unfold (e >>= k)

instance TypeableF MuF where
  tcAlg ctx (Fold ty e) = do
    ty' <- resolve ty
    b <- assertType _TMu (TMu (toScope TVoid)) ty'
    given <- typecheck ctx e
    let expected = instantiate1 ty' b
    if given == expected
      then pure ty'
      else typeError expected given
  tcAlg ctx (Unfold e) = do
    te <- typecheck ctx e
    b <- assertType _TMu (TMu (toScope TVoid)) te
    pure (instantiate1 te b)

instance EqAlg MuF where
  eqAlg (Fold ty e) (Fold ty' e') = ty == ty' && eqTerm e e'
  eqAlg (Unfold e) (Unfold e') = eqTerm e e'
  eqAlg _ _ = False

instance PrettyAlg MuF where
  prettyAlg sup (Fold ty e) = "fold" <+> P.brackets (prettyTy sup ty) <+> prettyTerm sup e
  prettyAlg sup (Unfold e) = "unfold" <+> prettyTerm sup e

instance FreeVarsAlg MuF where
  freeVarsAlg (Fold _ v) = freeVars v
  freeVarsAlg (Unfold v) = freeVars v

instance FreeTyVarsAlg MuF where
  freeTyVarsAlg (Fold t body) = setFromList t <> freeTyVars body
  freeTyVarsAlg (Unfold body) = freeTyVars body

fold_ :: (MuF :<: s) => Ty Ident -> Term s a -> Term s a
fold_ ty e = inject (Fold ty e)

unfold_ :: (MuF :<: s) => Term s a -> Term s a
unfold_ e = inject (Unfold e)
