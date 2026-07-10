{-# LANGUAGE OverloadedStrings #-}
module Docent.Syntax.Mu
  ( MuF (..)
  , fold_
  , unfold_
  ) where

import Bound
import Prettyprinter ((<+>))
import Prettyprinter qualified as P

import Docent.Ident (Ident)
import Docent.Sum
import Docent.Type
import Docent.Algebra
import Docent.Typecheck

-- fold [μα.τ] e rolls e : τ[α ↦ μα.τ] up into μα.τ; unfold unrolls it again.
data MuF t a
  = Fold (Ty Ident) (t a)
  | Unfold (t a)

instance HBind MuF where
  hbind k (Fold ty e) = Fold ty (e >>= k)
  hbind k (Unfold e)  = Unfold (e >>= k)

instance TypeableF MuF where
  tcAlg ctx (Fold ty e) = do
    ty' <- resolve ty
    case ty' of
      TMu b -> do
        given <- typecheck ctx e
        let expected = instantiate1 ty' b
        if given == expected
          then pure ty'
          else typeError expected given
      other -> typeError (TMu (toScope TVoid)) other
  tcAlg ctx (Unfold e) = do
    te <- typecheck ctx e
    case te of
      TMu b -> pure (instantiate1 (TMu b) b)
      other -> typeError (TMu (toScope TVoid)) other

instance EqAlg MuF where
  eqAlg (Fold ty e) (Fold ty' e') = ty == ty' && eqTerm e e'
  eqAlg (Unfold e)  (Unfold e')   = eqTerm e e'
  eqAlg _ _ = False

instance PrettyAlg MuF where
  prettyAlg sup (Fold ty e) = "fold" <+> P.brackets (prettyTy sup ty) <+> prettyTerm sup e
  prettyAlg sup (Unfold e)  = "unfold" <+> prettyTerm sup e

fold_ :: (MuF :<: s) => Ty Ident -> Term s a -> Term s a
fold_ ty e = inject (Fold ty e)

unfold_ :: (MuF :<: s) => Term s a -> Term s a
unfold_ e = inject (Unfold e)
