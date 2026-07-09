{-# LANGUAGE OverloadedStrings #-}
module Docent.Syntax.Fixpoint
  ( FixF (..)
  , fix_
  ) where

import Bound
import Docent.Type
import Data.Stream (Stream(..))
import Docent.Algebra
import Docent.Sum
import Prettyprinter qualified as P
import Prettyprinter ((<+>))
import Bound.Var

data FixF t a = Fix Ty (Scope () t a)

instance PrettyAlg FixF where
  prettyAlg (Cons n rest) (Fix ty body) =
    "fix" <+> P.parens (hasType n ty) <> "." <+> prettyTerm rest (instantiate1 (var n) body)

instance HBind FixF where
  hbind k (Fix ty expr) = Fix ty (expr >>>= k)

instance EqAlg FixF where
  eqAlg (Fix ty bod) (Fix ty' bod') = ty == ty' && eqTerm (fromScope bod) (fromScope bod')

instance TypeableF FixF where
  tcAlg ctx (Fix ty bod) = do
    tb <- typecheck (unvar (const ty) ctx) (fromScope bod)
    if ty == tb
      then Right ty
      else Left (TypeError ty tb)

fix_ :: (FixF :<: s, HBind s, Eq a) => a -> Ty -> Term s a -> Term s a
fix_ x ty body = inject (Fix ty (abstract1 x body))
