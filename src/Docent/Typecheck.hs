module Docent.Typecheck
  ( TypeableF (..),
    TypeError (..),
    runTypecheck,
    typecheck,
    typeError,
  )
where

import Control.Carrier.Error.Either
import Docent.Ident
import Docent.Sum
import Docent.Type

class TypeableF f where
  tcAlg ::
    (TypeableF s, HBind s, Has (Error TypeError) sig m) =>
    (a -> Ty Ident) -> f (Term s) a -> m (Ty Ident)

typecheck ::
  (TypeableF s, HBind s, Has (Error TypeError) sig m) =>
  (a -> Ty Ident) -> Term s a -> m (Ty Ident)
typecheck ctx (Var a) = pure (ctx a)
typecheck ctx (In t) = tcAlg ctx t

runTypecheck ::
  (TypeableF s, HBind s) =>
  (a -> Ty Ident) -> Term s a -> Either TypeError (Ty Ident)
runTypecheck = typecheck

instance (TypeableF f, TypeableF g) => TypeableF (f :+: g) where
  tcAlg ctx (InL x) = tcAlg ctx x
  tcAlg ctx (InR y) = tcAlg ctx y

typeError :: (Has (Error TypeError) sig m) => Ty Ident -> Ty Ident -> m a
typeError a b = throwError (TypeError a b)
