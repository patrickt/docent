module Docent.Typecheck
  ( TypeableF (..),
    TypeError (..),
    Checking,
    TyEnv (..),
    runTypecheck,
    typecheck,
    typeError,
    resolve,
    freshTyVar,
    withTyVar,
  )
where

import Control.Carrier.Error.Either
import Control.Carrier.Fresh.Strict
import Control.Carrier.Reader
import Docent.Ident
import Docent.Sum
import Docent.Type
import Data.Map (Map)
import Data.Map.Strict qualified as Map

-- Maps source-syntax type-variable names to the skolems currently standing in
-- for them. Unbound names resolve to themselves (TVar). Every annotation
-- coming out of the syntax must go through 'resolve' before use; types
-- produced by 'typecheck' are already resolved.
newtype TyEnv = TyEnv (Map Ident (Ty Ident))

type Checking sig m = (Has (Error TypeError) sig m, Has Fresh sig m, Has (Reader TyEnv) sig m)

class TypeableF f where
  tcAlg ::
    (TypeableF s, HBind s, Checking sig m) =>
    (a -> Ty Ident) -> f (Term s) a -> m (Ty Ident)

typecheck ::
  (TypeableF s, HBind s, Checking sig m) =>
  (a -> Ty Ident) -> Term s a -> m (Ty Ident)
typecheck ctx (Var a) = pure (ctx a)
typecheck ctx (In t) = tcAlg ctx t

runTypecheck ::
  (TypeableF s, HBind s) =>
  (a -> Ty Ident) -> Term s a -> Either TypeError (Ty Ident)
runTypecheck ctx = run . runError . evalFresh 0 . runReader (TyEnv Map.empty) . typecheck ctx

instance (TypeableF f, TypeableF g) => TypeableF (f :+: g) where
  tcAlg ctx (InL x) = tcAlg ctx x
  tcAlg ctx (InR y) = tcAlg ctx y

typeError :: (Has (Error TypeError) sig m) => Ty Ident -> Ty Ident -> m a
typeError a b = throwError (TypeError a b)

resolve :: (Has (Reader TyEnv) sig m) => Ty Ident -> m (Ty Ident)
resolve ty = do
  TyEnv env <- ask
  pure (ty >>= \v -> Map.findWithDefault (TVar v) v env)

freshTyVar :: (Has Fresh sig m) => Ident -> m Ident
freshTyVar base = gensym base <$> fresh

withTyVar :: (Has (Reader TyEnv) sig m) => Ident -> Ident -> m x -> m x
withTyVar name sk = local (\(TyEnv env) -> TyEnv (Map.insert name (TVar sk) env))
