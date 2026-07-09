{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Docent.Lang
  ( Sig,
    EvalError (..),
    eval,
    runEval,
    names,
    renderTop,
    module Docent.Sum,
    module Docent.Type,
    module Docent.Algebra,
    module Docent.Syntax.StrLit,
    module Docent.Syntax.Prog,
  )
where

import Bound (instantiate1)
import Control.Carrier.Error.Either
import Data.Map.Ordered qualified as OMap
import Data.Stream qualified as Stream
import Data.Text (Text)
import Data.Text qualified as T
import Docent.Algebra
import Docent.Ident (Ident)
import Docent.Ident qualified as Ident
import Docent.Optics (require)
import Docent.Optics qualified as O
import Docent.Sum
import Docent.Syntax.Fixpoint
import Docent.Syntax.Prog
import Docent.Syntax.Record
import Docent.Syntax.StrLit
import Docent.Syntax.Variant
import Docent.Type
import Prettyprinter (Pretty (..), defaultLayoutOptions, layoutPretty, (<+>))
import Prettyprinter.Render.Text (renderStrict)

type Sig = StrF :+: LamF :+: RecF :+: VntF :+: FixF

data EvalError
  = NonStringConcat
  | NonFunctionApplication
  | NonRecordProjection
  | MissingField Ident
  | NonVariantScrutinee
  | MissingBranch Ident
  | StuckTerm
  deriving (Eq, Show)

instance Pretty EvalError where
  pretty NonStringConcat = "concatenation of non-string values"
  pretty NonFunctionApplication = "application of a non-function"
  pretty NonRecordProjection = "projection from a non-record"
  pretty (MissingField f) = "record has no field" <+> pretty f
  pretty NonVariantScrutinee = "case scrutinee is not a variant"
  pretty (MissingBranch l) = "case has no branch for label" <+> pretty l
  pretty StuckTerm = "evaluation is stuck"

eval :: (Has (Error EvalError) sig m) => Term Sig a -> m (Term Sig a)
eval (Var a) = pure (Var a)
eval (In t)
  | Just (EString _) <- prj t = do
      pure (In t)
  | Just (Concat a b) <- prj t = do
      a' <- eval a >>= require O._EString NonStringConcat
      b' <- eval b >>= require O._EString NonStringConcat
      pure (eString (a' <> b'))
  | Just (Lam _ _) <- prj t = do
      pure (In t)
  | Just (App f x) <- prj t = do
      (_, b) <- eval f >>= require O._Lam NonFunctionApplication
      x' <- eval x
      eval (instantiate1 x' b)
  | Just (Let e b) <- prj t = do
      eval (instantiate1 e b)
  | Just (Record _) <- prj t = do
      pure (In t)
  | Just (Project rec_ f) <- prj t = do
      rs <- eval rec_ >>= require O._Record NonRecordProjection
      case Map.lookup f rs of
        Just field -> eval field
        Nothing -> throwError (MissingField f)
  | Just (Inject {}) <- prj t = pure (In t)
  | Just (Case val branches) <- prj t = do
      (lab, _ty, payload) <- eval val >>= require O._Inject NonVariantScrutinee
      case OMap.lookup lab branches of
        Just alt -> do
          payload' <- eval payload
          eval (instantiate1 payload' alt)
        Nothing -> throwError (MissingBranch lab)
  | Just (Fix _ty val) <- prj t = do
      eval (instantiate1 (In t) val)
  | otherwise = do
      throwError StuckTerm

runEval :: Term Sig a -> Either EvalError (Term Sig a)
runEval = run . runError . eval

names :: Stream.Stream Ident
names = Stream.unfold (\i -> (Ident.fromText (T.pack ("v" <> show (i :: Int))), succ i)) 0

renderTop :: Term Sig Ident -> Text
renderTop = renderStrict . layoutPretty defaultLayoutOptions . prettyTerm names
