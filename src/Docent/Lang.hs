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
import Data.Text (Text)
import Docent.Algebra
import Docent.Ident (Ident, names)
import Docent.Optics (require)
import Docent.Optics qualified as O
import Docent.Sum
import Docent.Syntax.Fixpoint
import Docent.Syntax.Mu
import Docent.Syntax.Prog
import Docent.Syntax.Record
import Docent.Syntax.StrLit
import Docent.Syntax.Variant
import Docent.Type
import Prettyprinter (Pretty (..), defaultLayoutOptions, layoutPretty, (<+>))
import Prettyprinter.Render.Text (renderStrict)
import Docent.Syntax.Existential
import Docent.Syntax.Universal
import Optics ((%), _Just)

type Sig = StrF :+: LamF :+: RecF :+: VntF :+: FixF :+: MuF :+: ExiF :+: UniF

data EvalError
  = NonStringConcat
  | NonFunctionApplication
  | NonRecordProjection
  | MissingField Ident
  | NonVariantScrutinee
  | MissingBranch Ident
  | NonFoldUnfold
  | NonPackUnpack
  | NonTypeAbstraction
  | StuckTerm
    deriving (Eq, Show)

instance Pretty EvalError where
  pretty NonStringConcat = "concatenation of non-string values"
  pretty NonFunctionApplication = "application of a non-function"
  pretty NonRecordProjection = "projection from a non-record"
  pretty (MissingField f) = "record has no field" <+> pretty f
  pretty NonVariantScrutinee = "case scrutinee is not a variant"
  pretty (MissingBranch l) = "case has no branch for label" <+> pretty l
  pretty NonFoldUnfold = "unfold of a non-fold value"
  pretty NonPackUnpack = "unpack of a non-pack value"
  pretty NonTypeAbstraction = "type application of a non-type-abstraction"
  pretty StuckTerm = "evaluation is stuck: "

eval :: (Has (Error EvalError) sig m) => Term Sig a -> m (Term Sig a)
eval (Var a) = pure (Var a)
eval v@(Match (EString _)) = pure v
eval (Match (Concat a b)) = do
  a' <- eval a >>= require (O._Term % _EString) NonStringConcat
  b' <- eval b >>= require (O._Term % _EString) NonStringConcat
  pure (eString (a' <> b'))
eval v@(Match (Lam _ _)) = pure v
eval (Match (App f x)) = do
  (_, b) <- eval f >>= require (O._Term % _Lam) NonFunctionApplication
  x' <- eval x
  eval (instantiate1 x' b)
eval (Match (Let e b)) = eval (instantiate1 e b)
eval v@(Match (Record _)) = pure v
eval (Match (Project rec_ f)) = do
  rs <- eval rec_ >>= require (O._Term % _Record) NonRecordProjection
  field <- require _Just (MissingField f) (OMap.lookup f rs)
  eval field
eval v@(Match (Inject {})) = pure v
eval (Match (Case val branches)) = do
  (lab, _ty, payload) <- eval val >>= require (O._Term % _Inject) NonVariantScrutinee
  alt <- require _Just (MissingBranch lab) (OMap.lookup lab branches)
  payload' <- eval payload
  eval (instantiate1 payload' alt)
eval v@(Match (Fix _ty val)) = eval (instantiate1 v val)
eval v@(Match (Fold _ _)) = pure v
eval (Match (Unfold e)) = do
  (_ty, inner) <- eval e >>= require (O._Term % _Fold) NonFoldUnfold
  eval inner
eval v@(Match (Pack {})) = pure v
eval (Match (Unpack _name val scope)) = do
  (payload, _wit, _ann) <- eval val >>= require (O._Term % _Pack) NonPackUnpack
  payload' <- eval payload
  eval (instantiate1 payload' scope)
eval v@(Match (TyLam {})) = pure v
eval (Match (TyApp e _ty)) = do
  (_name, body) <- eval e >>= require (O._Term % _TyLam) NonTypeAbstraction
  eval body
eval _other = throwError StuckTerm

runEval :: Term Sig a -> Either EvalError (Term Sig a)
runEval = run . runError . eval

renderTop :: Term Sig Ident -> Text
renderTop = renderStrict . layoutPretty defaultLayoutOptions . prettyTerm names
