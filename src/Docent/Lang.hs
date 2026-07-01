{-# LANGUAGE FlexibleContexts #-}
module Docent.Lang
  ( Sig
  , eval
  , module Docent.Sum
  , module Docent.Type
  , module Docent.Algebra
  , module Docent.Syntax.StrLit
  , module Docent.Syntax.Prog
  ) where

import Bound (instantiate1)

import Docent.Sum
import Docent.Type
import Docent.Algebra
import Docent.Syntax.StrLit
import Docent.Syntax.Prog

type Sig = StrF :+: LamF

eval :: Term Sig a -> Term Sig a
eval (Var a) = Var a
eval (In t)
  | Just (EString _) <- prj t = In t
  | Just (Concat a b) <- prj t =
      case (eval a, eval b) of
        (In u, In v)
          | Just (EString sa) <- prj u
          , Just (EString sb) <- prj v -> eString (sa <> sb)
        _ -> error "eval: Concat of non-strings"
  | Just (Lam _ _) <- prj t = In t
  | Just (App f x) <- prj t =
      case eval f of
        In u | Just (Lam _ b) <- prj u -> eval (instantiate1 (eval x) b)
        _ -> error "eval: App of non-lambda"
  | Just (Let e b) <- prj t = eval (instantiate1 e b)
  | otherwise = error "eval: stuck"
