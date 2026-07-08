{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Docent.Lang
  ( Sig
  , eval
  , names
  , textShowTop
  , module Docent.Sum
  , module Docent.Type
  , module Docent.Algebra
  , module Docent.Syntax.StrLit
  , module Docent.Syntax.Prog
  ) where

import Bound (instantiate1)
import Data.Text (Text)
import Data.Stream qualified as Stream
import Data.Text qualified as T
import Data.Map.Ordered (OMap)
import Data.Map.Ordered qualified as Map

import Docent.Ident (Ident)
import Docent.Ident qualified as Ident
import Docent.Sum
import Docent.Type
import Docent.Algebra
import Docent.Syntax.StrLit
import Docent.Syntax.Prog
import Docent.Syntax.Record

type Sig = StrF :+: LamF :+: RecF

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
  | Just (Record _) <- prj t = In t
  | Just (Project rec_ f) <- prj t =
      case (eval rec_) of
        In u | Just (Record rs) <- prj u, Just field <- Map.lookup f rs -> eval field
        In u | Just (Record rs) <- prj u, Nothing <- Map.lookup f rs -> error "no such field"
        _ -> error "eval: project on non-record"
  | otherwise = error "eval: stuck"

names :: Stream.Stream Ident
names = Stream.unfold (\i -> (Ident.fromText (T.pack ("v" <> show (i :: Int))), succ i)) 0

textShowTop :: Term Sig Ident -> Text
textShowTop = textShow names
