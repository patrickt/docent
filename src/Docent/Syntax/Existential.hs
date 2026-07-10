{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}

module Docent.Syntax.Existential
  ( ExiF (..),
    pack_,
    unpack_,
  )
where

import Bound
import Bound.Var (unvar)
import Data.Stream
import Docent.Algebra
import Docent.Ident
import Docent.Sum
import Docent.Type
import Docent.Typecheck
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as P

data ExiF t a
  = Pack (t a) (Ty Ident) (Ty Ident) -- payload, witness, annotation
  | Unpack Ident (t a) (Scope () t a)

instance HBind ExiF where
  hbind k (Pack p w a) = Pack (p >>= k) w a
  hbind k (Unpack n v s) = Unpack n (v >>= k) (s >>>= k)

instance PrettyAlg ExiF where
  prettyAlg sup (Pack payload witness annotation) =
    "pack" <+> prettyTerm sup payload <+> "as ∃" <> pretty witness <> "." <> pretty annotation
  prettyAlg (Cons n rest) (Unpack name val scope) =
    "unpack" <+> P.parens (pretty name <> "," <> prettyTerm rest val) <+> "=" <+> prettyTerm rest (instantiate1 (var n) scope)

instance TypeableF ExiF where
  tcAlg ctx (Pack payload witness ann) = case ann of
    TExists within -> do
      given <- typecheck ctx payload
      let expected = instantiate1 witness within
      if given == expected
        then pure ann
        else typeError expected given
    other -> typeError (TExists (toScope TVoid)) other
  tcAlg ctx (Unpack name val scope) = do
    te <- typecheck ctx val
    case te of
      TExists within -> do
        let inner = instantiate1 (pure name) within
        result <- typecheck (unvar (const inner) ctx) (fromScope scope)
        if name `elem` result
          then typeError (TExists (toScope TVoid)) result
          else pure result
      other -> typeError (TExists (toScope TVoid)) other

instance EqAlg ExiF where
  eqAlg (Pack p w a) (Pack p' w' a') = eqTerm p p' && w == w' && a == a'
  eqAlg (Unpack n v s) (Unpack n' v' s') = n == n' && eqTerm v v' && eqTerm (fromScope s) (fromScope s')
  eqAlg _ _ = False

pack_ :: (ExiF :<: s) => Term s a -> Ty Ident -> Ty Ident -> Term s a
pack_ payload witness annotation = inject (Pack payload witness annotation)

unpack_ :: (ExiF :<: s, HBind s, Eq a) => a -> Ident -> Term s a -> Term s a -> Term s a
unpack_ x name val scope = inject (Unpack name val (abstract1 x scope))
