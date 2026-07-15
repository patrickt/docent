{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Docent.Syntax.Existential
  ( ExiF (..),
    _Pack,
    _Unpack,
    pack_,
    unpack_,
  )
where

import Bound
import Bound.Var (unvar)
import Data.Set qualified as Set
import Data.Stream
import Docent.Algebra
import Docent.FreeVars
import Docent.Ident
import Docent.Sum
import Docent.Type
import Docent.Typecheck
import Docent.Util
import Optics
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as P
import Docent.Optics (_Free)

data ExiF t a
  = Pack (t a) (Ty Ident) (Ty Ident) -- payload, witness, annotation
  | Unpack Ident (t a) (Scope () t a)

makePrisms ''ExiF

instance HBind ExiF where
  hbind k (Pack p w a) = Pack (p >>= k) w a
  hbind k (Unpack n v s) = Unpack n (v >>= k) (s >>>= k)

instance PrettyAlg ExiF where
  prettyAlg sup (Pack payload witness annotation) =
    "pack" <+> prettyTerm sup payload <+> "as ∃" <> prettyTy sup witness <> "." <> prettyTy sup annotation
  prettyAlg (Cons n rest) (Unpack name val scope) =
    "unpack" <+> P.parens (pretty name <> "," <> prettyTerm rest val) <+> "=" <+> prettyTerm rest (instantiate1 (var n) scope)

instance TypeableF ExiF where
  tcAlg ctx (Pack payload witness ann) = do
    witness' <- resolve witness
    ann' <- resolve ann
    within <- assertType _TExists (TExists (toScope TVoid)) ann'
    given <- typecheck ctx payload
    let expected = instantiate1 witness' within
    if given == expected
      then pure ann'
      else typeError expected given
  tcAlg ctx (Unpack name val scope) = do
    te <- typecheck ctx val
    within <- assertType _TExists (TExists (toScope TVoid)) te
    sk <- freshTyVar name
    let inner = instantiate1 (TVar sk) within
    result <- withTyVar name sk (typecheck (unvar (const inner) ctx) (fromScope scope))
    if sk `elem` result
      then typeError (TExists (toScope TVoid)) result
      else pure result

instance EqAlg ExiF where
  eqAlg (Pack p w a) (Pack p' w' a') = eqTerm p p' && w == w' && a == a'
  eqAlg (Unpack n v s) (Unpack n' v' s') = n == n' && eqTerm v v' && eqTerm (fromScope s) (fromScope s')
  eqAlg _ _ = False

instance FreeVarsAlg ExiF where
  freeVarsAlg (Pack payload _w _a) = freeVars payload
  freeVarsAlg (Unpack _ payload body) = do
    let v = freeVars payload
    let b = mapMaybeSet (preview _Free) (freeVars (fromScope body))
    v `Set.union` b

instance FreeTyVarsAlg ExiF where
  freeTyVarsAlg (Pack payload witness annotation)
    = freeTyVars payload <> setFromList witness <> setFromList annotation
  freeTyVarsAlg (Unpack nam term body)
    = freeTyVars term <> Set.delete nam (freeTyVars (fromScope body))

pack_ :: (ExiF :<: s) => Term s a -> Ty Ident -> Ty Ident -> Term s a
pack_ payload witness annotation = inject (Pack payload witness annotation)

unpack_ :: (ExiF :<: s, HBind s, Eq a) => a -> Ident -> Term s a -> Term s a -> Term s a
unpack_ x name val scope = inject (Unpack name val (abstract1 x scope))
