{-# LANGUAGE TemplateHaskell #-}

module Docent.Optics
  ( _Term,
    _EString,
    _Concat,
    _Lam,
    _Record,
    _Just,
    _Inject,
    _Fold,
    _Unfold,
    _Pack,
    _TyLam,
    require
  )
where

import Control.Effect.Error
import Docent.Sum (Term, (:<:))
import Docent.Sum qualified as Sum
import Docent.Type qualified as X
import Docent.Syntax.Existential
import Docent.Syntax.Mu (MuF (..))
import Docent.Syntax.Prog (LamF (..))
import Docent.Syntax.Record (RecF (..))
import Docent.Syntax.StrLit (StrF (..))
import Docent.Syntax.Universal (UniF (..))
import Docent.Syntax.Variant (VntF (..))
import Optics

require :: (Has (Error err) sig m) => Prism' x y -> err -> x -> m y
require optic err val =
   case (preview optic val) of
     Just v -> pure v
     Nothing -> throwError err

_Term :: (f :<: s) => Prism' (Term s a) (f (Term s) a)
_Term =
  prism'
    Sum.inject
    ( \case
        Sum.Var _ -> Nothing
        Sum.In v -> Sum.prj v
    )

makePrisms ''StrF
makePrisms ''LamF
makePrisms ''RecF
makePrisms ''VntF
makePrisms ''MuF
makePrisms ''ExiF
makePrisms ''UniF
