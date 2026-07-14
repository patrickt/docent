{-# LANGUAGE TemplateHaskell #-}

module Docent.Optics
  ( _Term,
    _Just,
    _Free,
    require,
  )
where

import Bound qualified as B
import Control.Effect.Error
import Docent.Sum (Term, (:<:))
import Docent.Sum qualified as Sum
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

_Free :: Prism (B.Var b a) (B.Var b a) a a
_Free =
  prism'
    B.F
    ( \case
        B.F x -> Just x
        _ -> Nothing
    )
