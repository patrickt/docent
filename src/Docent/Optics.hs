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
    require,
  )
where

import Control.Effect.Error
import Data.Text (Text)
import Docent.Sum (Term, (:<:))
import Docent.Sum qualified as Sum
import Docent.Syntax.Existential
import Docent.Syntax.Mu (MuF (..))
import Docent.Syntax.Prog
import Docent.Syntax.Record
import Docent.Syntax.StrLit (StrF (..))
import Docent.Syntax.Variant
import Optics
import Optics.TH (makePrisms)

require :: (Has (Error err) sig m, f :<: s) => Prism' (f (Term s) a) x -> err -> Term s a -> m x
require optic err val =
  let x = _Term % optic
   in case (preview x val) of
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
