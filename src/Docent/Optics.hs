{-# LANGUAGE TemplateHaskell #-}

module Docent.Optics
  ( _Term
  , _EString
  , _Concat
  , _Lam
  , _Record
  , _Just
  , require
  ) where

import Docent.Sum qualified as Sum
import Docent.Syntax.StrLit (StrF (..))
import Optics.TH (makePrisms)
import Docent.Sum ((:<:), Term)
import Optics
import Control.Effect.Error
import Data.Text (Text)
import Docent.Syntax.Prog
import Docent.Syntax.Record
import Docent.Syntax.Variant

require :: (Has (Error err) sig m, f :<: s) => Prism' (f (Term s) a) x -> err -> Term s a -> m x
require optic err val = let x = _Term % optic in case (preview x val) of
  Just v -> pure v
  Nothing -> throwError err


_Term :: (f :<: s) => Prism' (Term s a) (f (Term s) a)
_Term = prism' Sum.inject (\case
                              Sum.Var _ -> Nothing
                              Sum.In v -> Sum.prj v)

traverse makePrisms [''StrF, ''LamF, ''RecF, ''VntF]
