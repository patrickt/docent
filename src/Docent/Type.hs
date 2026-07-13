{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Docent.Type
  ( Ty (..),
    -- | smart ctors
    forall_,
    mu_,
    exists_,
    -- | retty-printing
    prettyTy,
    renderTy,
    hasType,
    -- | optics
    _TVar,
    _TString,
    _TVoid,
    _TFun,
    _TRecord,
    _TVariant,
    _TForall,
    _TMu, -- lol
    _TExists,
    -- | Errors
    TypeError (..),
    assertType,
  )
where

import Bound
import Control.Effect.Error
import Control.Monad (ap)
import Data.Map.Ordered (OMap)
import Data.Map.Ordered qualified as OMap
import Data.Stream (Stream (..))
import Data.Text (Text)
import Data.Text qualified as T
import Docent.Ident
import Optics
import Prettyprinter (Pretty (..), defaultLayoutOptions, layoutPretty, (<+>))
import Prettyprinter qualified as P
import Prettyprinter.Render.Text (renderStrict)

data Ty a
  = TVar a
  | TString
  | TVoid
  | TFun (Ty a) (Ty a)
  | TRecord (OMap Ident (Ty a))
  | TVariant (OMap Ident (Ty a))
  | TForall (Scope () Ty a)
  | TMu (Scope () Ty a)
  | TExists (Scope () Ty a)
  deriving (Functor, Foldable, Traversable)

makePrisms ''Ty

instance Applicative Ty where
  pure = TVar
  (<*>) = ap

-- (>>=) is capture-avoiding substitution of types for type variables.
instance Monad Ty where
  TVar a >>= k = k a
  TString >>= _ = TString
  TVoid >>= _ = TVoid
  TFun d c >>= k = TFun (d >>= k) (c >>= k)
  TRecord fs >>= k = TRecord (fmap (>>= k) fs)
  TVariant fs >>= k = TVariant (fmap (>>= k) fs)
  TForall b >>= k = TForall (b >>>= k)
  TMu b >>= k = TMu (b >>>= k)
  TExists b >>= k = TExists (b >>>= k)

-- Comparing under fromScope compares de Bruijn structure, so (==) is
-- alpha-equivalence.
instance (Eq a) => Eq (Ty a) where
  TVar a == TVar b = a == b
  TString == TString = True
  TVoid == TVoid = True
  TFun d c == TFun d' c' = d == d' && c == c'
  TRecord as == TRecord bs = OMap.assocs as == OMap.assocs bs
  TVariant as == TVariant bs = OMap.assocs as == OMap.assocs bs
  TForall a == TForall b = fromScope a == fromScope b
  TMu a == TMu b = fromScope a == fromScope b
  TExists a == TExists b = fromScope a == fromScope b
  _ == _ = False

forall_, mu_, exists_ :: (Eq a) => a -> Ty a -> Ty a
forall_ x = TForall . abstract1 x
mu_ x = TMu . abstract1 x
exists_ x = TExists . abstract1 x

-- Binders bind loosest (their body extends maximally right); the function
-- arrow is right-associative. Atoms and the brace/angle forms self-delimit.
prettyTy :: Stream Ident -> Ty Ident -> P.Doc ann
prettyTy = prettyTyPrec 0

prettyTyPrec :: Int -> Stream Ident -> Ty Ident -> P.Doc ann
prettyTyPrec _ _ (TVar a) = pretty a
prettyTyPrec _ _ TString = "string"
prettyTyPrec _ _ TVoid = "∅"
prettyTyPrec d sup (TFun from to) =
  parensIf (d > funPrec) (prettyTyPrec (funPrec + 1) sup from <+> "→" <+> prettyTyPrec funPrec sup to)
  where
    funPrec = 5
prettyTyPrec _ sup (TRecord fields) =
  P.group . P.braces . P.nest 2 . P.vsep . P.punctuate "," . fmap (uncurry (fieldWith sup ":")) . OMap.assocs $ fields
prettyTyPrec _ sup (TVariant fields) =
  P.group . P.angles . P.nest 2 . P.vsep . P.punctuate "|" . fmap (uncurry (fieldWith sup ":")) . OMap.assocs $ fields
prettyTyPrec d (Cons n rest) (TForall b) = prettyQuant d "∀" n rest b
prettyTyPrec d (Cons n rest) (TMu b) = prettyQuant d "μ" n rest b
prettyTyPrec d (Cons n rest) (TExists b) = prettyQuant d "∃" n rest b

prettyQuant :: Int -> P.Doc ann -> Ident -> Stream Ident -> Scope () Ty Ident -> P.Doc ann
prettyQuant d q n rest b =
  parensIf (d > 0) (q <> pretty n <> "." <+> prettyTyPrec 0 rest (instantiate1 (TVar n) b))

fieldWith :: Stream Ident -> P.Doc ann -> Ident -> Ty Ident -> P.Doc ann
fieldWith sup sep name ty = pretty name <+> sep <+> prettyTyPrec 0 sup ty

parensIf :: Bool -> P.Doc ann -> P.Doc ann
parensIf True = P.parens
parensIf False = id

renderTy :: Ty Ident -> Text
renderTy = renderStrict . layoutPretty defaultLayoutOptions . prettyTy names

instance Pretty (Ty Ident) where
  pretty = prettyTy names

instance Show (Ty Ident) where
  show = T.unpack . renderTy

hasType :: Stream Ident -> Ident -> Ty Ident -> P.Doc ann
hasType sup name ty = pretty name <+> ":" <+> prettyTy sup ty

data TypeError = TypeError (Ty Ident) (Ty Ident) -- expected, got
  deriving (Eq)

instance Show TypeError where
  show = T.unpack . renderStrict . layoutPretty defaultLayoutOptions . pretty

instance Pretty TypeError where
  pretty (TypeError ex got) = "type error: expected " <+> pretty ex <+> ", got" <+> pretty got

assertType :: (Has (Error TypeError) sig m) => Prism' (Ty Ident) y -> Ty Ident -> Ty Ident -> m y
assertType optic given val =
  case (preview optic val) of
    Just v -> pure v
    Nothing -> throwError (TypeError given val)
