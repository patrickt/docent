{-# LANGUAGE OverloadedStrings #-}

module Docent.Type (Ty (..), TypeError (..), hasType) where

import Prettyprinter (Pretty (..), (<+>))
import Prettyprinter qualified as P
import Data.Map.Ordered (OMap)
import Data.Map.Ordered qualified as OMap

import Docent.Ident

data Ty
  = TString
  | TFun Ty Ty
  | TRecord (OMap Ident Ty)
  | TVariant (OMap Ident Ty)
  deriving (Eq, Show)

instance Pretty Ty where
  pretty TString = "string"
  pretty (TFun from to) = P.parens (pretty from <+> " → " <+> pretty to)
  pretty (TRecord fields) =
    P.braces . P.vsep . P.punctuate "," . fmap (uncurry hasType) . OMap.assocs $ fields
  pretty (TVariant fields) =
    P.angles . P.vsep . P.punctuate "|" . fmap (uncurry hasType) . OMap.assocs $ fields

hasType :: Ident -> Ty -> P.Doc ann
hasType name ty = pretty name <+> ":" <+> pretty ty

data TypeError = TypeError Ty Ty -- expected, got
  deriving (Eq, Show)

instance Pretty TypeError where
  pretty (TypeError ex got) = "type error: expected " <+> pretty ex <+> ", got" <+> pretty got
