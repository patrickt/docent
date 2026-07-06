{-# LANGUAGE OverloadedStrings #-}

module Docent.Type (Ty (..), TypeError (..)) where

import Prettyprinter

data Ty = TString | TFun Ty Ty
  deriving (Eq, Show)

instance Pretty Ty where
  pretty TString = "string"
  pretty (TFun from to) = parens (pretty from <+> " → " <+> pretty to)

data TypeError = TypeError Ty Ty -- expected, got
  deriving (Eq, Show)

instance Pretty TypeError where
  pretty (TypeError ex got) = "type error: expected " <+> pretty ex <+> ", got" <+> pretty got
