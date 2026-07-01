module Docent.Type (Ty (..), TypeError (..)) where

data Ty = TString | TFun Ty Ty
  deriving (Eq, Show)

newtype TypeError = TypeError String
  deriving (Eq, Show)
