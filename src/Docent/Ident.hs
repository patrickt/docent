module Docent.Ident
  ( Ident (..)
  , fromText
  , toText
  , toString
  ) where

import Data.Interned (intern, unintern)
import Data.Interned.Text (InternedText)
import Data.String (IsString)
import Data.Text (Text)
import Data.Text qualified as T
import Prettyprinter (Pretty (..))

newtype Ident = Ident InternedText
  deriving newtype (Eq, Ord, Show, IsString)

fromText :: Text -> Ident
fromText = Ident . intern

toText :: Ident -> Text
toText (Ident t) = unintern t

toString :: Ident -> String
toString = T.unpack . toText

instance Pretty Ident where
  pretty = pretty . toText
