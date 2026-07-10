module Docent.Ident
  ( Ident (..)
  , fromText
  , toText
  , toString
  , names
  ) where

import Data.Interned (intern, unintern)
import Data.Interned.Text (InternedText)
import Data.Stream (Stream)
import Data.Stream qualified as Stream
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

names :: Stream Ident
names = Stream.unfold (\i -> (fromText (T.pack ("v" <> show (i :: Int))), succ i)) 0
