{-# LANGUAGE OverloadedStrings #-}
module Docent.Ident
  ( Ident (..)
  , fromText
  , toText
  , toString
  , gensym
  , names
  ) where

import Data.Interned (intern, unintern)
import Data.Interned.Text (InternedText)
import Data.Stream (Stream)
import Data.Stream qualified as Stream
import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as T
import Prettyprinter (Pretty (..))

-- Gensyms can never collide with source-syntax names: distinctness lives in
-- the constructor, not in a naming convention. The base name is display-only;
-- the Int alone carries identity.
data Ident
  = Ident InternedText
  | Gensym InternedText Int
  deriving (Eq, Ord)

instance IsString Ident where
  fromString = fromText . T.pack

instance Show Ident where
  show = show . toText

instance Pretty Ident where
  pretty = pretty . toText

fromText :: Text -> Ident
fromText = Ident . intern

gensym :: Ident -> Int -> Ident
gensym base = Gensym (baseName base)
  where
    baseName (Ident t) = t
    baseName (Gensym t _) = t

toText :: Ident -> Text
toText (Ident t) = unintern t
toText (Gensym t i) = unintern t <> "%" <> T.pack (show i)

toString :: Ident -> String
toString = T.unpack . toText

names :: Stream Ident
names = Gensym "v" <$> Stream.iterate succ 0
