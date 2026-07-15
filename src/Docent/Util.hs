module Docent.Util (mapMaybeSet, setFromList) where

import Data.Foldable (toList)
import Data.Maybe
import Data.Set (Set)
import Data.Set qualified as Set

-- O(n)
mapMaybeSet :: (Ord b) => (a -> Maybe b) -> Set a -> Set b
mapMaybeSet fn = Set.fromList . mapMaybe fn . Set.toList

setFromList :: (Ord a, Foldable f) => f a -> Set a
setFromList = Set.fromList . toList
