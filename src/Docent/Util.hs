module Docent.Util (mapMaybeSet ) where
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe

-- O(n)
mapMaybeSet :: Ord b => (a -> Maybe b) -> Set a -> Set b
mapMaybeSet fn = Set.fromList . mapMaybe fn . Set.toList
