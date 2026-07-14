module Docent.FreeVars
  ( FreeVarsAlg (..)
  , freeVars
  , Set
  ) where

import Data.Set (Set)
import Data.Set qualified as Set
import Docent.Sum

class FreeVarsAlg f where
  freeVarsAlg :: (FreeVarsAlg s, HBind s, Ord a) => f (Term s) a -> Set a

freeVars :: (FreeVarsAlg s, HBind s, Ord a) => Term s a -> Set a
freeVars (Var s) = Set.singleton s
freeVars (In s) = freeVarsAlg s

instance (FreeVarsAlg f, FreeVarsAlg g) => FreeVarsAlg (f :+: g) where
  freeVarsAlg (InL x) = freeVarsAlg x
  freeVarsAlg (InR y) = freeVarsAlg y
