module Docent.FreeVars
  ( FreeVarsAlg (..),
    freeVars,
    FreeTyVarsAlg (..),
    freeTyVars,
    Set,
  )
where

import Data.Set (Set)
import Data.Set qualified as Set
import Docent.Ident (Ident)
import Docent.Sum

class FreeVarsAlg f where
  freeVarsAlg :: (FreeVarsAlg s, HBind s, Ord a) => f (Term s) a -> Set a

freeVars :: (FreeVarsAlg s, HBind s, Ord a) => Term s a -> Set a
freeVars (Var s) = Set.singleton s
freeVars (In s) = freeVarsAlg s

instance (FreeVarsAlg f, FreeVarsAlg g) => FreeVarsAlg (f :+: g) where
  freeVarsAlg (InL x) = freeVarsAlg x
  freeVarsAlg (InR y) = freeVarsAlg y

class FreeTyVarsAlg f where
  freeTyVarsAlg :: (FreeTyVarsAlg s, HBind s) => f (Term s) a -> Set Ident

freeTyVars :: (FreeTyVarsAlg s, HBind s) => Term s a -> Set Ident
freeTyVars (Var _) = Set.empty
freeTyVars (In s) = freeTyVarsAlg s

instance (FreeTyVarsAlg f, FreeTyVarsAlg g) => FreeTyVarsAlg (f :+: g) where
  freeTyVarsAlg (InL x) = freeTyVarsAlg x
  freeTyVarsAlg (InR y) = freeTyVarsAlg y
