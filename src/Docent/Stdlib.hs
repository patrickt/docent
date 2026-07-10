{-# LANGUAGE OverloadedStrings #-}

module Docent.Stdlib
  ( list
  , unit
  , unitTy
  , con
  , nil
  , cons
  , map_
  , append
  , flatten
  , join
  ) where

import Bound (instantiate1)
import Data.Map.Ordered qualified as OMap

import Docent.Ident (Ident)
import Docent.Lang (Sig)
import Docent.Sum (Term, var)
import Docent.Syntax.Fixpoint (fix_)
import Docent.Syntax.Mu (fold_, unfold_)
import Docent.Syntax.Prog (app, lam)
import Docent.Syntax.Record (project, record)
import Docent.Syntax.StrLit (concat_, eString)
import Docent.Syntax.Universal (tyApp, tyLam)
import Docent.Syntax.Variant (Branch (..), case_, inject_)
import Docent.Type

unitTy :: Ty Ident
unitTy = TRecord OMap.empty

unit :: Term Sig Ident
unit = record ([] :: [(Ident, Term Sig Ident)])

-- τ list ≜ μt. ⟨nil : () | cons : {hd : τ, tail : t}⟩
-- The recursion binder is "t" so that instantiating at a type with "α" free
-- (as the Λ-terms below do) can't be captured by it.
list :: Ty Ident -> Ty Ident
list elemTy = mu_ "t" (body (TVar "t"))
  where
    body tl = TVariant (OMap.fromList
      [ ("nil", unitTy)
      , ("cons", TRecord (OMap.fromList [("hd", elemTy), ("tail", tl)]))
      ])

-- ℓ_{μα.τ} e ≜ fold [μα.τ] (inject e at ℓ as τ[α ↦ μα.τ])
con :: Ident -> Ty Ident -> Term Sig Ident -> Term Sig Ident
con l ty@(TMu b) e = fold_ ty (inject_ l (instantiate1 ty b) e)
con _ ty _ = error ("con: not a recursive type: " <> show ty)

nil :: Ty Ident -> Term Sig Ident
nil a = con "nil" (list a) unit

cons :: Ty Ident -> Term Sig Ident -> Term Sig Ident -> Term Sig Ident
cons a hd tl = con "cons" (list a) (record [("hd", hd), ("tail", tl)])

-- map : ∀α,β. (α → β) → α list → β list
map_ :: Term Sig Ident
map_ =
  tyLam "α" $ tyLam "β" $
    fix_ "map" (TFun (TFun a b) (TFun (list a) (list b))) $
      lam "f" (TFun a b) $
        lam "xs" (list a) $
          case_ (unfold_ (var "xs"))
            [ Branch "nil" "u" (nil b)
            , Branch "cons" "c"
                (cons b
                  (app (var "f") (project (var "c") "hd"))
                  (app (app (var "map") (var "f")) (project (var "c") "tail")))
            ]
  where
    a = TVar "α"
    b = TVar "β"

-- append : ∀α. α list → α list → α list
append :: Term Sig Ident
append =
  tyLam "α" $
    fix_ "append" (TFun (list a) (TFun (list a) (list a))) $
      lam "xs" (list a) $
        lam "ys" (list a) $
          case_ (unfold_ (var "xs"))
            [ Branch "nil" "u" (var "ys")
            , Branch "cons" "c"
                (cons a
                  (project (var "c") "hd")
                  (app (app (var "append") (project (var "c") "tail")) (var "ys")))
            ]
  where
    a = TVar "α"

-- flatten : ∀α. α list list → α list
flatten :: Term Sig Ident
flatten =
  tyLam "α" $
    fix_ "flatten" (TFun (list (list a)) (list a)) $
      lam "xss" (list (list a)) $
        case_ (unfold_ (var "xss"))
          [ Branch "nil" "u" (nil a)
          , Branch "cons" "c"
              (app (app (tyApp append a) (project (var "c") "hd"))
                   (app (var "flatten") (project (var "c") "tail")))
          ]
  where
    a = TVar "α"

-- join : String list → String
join :: Term Sig Ident
join =
  fix_ "join" (TFun (list TString) TString) $
    lam "xs" (list TString) $
      case_ (unfold_ (var "xs"))
        [ Branch "nil" "u" (eString "")
        , Branch "cons" "c"
            (concat_ (project (var "c") "hd") (app (var "join") (project (var "c") "tail")))
        ]
