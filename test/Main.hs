{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.Text (Text)
import Data.Text qualified as T

import Hedgehog hiding (eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Docent.Ident (Ident)
import Docent.Ident qualified as Ident
import Docent.Sum (Term, var)
import Docent.Type (Ty (..))
import Docent.Algebra (typecheck, eqTerm)
import Docent.Syntax.StrLit (eString, concat_)
import Docent.Syntax.Prog (lam, app, let_)
import Docent.Lang (Sig, eval, textShowTop)

genText :: Gen Text
genText = Gen.text (Range.linear 0 32) Gen.unicode

noFree :: Ident -> Ty
noFree v = error ("unexpected free variable: " <> Ident.toString v)

typechecksTo :: Term Sig Ident -> Ty -> PropertyT IO ()
typechecksTo t ty = typecheck noFree t === Right ty

infix 4 ~==
(~==) :: Term Sig Ident -> Term Sig Ident -> PropertyT IO ()
actual ~== expected = do
  annotate ("expected: " <> T.unpack (textShowTop expected))
  annotate ("actual:   " <> T.unpack (textShowTop actual))
  assert (eqTerm actual expected)

prop_typecheckString :: Property
prop_typecheckString = property $ do
  s <- forAll genText
  eString s `typechecksTo` TString

prop_evalString :: Property
prop_evalString = property $ do
  s <- forAll genText
  eval (eString s) ~== eString s

prop_evalConcat :: Property
prop_evalConcat = property $ do
  a <- forAll genText
  b <- forAll genText
  eval (concat_ (eString a) (eString b)) ~== eString (a <> b)

-- let x = a in x + (b + x)
letProg :: Text -> Text -> Term Sig Ident
letProg a b = let_ "x" (eString a) (concat_ (var "x") (concat_ (eString b) (var "x")))

prop_typecheckLet :: Property
prop_typecheckLet = property $ do
  a <- forAll genText
  b <- forAll genText
  letProg a b `typechecksTo` TString

prop_evalLet :: Property
prop_evalLet = property $ do
  a <- forAll genText
  b <- forAll genText
  eval (letProg a b) ~== eString (a <> b <> a)

-- (\x:string. x) s
appProg :: Text -> Term Sig Ident
appProg s = app (lam "x" TString (var "x")) (eString s)

prop_typecheckApp :: Property
prop_typecheckApp = property $ do
  s <- forAll genText
  appProg s `typechecksTo` TString

prop_evalApp :: Property
prop_evalApp = property $ do
  s <- forAll genText
  eval (appProg s) ~== eString s

prop_textShowApp :: Property
prop_textShowApp = withTests 1 . property $
  textShowTop (appProg "z") === "fun (v0 : string). v0 \"z\""

main :: IO ()
main = defaultMain $ testGroup "docent"
  [ testGroup "typecheck"
      [ testPropertyNamed "string literal is TString" "prop_typecheckString" prop_typecheckString
      , testPropertyNamed "let-bound concat is TString" "prop_typecheckLet" prop_typecheckLet
      , testPropertyNamed "identity application is TString" "prop_typecheckApp" prop_typecheckApp
      ]
  , testGroup "eval"
      [ testPropertyNamed "string literal is a value" "prop_evalString" prop_evalString
      , testPropertyNamed "concat concatenates" "prop_evalConcat" prop_evalConcat
      , testPropertyNamed "let substitutes" "prop_evalLet" prop_evalLet
      , testPropertyNamed "beta reduction" "prop_evalApp" prop_evalApp
      ]
  , testGroup "textShow"
      [ testPropertyNamed "freshens bound names" "prop_textShowApp" prop_textShowApp
      ]
  ]
