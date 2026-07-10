{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.Either (isLeft)
import Data.Foldable (toList)
import Data.Map.Ordered qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog

import Docent.Ident (Ident)
import Docent.Ident qualified as Ident
import Docent.Sum (Term, var)
import Docent.Type (Ty (..), exists_, forall_, mu_, renderTy)
import Docent.Algebra (eqTerm)
import Docent.Syntax.StrLit (eString, concat_)
import Docent.Syntax.Prog (lam, app, let_)
import Docent.Stdlib qualified as Std
import Docent.Syntax.Existential (pack_, unpack_)
import Docent.Syntax.Mu (fold_, unfold_)
import Docent.Syntax.Universal (tyApp, tyLam)
import Docent.Syntax.Record (record_, project_)
import Docent.Syntax.Variant (inject_)
import Docent.Typecheck (runTypecheck)
import Docent.Lang (Sig, EvalError (..), runEval, renderTop)

genText :: Gen Text
genText = Gen.text (Range.linear 0 32) Gen.unicode

noFree :: Ident -> Ty Ident
noFree v = error ("unexpected free variable: " <> Ident.toString v)

typechecksTo :: Term Sig Ident -> Ty Ident -> PropertyT IO ()
typechecksTo t ty = runTypecheck noFree t === Right ty

infix 4 ~==
(~==) :: Term Sig Ident -> Term Sig Ident -> PropertyT IO ()
actual ~== expected = do
  annotate ("expected: " <> T.unpack (renderTop expected))
  annotate ("actual:   " <> T.unpack (renderTop actual))
  assert (eqTerm actual expected)

evalsTo :: Term Sig Ident -> Term Sig Ident -> PropertyT IO ()
evalsTo t expected = case runEval t of
  Left err -> annotateShow err *> failure
  Right actual -> actual ~== expected

evalFailsWith :: Term Sig Ident -> EvalError -> PropertyT IO ()
evalFailsWith t err = case runEval t of
  Left e -> e === err
  Right v -> annotate ("evaluated to: " <> T.unpack (renderTop v)) *> failure

prop_typecheckString :: Property
prop_typecheckString = property $ do
  s <- forAll genText
  eString s `typechecksTo` TString

prop_evalString :: Property
prop_evalString = property $ do
  s <- forAll genText
  eString s `evalsTo` eString s

prop_evalConcat :: Property
prop_evalConcat = property $ do
  a <- forAll genText
  b <- forAll genText
  concat_ (eString a) (eString b) `evalsTo` eString (a <> b)

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
  letProg a b `evalsTo` eString (a <> b <> a)

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
  appProg s `evalsTo` eString s

prop_evalNonFunction :: Property
prop_evalNonFunction = property $ do
  a <- forAll genText
  b <- forAll genText
  app (eString a) (eString b) `evalFailsWith` NonFunctionApplication

prop_evalMissingField :: Property
prop_evalMissingField = property $ do
  names <- forAll genFieldNames
  missing <- forAll (Gen.filter (`notElem` names) genIdent)
  let fields = [(n, eString (Ident.toText n)) | n <- names]
  project_ (record_ fields) missing `evalFailsWith` MissingField missing

prop_tyAlphaEq :: Property
prop_tyAlphaEq = property $ do
  a <- forAll genIdent
  b <- forAll (Gen.filter (/= a) genIdent)
  forall_ a (TFun (TVar a) (TVar a)) === forall_ b (TFun (TVar b) (TVar b))
  forall_ a (TFun (TVar a) (TVar a)) /== forall_ a (TFun (TVar a) TString)

-- μa. ⟨nil : {} | cons : {head : string, tail : a}⟩
strListBody :: Ty Ident -> Ty Ident
strListBody tl = TVariant (Map.fromList
  [ ("nil", TRecord Map.empty)
  , ("cons", TRecord (Map.fromList [("head", TString), ("tail", tl)]))
  ])

strList, strListUnrolled :: Ty Ident
strList = mu_ "a" (strListBody (TVar "a"))
strListUnrolled = strListBody strList

nil :: Term Sig Ident
nil = fold_ strList (inject_ "nil" strListUnrolled (record_ ([] :: [(Ident, Term Sig Ident)])))

cons :: Text -> Term Sig Ident -> Term Sig Ident
cons s xs = fold_ strList (inject_ "cons" strListUnrolled (record_ [("head", eString s), ("tail", xs)]))

prop_typecheckFold :: Property
prop_typecheckFold = property $ do
  ss <- forAll (Gen.list (Range.linear 0 5) genText)
  foldr cons nil ss `typechecksTo` strList

prop_typecheckUnfold :: Property
prop_typecheckUnfold = property $ do
  ss <- forAll (Gen.list (Range.linear 0 5) genText)
  unfold_ (foldr cons nil ss) `typechecksTo` strListUnrolled

prop_evalUnfoldFold :: Property
prop_evalUnfoldFold = property $ do
  s <- forAll genText
  unfold_ (fold_ strList (eString s)) `evalsTo` eString s

prop_evalUnfoldNonFold :: Property
prop_evalUnfoldNonFold = property $ do
  s <- forAll genText
  unfold_ (eString s) `evalFailsWith` NonFoldUnfold

prop_evalUnpackPack :: Property
prop_evalUnpackPack = property $ do
  s <- forAll genText
  let pkg = pack_ (eString s) TString (exists_ "a" (TVar "a"))
  unpack_ "x" "a" pkg (var "x") `evalsTo` eString s

prop_evalUnpackNonPack :: Property
prop_evalUnpackNonPack = property $ do
  s <- forAll genText
  unpack_ "x" "a" (eString s) (var "x") `evalFailsWith` NonPackUnpack

prop_typecheckTyLam :: Property
prop_typecheckTyLam = withTests 1 . property $
  tyLam "a" (lam "x" (TVar "a") (var "x")) `typechecksTo` forall_ "b" (TFun (TVar "b") (TVar "b"))

prop_typecheckTyLamShadow :: Property
prop_typecheckTyLamShadow = withTests 1 . property $
  tyLam "a" (lam "x" (TVar "a") (tyLam "a" (lam "y" (TVar "a") (var "x"))))
    `typechecksTo`
      forall_ "a" (TFun (TVar "a") (forall_ "b" (TFun (TVar "b") (TVar "a"))))

prop_evalTyApp :: Property
prop_evalTyApp = property $ do
  s <- forAll genText
  app (tyApp (tyLam "a" (lam "x" (TVar "a") (var "x"))) TString) (eString s) `evalsTo` eString s

prop_evalTyAppNonTyLam :: Property
prop_evalTyAppNonTyLam = property $ do
  s <- forAll genText
  tyApp (eString s) TString `evalFailsWith` NonTypeAbstraction

strs :: [Text] -> Term Sig Ident
strs = foldr (Std.cons TString . eString) (Std.nil TString)

prop_stdlibTypes :: Property
prop_stdlibTypes = withTests 1 . property $ do
  Std.join `typechecksTo` TFun (Std.list TString) TString
  Std.map_ `typechecksTo`
    forall_ "a" (forall_ "b"
      (TFun (TFun (TVar "a") (TVar "b")) (TFun (Std.list (TVar "a")) (Std.list (TVar "b")))))
  Std.append `typechecksTo`
    forall_ "a" (TFun (Std.list (TVar "a")) (TFun (Std.list (TVar "a")) (Std.list (TVar "a"))))
  Std.flatten `typechecksTo`
    forall_ "a" (TFun (Std.list (Std.list (TVar "a"))) (Std.list (TVar "a")))

prop_stdlibJoin :: Property
prop_stdlibJoin = property $ do
  ss <- forAll (Gen.list (Range.linear 0 5) genText)
  app Std.join (strs ss) `evalsTo` eString (mconcat ss)

prop_stdlibAppend :: Property
prop_stdlibAppend = property $ do
  xs <- forAll (Gen.list (Range.linear 0 4) genText)
  ys <- forAll (Gen.list (Range.linear 0 4) genText)
  app Std.join (app (app (tyApp Std.append TString) (strs xs)) (strs ys))
    `evalsTo` eString (mconcat (xs <> ys))

prop_stdlibMap :: Property
prop_stdlibMap = property $ do
  ss <- forAll (Gen.list (Range.linear 0 4) genText)
  let bang = lam "s" TString (concat_ (var "s") (eString "!"))
  app Std.join (app (app (tyApp (tyApp Std.map_ TString) TString) bang) (strs ss))
    `evalsTo` eString (mconcat (map (<> "!") ss))

prop_stdlibFlatten :: Property
prop_stdlibFlatten = property $ do
  sss <- forAll (Gen.list (Range.linear 0 3) (Gen.list (Range.linear 0 3) genText))
  let obj = foldr (Std.cons (Std.list TString) . strs) (Std.nil (Std.list TString)) sss
  app Std.join (app (tyApp Std.flatten TString) obj)
    `evalsTo` eString (mconcat (mconcat sss))

prop_renderTyPrec :: Property
prop_renderTyPrec = withTests 1 . property $ do
  renderTy (TFun TString (TFun TString TString)) === "string → string → string"
  renderTy (TFun (TFun TString TString) TString) === "(string → string) → string"
  renderTy (forall_ "a" (TFun (TVar "a") (TVar "a"))) === "∀v%0. v%0 → v%0"
  renderTy (TFun (forall_ "a" (TVar "a")) TString) === "(∀v%0. v%0) → string"

prop_renderApp :: Property
prop_renderApp = withTests 1 . property $
  renderTop (appProg "z") === "fun (v%0 : string). v%0 \"z\""

genIdent :: Gen Ident
genIdent = Ident.fromText <$> Gen.text (Range.linear 1 8) Gen.alpha

-- Distinct names in a random (not sorted) insertion order.
genFieldNames :: Gen [Ident]
genFieldNames = do
  names <- Gen.set (Range.linear 1 5) (Gen.text (Range.linear 1 8) Gen.alpha)
  Gen.shuffle (map Ident.fromText (toList names))

prop_typecheckRecord :: Property
prop_typecheckRecord = property $ do
  names <- forAll genFieldNames
  vals <- forAll (Gen.list (Range.singleton (length names)) genText)
  let fields = zipWith (\n v -> (n, eString v)) names vals
  record_ fields `typechecksTo` TRecord (Map.fromList [(n, TString) | n <- names])

prop_typecheckProject :: Property
prop_typecheckProject = property $ do
  names <- forAll genFieldNames
  target <- forAll (Gen.element names)
  let fields = [(n, eString (Ident.toText n)) | n <- names]
  project_ (record_ fields) target `typechecksTo` TString

prop_typecheckProjectMissing :: Property
prop_typecheckProjectMissing = property $ do
  names <- forAll genFieldNames
  missing <- forAll (Gen.filter (`notElem` names) genIdent)
  let fields = [(n, eString (Ident.toText n)) | n <- names]
  let result = runTypecheck noFree (project_ (record_ fields) missing :: Term Sig Ident)
  annotateShow result
  assert (isLeft result)

prop_evalRecord :: Property
prop_evalRecord = property $ do
  names <- forAll genFieldNames
  vals <- forAll (Gen.list (Range.singleton (length names)) genText)
  let fields = zipWith (\n v -> (n, eString v)) names vals
  record_ fields `evalsTo` record_ fields

prop_evalProject :: Property
prop_evalProject = property $ do
  names <- forAll genFieldNames
  vals <- forAll (Gen.list (Range.singleton (length names)) genText)
  (target, expected) <- forAll (Gen.element (zip names vals))
  let fields = zipWith (\n v -> (n, eString v)) names vals
  project_ (record_ fields) target `evalsTo` eString expected

prop_projectForcesField :: Property
prop_projectForcesField = property $ do
  n <- forAll genIdent
  a <- forAll genText
  b <- forAll genText
  project_ (record_ [(n, concat_ (eString a) (eString b))]) n `evalsTo` eString (a <> b)

prop_recordEqWidth :: Property
prop_recordEqWidth = property $ do
  names <- forAll genFieldNames
  extra <- forAll (Gen.filter (`notElem` names) genIdent)
  let fields = [(n, eString (Ident.toText n)) | n <- names]
  let narrow = record_ fields :: Term Sig Ident
  let wide = record_ (fields <> [(extra, eString "extra")])
  assert (not (eqTerm narrow wide))

prop_renderRecord :: Property
prop_renderRecord = withTests 1 . property $
  renderTop (project_ (record_ [("a", eString "x"), ("b", eString "y")]) "b")
    === "{a = \"x\", b = \"y\"}.b"

prop_renderRecordTy :: Property
prop_renderRecordTy = withTests 1 . property $
  renderTop (lam "r" (TRecord (Map.fromList [("a", TString)])) (project_ (var "r") "a"))
    === "fun (v%0 : {a : string}). v%0.a"

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
      , testPropertyNamed "applying a non-function is an error" "prop_evalNonFunction" prop_evalNonFunction
      , testPropertyNamed "projecting a missing field is an error" "prop_evalMissingField" prop_evalMissingField
      ]
  , testGroup "types"
      [ testPropertyNamed "quantified types compare up to alpha-equivalence" "prop_tyAlphaEq" prop_tyAlphaEq
      , testPropertyNamed "prints types with minimal parentheses" "prop_renderTyPrec" prop_renderTyPrec
      ]
  , testGroup "recursive types"
      [ testPropertyNamed "string lists typecheck at their mu type" "prop_typecheckFold" prop_typecheckFold
      , testPropertyNamed "unfold typechecks at the unrolling" "prop_typecheckUnfold" prop_typecheckUnfold
      , testPropertyNamed "unfold cancels fold" "prop_evalUnfoldFold" prop_evalUnfoldFold
      , testPropertyNamed "unfold of a non-fold is an error" "prop_evalUnfoldNonFold" prop_evalUnfoldNonFold
      ]
  , testGroup "existentials"
      [ testPropertyNamed "unpack cancels pack" "prop_evalUnpackPack" prop_evalUnpackPack
      , testPropertyNamed "unpack of a non-pack is an error" "prop_evalUnpackNonPack" prop_evalUnpackNonPack
      ]
  , testGroup "universals"
      [ testPropertyNamed "type abstraction generalizes" "prop_typecheckTyLam" prop_typecheckTyLam
      , testPropertyNamed "shadowed type binders stay distinct" "prop_typecheckTyLamShadow" prop_typecheckTyLamShadow
      , testPropertyNamed "type application instantiates" "prop_evalTyApp" prop_evalTyApp
      , testPropertyNamed "type application of a non-abstraction is an error" "prop_evalTyAppNonTyLam" prop_evalTyAppNonTyLam
      ]
  , testGroup "stdlib"
      [ testPropertyNamed "stdlib entries have their advertised types" "prop_stdlibTypes" prop_stdlibTypes
      , testPropertyNamed "join concatenates" "prop_stdlibJoin" prop_stdlibJoin
      , testPropertyNamed "append concatenates lists" "prop_stdlibAppend" prop_stdlibAppend
      , testPropertyNamed "map maps" "prop_stdlibMap" prop_stdlibMap
      , testPropertyNamed "flatten flattens" "prop_stdlibFlatten" prop_stdlibFlatten
      ]
  , testGroup "rendering"
      [ testPropertyNamed "freshens bound names" "prop_renderApp" prop_renderApp
      ]
  , testGroup "records"
      [ testPropertyNamed "record of strings is a TRecord in insertion order" "prop_typecheckRecord" prop_typecheckRecord
      , testPropertyNamed "projecting a field yields its type" "prop_typecheckProject" prop_typecheckProject
      , testPropertyNamed "projecting a missing field is a type error" "prop_typecheckProjectMissing" prop_typecheckProjectMissing
      , testPropertyNamed "records are values" "prop_evalRecord" prop_evalRecord
      , testPropertyNamed "projection selects the right field" "prop_evalProject" prop_evalProject
      , testPropertyNamed "projection evaluates the field" "prop_projectForcesField" prop_projectForcesField
      , testPropertyNamed "records with extra fields are unequal" "prop_recordEqWidth" prop_recordEqWidth
      , testPropertyNamed "prints record literals and projection" "prop_renderRecord" prop_renderRecord
      , testPropertyNamed "prints record types" "prop_renderRecordTy" prop_renderRecordTy
      ]
  ]
