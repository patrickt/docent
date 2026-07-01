{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.IORef
import System.Exit (exitFailure, exitSuccess)

import Docent.Sum (Term, var)
import Docent.Type (Ty (..))
import Docent.Algebra (typecheck, eqTerm)
import Docent.Syntax.StrLit (eString, concat_)
import Docent.Syntax.Prog (lam, app, let_)
import Docent.Lang (Sig, eval)

check :: IORef Int -> String -> Bool -> IO ()
check failures name ok =
  if ok then putStrLn ("ok   - " <> name)
        else modifyIORef' failures (+ 1) >> putStrLn ("FAIL - " <> name)

main :: IO ()
main = do
  failures <- newIORef (0 :: Int)
  let ck = check failures

  -- typecheck of a string literal is TString
  ck "typecheck EString" (typecheck (const (error "free")) (eString "sup" :: Term Sig String) == Right TString)

  -- eval of a string literal is itself
  ck "eval EString" (eqTerm (eval (eString "sup")) (eString "sup" :: Term Sig String))

  -- eval of concat concatenates
  ck "eval Concat"
     (eqTerm (eval (concat_ (eString "hello") (eString " world")))
             (eString "hello world" :: Term Sig String))

  -- let x = "a" in x + ("b" + x)  typechecks to TString and evals to "aba"
  let letProg :: Term Sig String
      letProg = let_ "x" (eString "a")
                     (concat_ (var "x") (concat_ (eString "b") (var "x")))
  ck "typecheck let" (typecheck (const (error "free")) letProg == Right TString)
  ck "eval let"      (eqTerm (eval letProg) (eString "aba"))

  -- (\x:string. x) "z"  typechecks to TString and evals to "z"
  let appProg :: Term Sig String
      appProg = app (lam "x" TString (var "x")) (eString "z")
  ck "typecheck app" (typecheck (const (error "free")) appProg == Right TString)
  ck "eval app"      (eqTerm (eval appProg) (eString "z"))

  n <- readIORef failures
  if n == 0 then exitSuccess else exitFailure
