module Main where

open import Javalette.IOLib
open import Javalette.AST using (printProg)
open import Javalette.Parser using (Err; parseProg)
open import TypeChecker
open import DeSugar
--open import Data.Sum.Effectful.Left String renaming (monad to monadSum)
open import Data.Sum.Base


catchError : {A : Set} → TCM A → IO ⊤
catchError (inj₁ x) = putStrLn x
catchError (inj₂ y) = putStrLn "TypeCheck successful"

main : IO ⊤
main = do
  file ∷ [] ← getArgs where
    _ → do
      putStrLn "usage: Main <SourceFile>"
      exitFailure
  Err.ok result ← parseProg <$> readFiniteFile file where
    Err.bad msg → do
      putStrLn "PARSE FAILED\n"
      putStrLn (stringFromList msg)
      exitFailure
  putStrLn "PARSE SUCCESSFUL\n"
  catchError (typeCheck result)

