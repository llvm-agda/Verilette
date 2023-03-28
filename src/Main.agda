module Main where

open import Javalette.IOLib
open import Javalette.AST using (printProg)
open import Javalette.Parser using (Err; parseProg)
open import Data.String
open import TypeChecker
open import DeSugar
--open import Data.Sum.Effectful.Left String renaming (monad to monadSum)
open import Data.Sum.Base


catchError : {A : Set} → TCM A → IO ⊤
catchError (inj₁ x) = do putStrLn ("ERROR" ++ x)
                         exitFailure
catchError (inj₂ y) = putStrLn "OK"

main : IO ⊤
main = do
  file ∷ [] ← getArgs where
    _ → do
      putStrLn "usage: Main <SourceFile>"
      exitFailure
  Err.ok result ← parseProg <$> readFiniteFile file where
    Err.bad msg → do
      putStrLn "ERROR"
      putStrLn "PARSER FAILED"
      putStrLn (stringFromList msg)
      exitFailure
  catchError (typeCheck builtin result)
