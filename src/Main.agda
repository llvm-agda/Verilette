module Main where

open import Javalette.IOLib
open import Javalette.AST using (printProg)
open import Javalette.Parser using (Err; parseProg)
open import Data.String
open import TypeChecker
open import DeSugar
--open import Data.Sum.Effectful.Left String renaming (monad to monadSum)
open import Data.Sum.Base
open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit


-- {-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified System.IO as IO #-}
{-# FOREIGN GHC import qualified System.IO #-}
-- {-# FOREIGN GHC import qualified System.IO.Handle.Text #-}

postulate
  FileHandle   : Set
  stdout       : FileHandle
  stderr       : FileHandle
  stdin        : FileHandle
  hPutStrLn    : FileHandle → String → IO ⊤
  hGetLine     : FileHandle → IO String
  hGetContents : FileHandle → IO String
{-# COMPILE GHC stderr       = IO.stderr #-}
{-# COMPILE GHC stdout       = IO.stdout #-}
{-# COMPILE GHC stdin        = IO.stdin #-}
{-# COMPILE GHC FileHandle   = type System.IO.Handle #-}
{-# COMPILE GHC hPutStrLn    = Text.hPutStrLn #-}
{-# COMPILE GHC hGetLine     = Text.hGetLine #-}
{-# COMPILE GHC hGetContents = Text.hGetContents #-}

catchError : {A : Set} → TCM A → IO ⊤
catchError (inj₁ x) = do hPutStrLn stderr "ERROR"
                         exitFailure
catchError (inj₂ y) = hPutStrLn stderr "OK"


main : IO ⊤
main = do
  contents ← hGetContents stdin
  Err.ok result ← return (parseProg contents) where
    Err.bad _ → do hPutStrLn stderr "ERROR"
                   exitFailure
  catchError (typeCheck builtin result)
