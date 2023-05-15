module Main where

open import Javalette.IOLib
open import Javalette.AST using (printProg)
open import Javalette.Parser using (Err; parseProg)
open import Data.String
open import TypeChecker
open import TypeCheckerMonad using (TCM)
open import Compile using (compileProgram)
open import Print   using (pProgram)
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

main : IO ⊤
main = do
  contents ← hGetContents stdin
  Err.ok result ← return (parseProg contents) where
    Err.bad s → do hPutStrLn stderr "ERROR"
                   hPutStrLn stderr "Parse Failed"
                   exitFailure
  inj₂ y ← return (typeCheck builtin result) where
    inj₁ s → do hPutStrLn stderr "ERROR"
                hPutStrLn stderr s
                exitFailure
  hPutStrLn stdout (pProgram (compileProgram y))
  hPutStrLn stderr "OK"
