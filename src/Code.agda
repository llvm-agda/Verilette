{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Product using (_×_; _,_; ∃) renaming (proj₁ to fst; proj₂ to snd)

open import Data.Nat
open import Data.String using (String)

open import Agda.Builtin.Bool  using (Bool)
open import Agda.Builtin.Int   using (Int)
open import Agda.Builtin.Float using (Float)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Javalette.AST using (RelOp) renaming (Ident to Id)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; map)
open import TypedSyntax Id hiding (toSet; T; Ts; FunType; SymbolTab; *)

open import Data.Empty using (⊥)

module Code where

Label : Set
Label = Id

data Type : Set where
  lint : ℕ → Type  -- i n -llvm-> i(n+1)
  float : Type
  void : Type
  _* : Type → Type
  fun : Type → List Type → Type

variable
  T  : Type
  Ts : List Type

toSet : Type → Set
toSet (lint zero)    = Bool
toSet (lint (suc _)) = Int
toSet float  = Float
toSet _ = ⊥


data FirstClass : Type → Set where
  lint : ∀ n → FirstClass (lint n)
  float : FirstClass float

pattern i1  = lint 0
pattern i8  = lint 7
pattern i32 = lint 31

FunType : Set
FunType = ((List Type) × Type)

SymbolTab : Set
SymbolTab = List (Id × FunType)


data Operand (T : Type) : Set where
  const  : toSet T → Operand T
  local  : (id : Id) → Operand T
  global : (id : Id) → Operand T

data Instruction : (T : Type) → Set where
  arith  : FirstClass T → ArithOp → (x y : Operand T) → Instruction T
  cmp    : FirstClass T → RelOp   → (x y : Operand T) → Instruction i1
  srem   : (x y : Operand i32) → Instruction i32 -- signed modulo
  alloc  : (T : Type) → Instruction (T *)
  load   : Operand (T *) → Instruction T
  store  : Operand T → Operand (T *) → Instruction void
  call   : Operand (fun T Ts) → TList Operand Ts → Instruction T
  getStr : (len : ℕ) → Id → Instruction (i8 *) -- getElemPtr specified to Strings
  phi    : List (Operand T × Label) → Instruction T

  -- Terminators
  jmp    : (l : Label) → Instruction void
  branch : Operand i1 → (t f : Label) → Instruction void
  vret   : Instruction void
  ret    : Operand T → Instruction void

  label  : Label → Instruction void

data Code : Set where
  [] : Code
  _∷_    :             Instruction T → Code → Code
  _:=_∷_ : Operand T → Instruction T → Code → Code
  

record FunDef (Σ : SymbolTab) (Ts : List Type) (T : Type) : Set  where
  field
    idents : List Id

  params = zip idents Ts

  field
    body      : Code
    -- hasEntry  : (Id.ident "entry" , params) ∈ ℓ
    -- voidparam : All (_≢ void) Ts
    -- uniqueParams   : Unique params


FunList' : (Σ' Σ : SymbolTab) → Set
FunList' Σ' = TList (λ (_ , (ts , t)) → FunDef Σ' ts t)

record llvmProgram : Set where
  field
    BuiltIn : SymbolTab
    Defs    : SymbolTab
  Σ' = BuiltIn ++ Defs

  field
    -- hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
    Strings    : List (Id × String)
    hasDefs    : FunList' Σ' Defs
    -- uniqueDefs : Unique Σ'
