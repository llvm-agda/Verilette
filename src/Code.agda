{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Product using (_×_; _,_; ∃) renaming (proj₁ to fst; proj₂ to snd)

open import Data.Nat
open import Data.String using (String)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Javalette.AST using (Type; RelOp) renaming (Ident to Id); open Type
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; map)
open import TypedSyntax Id

open import Data.Empty using (⊥)

module Code where

Label : Set
Label = Id


data Ptr (T : Type) : Set where
  ptr : Id → Ptr T 


data Operand (T : Type) : Set where
  const  : toSet T → Operand T
  local  : (id : Id) → Operand T
  global : (id : Id) → Operand T

data Instruction : (T : Type) → Set where
  arith  : Num T → ArithOp → (x y : Operand T) → Instruction T
  cmp    : RelOp → (x y : Operand T) → Instruction bool
  srem   : (x y : Operand int) → Instruction int -- signed modulo
  alloc  : (T : Type) → Instruction T
  load   : Ptr T → Instruction T
  store  : Operand T → Ptr T → Instruction void
  call   : Ptr (fun T Ts) → TList Operand Ts → Instruction T
  phi    : List (Operand T × Label) → Instruction T

  -- Terminators
  jmp    : (l : Label) → Instruction void
  branch : Operand bool → (t f : Label) → Instruction void
  ret    : Return Operand T → Instruction T

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
    voidparam : All (_≢ void) Ts
    uniqueParams   : Unique params


FunList' : (Σ' Σ : SymbolTab) → Set
FunList' Σ' = TList (λ (_ , (ts , t)) → FunDef Σ' ts t)

record llvmProgram : Set where
  field
    BuiltIn : SymbolTab
    Defs    : SymbolTab
  Σ' = BuiltIn ++ Defs

  field
    -- hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
    strings    : List (Id × String)
    hasDefs    : TList (λ (_ , ts , t) → FunDef Σ' ts t) Defs
    uniqueDefs : Unique Σ'
