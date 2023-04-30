{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Product using (_×_; _,_; ∃) renaming (proj₁ to fst; proj₂ to snd)

open import Data.Nat

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Javalette.AST using (Type; String) renaming (Ident to Id); open Type
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; map)
open import TypedSyntax Id

open import Data.Empty using (⊥)

module Code where

Label : Set
Label = Id


data Ptr (T : Type) : Set where
  ptr : Id → Ptr T 


data Operand (T : Type) : Set where
  const : toSet T → Operand T
  var   : (id : Id) → Operand T

data Instruction : (T : Type) → Set where
  arith  : Num T → ArithOp → (x y : Operand T) → Instruction T
  alloc  : (T : Type) → Instruction T
  load   : Ptr T → Instruction T
  store  : Operand T → Ptr T → Instruction void
  call   : Ptr (fun T Ts) → TList Operand Ts → Instruction T
  jmp    : (l : Label) → Instruction void
  branch : Operand bool → (t f : Label) → Instruction void
  ret    : Return Operand T → Instruction T
  label  : Label → Instruction void
  -- TODO more operations

data Block' : Set where
  [] : Block'
  _∷_ : Instruction T → Block' → Block'
  _:=_∷_ : Operand T → Instruction T → Block' → Block'
  

record FunDef (Σ : SymbolTab) (ts : List Type) (T : Type) : Set  where
  field
    idents : List Id

  params = zip idents ts

  field
    body      : Block'
    -- hasEntry  : (Id.ident "entry" , params) ∈ ℓ
    voidparam : All (_≢ void) ts
    uniqueParams   : Unique params



-- record Program : Set where
--   field
--     BuiltIn : SymbolTab
--     Defs    : SymbolTab
--   Σ' = BuiltIn ++ Defs

--   field
--     hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
--     hasDefs    : FunList Σ' Defs
--     uniqueDefs : Unique Σ'
