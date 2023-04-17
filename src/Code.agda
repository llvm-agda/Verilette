open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Javalette.AST using (Type; String) renaming (Ident to Id)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; map)
open import TypedSyntax

module Code where

Label : Set
Label = Id

LabelTab : Set
LabelTab = List (Label × Block)


Ptr : Set
Ptr = {!!}


data Operand (Δ : Block) (T : Type) : Set where
  const : toSet T → Operand Δ T
  var   : (id : Id) → (id , T) ∈ Δ → Operand Δ T

data Instruction (Δ : Block) : (T : Type) → Set where
  arith : Num T → ArithOp → Operand Δ T → Operand Δ T → Instruction Δ T
  store : Operand Δ T → Ptr → Instruction Δ void
  -- TODO more operations
  


-- Simplified subset
-- xs ⊆ ys if ys = x₁ : x₂ : ... : xs
data _⊆_ (xs : List A) : (ys : List A) → Set where
  eq  : xs ⊆ xs
  sub : xs ⊆ ys → xs ⊆ (y ∷ ys)


module Body (T : Type) (ℓ : LabelTab) where

  data Jumpable (Δ : Block) (l : Label) : Set where
    jumpable : (Δ' : Block) → Δ' ⊆ Δ → (l , Δ') ∈ ℓ → Jumpable Δ l

  data Terminator (Δ : Block) : Set where
    ret    : Return (Operand Δ) T → Terminator Δ
    jmp    : (l : Label) → Jumpable Δ l → Terminator Δ
    branch : Operand Δ bool → (t f : Label) → Jumpable Δ t → Jumpable Δ f → Terminator Δ

  data BasicBlock (Δ : Block) : Set where
    [_]    : Terminator Δ → BasicBlock Δ 
    _∷_    : Instruction Δ T → BasicBlock Δ → BasicBlock Δ 
    _:=_∷_ : (id : Id) → Instruction Δ T → {id ∉ Δ} → BasicBlock ((id , T) ∷ Δ) → BasicBlock Δ 


open Body

record FunDef (Σ : SymbolTab) (ts : List Type) (T : Type) : Set  where
  field
    idents : List Id

  params = zip idents ts

  field
    ℓ         : LabelTab
    body      : TList (BasicBlock T ℓ) (map snd ℓ)
    hasEntry  : (Id.ident "entry" , params) ∈ ℓ
    voidparam : All (_≢ void) ts
    uniqueParams   : Unique params
    uniqueLabelTab : Unique ℓ



-- record Program : Set where
--   field
--     BuiltIn : SymbolTab
--     Defs    : SymbolTab
--   Σ' = BuiltIn ++ Defs

--   field
--     hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
--     hasDefs    : FunList Σ' Defs
--     uniqueDefs : Unique Σ'
