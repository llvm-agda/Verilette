{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Javalette.AST using (Type; String) renaming (Ident to Id)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; map)
open import TypedSyntax

module Code where


-- Simplified subset
-- xs ⊆ ys if ys = x₁ : x₂ : ... : xs
data _⊆_ (xs : List A) : (ys : List A) → Set where
  eq  : xs ⊆ xs
  sub : xs ⊆ ys → xs ⊆ (y ∷ ys)

lemma⊆ : (x ∷ xs) ⊆ ys → xs ⊆ ys
lemma⊆ {_} {x} {xs} {.(x ∷ xs)} eq = sub eq
lemma⊆ {_} {x} {xs} {.(_ ∷ _)} (sub p) = sub (lemma⊆ p)

trans⊆ : {as bs cs : List A} → as ⊆ bs → bs ⊆ cs → as ⊆ cs
trans⊆ eq q = q
trans⊆ (sub p) q = trans⊆ p (lemma⊆ q)


Label : Set
Label = Id

LabelTab : Set
LabelTab = List (Label × Block)


data Ptr (T : Type) : Set where
  ptr : Id → Ptr T 


data Operand (T : Type) (Δ : Block) : Set where
  const : toSet T → Operand T Δ 
  var   : (id : Id) → (id , T) ∈ Δ → Operand T Δ 

data Instruction (Δ : Block) : (T : Type) → Set where
  arith : Num T → ArithOp → Operand T Δ₁ → {Δ₁ ⊆ Δ₂} → Operand T Δ₂ → {Δ₂ ⊆ Δ} → Instruction Δ T
  load  : Ptr T → Instruction Δ T
  store : Operand T Δ → Ptr T → Instruction Δ void
  -- TODO more operations
  

data Block' (Δ : Block) : (Δ' : Block) → Set where
  [] : Block' Δ Δ
  _∷_    : Instruction Δ T → Block' Δ Δ' → Block' Δ Δ'
  _:=_∷_ : (id : Id) → Instruction Δ T → {id ∉ Δ} → Block' ((id , T) ∷ Δ)  Δ' → Block' Δ Δ'

block'⊆ : Block' Δ Δ' → Δ ⊆ Δ'
block'⊆ [] = eq
block'⊆ (_ ∷ xs) = block'⊆ xs
block'⊆ (id := x ∷ xs) = lemma⊆ (block'⊆ xs)

uniqueBlock' : Block' Δ Δ' → Unique Δ → Unique Δ'
uniqueBlock' [] p = p
uniqueBlock' (x ∷ xs) p = uniqueBlock' xs p
uniqueBlock' b@(_:=_∷_ id x {p'} xs) p = uniqueBlock' xs (uniqueSuc p' p)


module Body (T : Type) (ℓ : LabelTab) where

  data Jumpable (Δ : Block) (l : Label) : Set where
    jumpable : (Δ' : Block) → Δ' ⊆ Δ → (l , Δ') ∈ ℓ → Jumpable Δ l

  data Terminator (Δ : Block) : Set where
    ret    : Return (λ t → Operand t Δ) T → Terminator Δ
    jmp    : (l : Label) → Jumpable Δ l → Terminator Δ
    branch : Operand bool Δ → (t f : Label) → Jumpable Δ t → Jumpable Δ f → Terminator Δ


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
    body      : TList (λ (l , b) → BasicBlock T ℓ b) ℓ
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
