--show-implicit
open import Data.Product using (_×_; _,_) renaming (Σ to Σ'; ∃ to ∃')
open import Data.Sum using (_⊎_) renaming (inj₁ to left; inj₂ to right)
open import Data.List using (List; _∷_ ; [] ; zip ; map)

open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_)

open import Function using (_$_)

open import Data.String using () renaming (_++_ to _++s_)
open import Data.Nat.Show using () renaming (show to showℕ)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong)
open import Relation.Nullary.Negation using (¬_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Effect.Monad.State.Indexed
import Effect.Monad.Identity as Identity
open import Effect.Monad.Indexed

open import Code
open import TypedSyntax ℕ hiding (+; <) -- Using ℕ as Id
open import Javalette.AST using (Type; String); open Type

module CompileIndexed where

private
  variable
    Ts : List Type 
    v  : List Type 
    v' : List Type 
    w  : List Type 

BlockList : Block → Set
BlockList Δ = TList (λ (id , t) → Ptr t) Δ

CtxList : Ctx → Set
CtxList Γ = TList BlockList  Γ 

SymTab : SymbolTab → Set
SymTab Σ = TList (λ (id , (ts , t)) → Def Σ ts t) Σ

length : List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)


toBlock : List Type → Block
toBlock [] = []
toBlock (T ∷ Ts) = (length Ts , T) ∷ toBlock Ts

lengthToBlock : length v ≡ length (toBlock v)
lengthToBlock {[]} = refl
lengthToBlock {x ∷ v} = cong suc (lengthToBlock {v})

lemmaToBlock : {Ts : List Type} → toBlock (T ∷ Ts) ≡ (length Ts , T) ∷ toBlock Ts
lemmaToBlock = refl

lemmaSuc : {n : ℕ} → suc n ≢ n
lemmaSuc () 

-- Solve by proving that toBlock returns a sorted list?
lemmaNextVar : (Ts : List Type) → length Ts ∉ toBlock Ts
lemmaNextVar [] = []
lemmaNextVar (x ∷ Ts) = (λ p → lemmaSuc p) ∷ {!!}

uniqueToBlock : Unique (toBlock v)
uniqueToBlock {[]} = unique[]
uniqueToBlock {x ∷ Ts} = uniqueSuc (lemmaNextVar Ts) (uniqueToBlock {Ts})


record CMState (v w : List Type) : Set where
  constructor cMS
  field 
    block : Block' (toBlock v) (toBlock w)

emptyState : CMState v v
emptyState = cMS []

_>:>_ : Block' Δ Δ'  → Block' Δ' Δ'' → Block' Δ Δ''
[] >:> xs = xs
(x ∷ xs) >:> ys = x ∷ (xs >:> ys)
(_:=_∷_ id x {p} xs) >:> ys = _:=_∷_ id x {p} (xs >:> ys)

_>:>'_ : CMState v w → CMState w v' → CMState v v'
cMS block >:>' cMS block₁ = cMS (block >:> block₁)

data CM (v : List Type) (w : List Type) (A : Set) : Set where
  cM : (s : CMState v w) → (a : A) → CM v w A

open RawIMonad {{...}}

instance
  CM'Monad : RawIMonad CM
  RawIMonad.return CM'Monad x = cM emptyState x
  (CM'Monad RawIMonad.>>= cM s a) f with f a
  ... | cM s₁ a₁ = cM (s >:>' s₁) a₁


lookupPtr' : ∀ {id} → BlockList Δ → (id , t) ∈ Δ → Ptr t
lookupPtr' (x :+ b) (here refl) = x
lookupPtr' (_ :+ b) (there x)   = lookupPtr' b x

lookupPtr : ∀ {id} → CtxList Γ → (id , t) ∈' Γ → Ptr t
lookupPtr (x :+ xs) (here p)  = lookupPtr' x p
lookupPtr (x :+ xs) (there s) = lookupPtr xs s

emit : Instruction (toBlock v) T → CM v (T ∷ v) (Operand T (toBlock (T ∷ v)))
emit {v = v}x = let id = length v
                in cM (cMS (_:=_∷_ id x {lemmaNextVar v} []))
                      (var id (here refl))

with⊆ : CM v w A → CM v w ((toBlock v ⊆ toBlock w) × A)
with⊆ (cM (cMS s) a) = cM (cMS s) (block'⊆ s , a)
  
module _ where
  open Typed

  newList : (e : Exp Σ Γ T) → List Type → List Type
  newList (EValue x) v = v
  newList (EId {T} id x) v = T ∷ v
  newList (EArith {T} p x _ y) v = T    ∷ newList y (newList x v)
  newList (EMod         x   y) v = int  ∷ newList y (newList x v)
  newList (EOrd   {T} P x _ y) v = T    ∷ newList y (newList x v)
  newList (EEq    {T} P x _ y) v = T    ∷ newList y (newList x v)
  newList (ELogic       x _ y) v = bool ∷ newList y (newList x v)
  newList (ENeg {T} x e) v = T ∷ newList e v
  newList (ENot e) v = bool ∷ newList e v
  newList (EStr x) v = void ∷ v -- Not sure
  newList (EAPP {_} {T} id es x₁) v = T ∷ foldr es
    where foldr : TList (Exp Σ Γ) Ts → List Type
          foldr NIL = v
          foldr (x :+ es) = newList x (foldr es)

  compileExp : {v : List Type} → (e : Exp Σ Γ T) → CM v (newList e v) (Operand T (toBlock (newList e v)))
  compileExp (EValue x) = pure (const x)
  compileExp (EId id x) = {!!}
  compileExp (EArith p x op y) = do x' ← compileExp x
                                    py , y' ← with⊆ $ compileExp y
                                    emit (arith p op x' {py}  y' {eq})
  compileExp (EMod e e₁) = {!!}
  compileExp (EOrd x e x₁ e₁) = {!!}
  compileExp (EEq x e x₁ e₁) = {!!}
  compileExp (ELogic e x e₁) = {!!}
  compileExp (ENeg x e) = {!!}
  compileExp (ENot e) = {!!}
  compileExp (EStr x) = {!!}
  compileExp (EAPP id es x₁) = {!!}
  
