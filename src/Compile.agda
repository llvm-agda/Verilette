
open import Data.Product using (_×_; _,_) renaming (Σ to Σ'; ∃ to ∃')
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; map)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Effect.Monad
open import Effect.Monad.State

open import Code
open import TypedSyntax
open import Javalette.AST using (Type; String; ident) renaming (Ident to Id)

module Compile where

BlockList : Block → Set
BlockList Δ = TList (λ (id , t) → Ptr t) Δ

CtxList : Ctx → Set
CtxList Γ = TList BlockList  Γ 

SymTab : SymbolTab → Set
SymTab Σ = TList (λ (id , (ts , t)) → Def Σ ts t) Σ

record CompileState (Γ : Ctx) : Set where
  field
    ctxList : CtxList Γ
    startScope endScope : Block
    block : Block' startScope endScope


data VarGen (Δ : Block) : Set where
  varGen : (id : Id) → id ∉ Δ → VarGen Δ

-- There exist some v Δ' that can be generated from Δ
data ∃ (Δ : Block) (v : Block → Set) : Set where
    bb : (VarGen Δ') → Block' Δ Δ' → v Δ' → ∃ Δ v


buildVarGen : Block → Set
buildVarGen Δ = {t : Type} → VarGen Δ → Σ' Id (λ id → (id ∉ Δ) × VarGen ((id , t) ∷ Δ))


-- | Compiler monad
CM : Ctx → Set → Set
CM Γ = State (CompileState Γ)

record CM' (Γ : Ctx) (v : Block → Set) : Set where
  constructor cM' 
  field
    CMFun : (CompileState Γ → Σ' (CompileState Γ) (λ s → v (CompileState.endScope s))) 

  
open CompileState
open RawMonad {{...}} public 
open RawMonadState {{...}} public 
instance
  monadCM : {Γ : Ctx} → RawMonad (CM Γ)
  monadCM = monad

  monadStateCM : {Γ : Ctx} → RawMonadState (CompileState Γ) (CM Γ)
  monadStateCM = monadState

_>:>_ : Block' Δ Δ'  → Block' Δ' Δ'' → Block' Δ Δ''
[] >:> xs = xs
(x ∷ xs) >:> ys = x ∷ (xs >:> ys)
(_:=_∷_ id x {p} xs) >:> ys = _:=_∷_ id x {p} (xs >:> ys)

newTmp : buildVarGen Δ
newTmp = {!!}

bindTmp : {T : Type} → (gen : VarGen Δ) → Instruction Δ T → CM Γ (∃ Δ (Operand T))
bindTmp {T = T} gen i = do let tmp , p , gen' = newTmp {_} {T} gen
                           pure (bb gen' (_:=_∷_ tmp i {p} []) (var tmp (here refl)))

emit : (gen : VarGen Δ') → Block' Δ Δ' → Instruction Δ' T → CM Γ (∃ Δ (Operand T))
emit {_} {Δ'} {T} gen b i = do bb gen' b' tmp ← bindTmp gen i
                               pure (bb gen' (b >:> b') tmp)

emit' : CM' Γ (λ Δ → Instruction Δ T) → CM' Γ (Operand T)
emit' = {!!}

lookupPtr' : ∀ {id} → BlockList Δ → (id , t) ∈ Δ → Ptr t
lookupPtr' (x :+ b) (here refl) = x
lookupPtr' (_ :+ b) (there x)   = lookupPtr' b x

lookupPtr : ∀ {id} → CtxList Γ → (id , t) ∈' Γ → Ptr t
lookupPtr (x :+ xs) (here p)  = lookupPtr' x p
lookupPtr (x :+ xs) (there s) = lookupPtr xs s

lookupPtrCM : ∀ {id} → (id , t) ∈' Γ → CM Γ (Ptr t)
lookupPtrCM p = gets (λ s → lookupPtr (ctxList s) p)


-- runCM : VarGen Δ → CM Γ A → 

_>>='_ : {v w : Block → Set} → (VarGen Δ → ∃ Δ v) → (∀ {Δ'} → Δ ⊆ Δ' → v Δ' → VarGen Δ' → ∃ Δ w) → VarGen Δ → ∃ Δ w
(f >>=' g) x with f x
... | bb gen b v = g (block'⊆ b) v gen

-- _>>='_ : {v w : Block → Set} → CM' Γ v → (∀ {Δ} → v Δ → CM' Γ w) → CM' Γ w
-- cM' m >>=' f = cM' λ x → (λ (s , v) → (λ (cM' m') → m' s) (f v)) (m x)

pure' : {v : Block → Set} → (∀ {Δ} → v Δ) → CM' Γ v
pure' x = cM' (λ s → s , x)

module _ (T : Type) (Σ : SymbolTab) (ℓ : LabelTab) where
  open Valid T Σ
  open Body T ℓ 
  open Typed
  
module _ where
  open Typed

  compileExp' : Exp Σ Γ T → (gen : VarGen Δ) → ∃ Δ (Operand T)
  compileExp' (EValue x) = λ gen → bb gen [] (const x)
  compileExp' (EId id x) = {!!}
  compileExp' (EAPP id x x₁) = {!!}
  compileExp' (EArith p x op y) = compileExp' x >>=' (λ x₁ x₂ → {!? >>=' ?!})
  compileExp' (EMod e e₁) = {!!}
  compileExp' (EOrd x e x₁ e₁) = {!!}
  compileExp' (EEq x e x₁ e₁) = {!!}
  compileExp' (ELogic e x e₁) = {!!}
  compileExp' (ENeg x e) = {!!}
  compileExp' (ENot e) = {!!}
  compileExp' (EStr x) = {!!}

  compileExp : (gen : VarGen Δ) → Exp Σ Γ T → CM Γ (∃ Δ (Operand T))
  compileExp gen (EValue x)        = pure (bb gen [] (const x))
  compileExp gen (EId id x)        = do p ← lookupPtrCM x
                                        emit gen [] (load p)
  compileExp gen (EAPP id x x₁)    = {!!}
  compileExp gen (EArith q x op y) = do bb gen'  b1 x' ← compileExp gen  x
                                        bb gen'' b2 y' ← compileExp gen' y
                                        emit gen'' (b1 >:> b2) (arith q op x' {block'⊆ b2} y' {eq})
  compileExp gen (EMod x x₁)       = {!!}
  compileExp gen (EOrd q x op y)   = {!!}
  compileExp gen (EEq  q x op y)   = {!!}
  compileExp gen (ELogic x op y)   = {!!}
  compileExp gen (ENeg q x)        = {!!} -- do x' ← compileExp x
                                        -- testCM x' (λ x'' → ... )
                                        -- {!!}
  compileExp gen (ENot x)          = {!!}
  compileExp gen (EStr x)          = {!!}

