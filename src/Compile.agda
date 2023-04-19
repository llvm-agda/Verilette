
open import Data.Product using (_×_; _,_) renaming (Σ to Σ')
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
    {startScope endScope} : Block
    block : Block' startScope endScope


data VarGen (Δ : Block) : Set where
  varGen : (id : Id) → id ∉ Δ → VarGen Δ

-- There exist some v Δ' that can be generated from Δ
data ∃ (Δ : Block) (v : Block → Set) : Set where
    bb : (VarGen Δ') → Block' Δ Δ' → v Δ' → ∃ Δ v


buildVarGen : Block → Set
buildVarGen Δ = {t : Type} → VarGen Δ → Σ' Id (λ id → VarGen ((id , t) ∷ Δ))

testVarGen : VarGen [] 
testVarGen = varGen (ident "t") [] 

modifyVarGen : buildVarGen Δ
modifyVarGen (varGen id x) = id , (varGen id {!!})


-- | Compiler monad
CM : Ctx → Set → Set
CM Γ = State (CompileState Γ)
  
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

newTmp : (Δ : Block) → CM Γ (Σ' Id (_∉ Δ))
newTmp = {!!}

bindTmp : {T : Type} → (Δ : Block) → Instruction Δ T → CM Γ (∃ Δ (Operand T))
bindTmp {T = T} Δ i = do tmp , p ← newTmp Δ
                         pure (bb {!!} (_:=_∷_ tmp i {p} []) (var tmp (here refl)))

emit : Block' Δ Δ' → Instruction Δ' T → CM Γ (∃ Δ (Operand T))
emit {_} {Δ'} {T} b i = do bb gen b' tmp ← bindTmp Δ' i
                           pure (bb {!!} (b >:> b') tmp)

lookupPtr' : ∀ {id} → BlockList Δ → (id , t) ∈ Δ → Ptr t
lookupPtr' (x :+ b) (here refl) = x
lookupPtr' (_ :+ b) (there x)   = lookupPtr' b x

lookupPtr : ∀ {id} → CtxList Γ → (id , t) ∈' Γ → Ptr t
lookupPtr (x :+ xs) (here p)  = lookupPtr' x p
lookupPtr (x :+ xs) (there s) = lookupPtr xs s

lookupPtrCM : ∀ {id} → (id , t) ∈' Γ → CM Γ (Ptr t)
lookupPtrCM p = gets (λ s → lookupPtr (ctxList s) p)


module _ (T : Type) (Σ : SymbolTab) (ℓ : LabelTab) where
  open Valid T Σ
  open Body T ℓ 
  open Typed
  
module _ where
  open Typed

  compileExp : (gen : VarGen Δ) → Exp Σ Γ T → CM Γ (∃ Δ (Operand T))
  compileExp gen (EValue x)        = pure (bb {!!} [] (const x))
  compileExp gen (EId id x)        = do p ← lookupPtrCM x
                                        emit [] (load p)
  compileExp gen (EAPP id x x₁)    = {!!}
  compileExp gen (EArith q x op y) = do bb gen'  b1 x' ← compileExp gen  x
                                        bb gen'' b2 y' ← compileExp gen' y
                                        emit (b1 >:> b2) (arith q op x' {block'⊆ b2} y' {eq})
  compileExp gen (EMod x x₁)       = {!!}
  compileExp gen (EOrd q x op y)   = {!!}
  compileExp gen (EEq  q x op y)   = {!!}
  compileExp gen (ELogic x op y)   = {!!}
  compileExp gen (ENeg q x)        = {!!}
  compileExp gen (ENot x)          = {!!}
  compileExp gen (EStr x)          = {!!}

