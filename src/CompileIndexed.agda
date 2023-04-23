open import Data.Product using (_×_; _,_; ∃) 
open import Data.List using (List; _∷_ ; [] ; zip ; map)

open import Agda.Builtin.Int using (negsuc) 
open import Data.Nat using (ℕ; suc)
open import Function using (_$_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Effect.Monad.Indexed

open import Code
open import TypedSyntax ℕ hiding (+; <) -- Using ℕ as Id
open import Javalette.AST using (Type); open Type

module CompileIndexed where

private
  variable
    v  : List Type 
    v' : List Type 
    w  : List Type 

BlockList : Block → Set
BlockList Δ = TList (λ (id , t) → Ptr t) Δ

CtxList : Ctx → Set
CtxList Γ = TList BlockList  Γ 

SymTab : SymbolTab → Set
SymTab Σ = TList (λ (id , (ts , t)) → Ptr (fun t ts)) Σ

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

data CM (v w : List Type) (A : Set) : Set where
  cM : (s : CMState v w) → (a : A) → CM v w A

emptyState : CMState v v
emptyState = cMS []

_>:>_ : Block' Δ Δ'  → Block' Δ' Δ'' → Block' Δ Δ''
[] >:> xs = xs
(x ∷ xs) >:> ys = x ∷ (xs >:> ys)
(_:=_∷_ id x {p} xs) >:> ys = _:=_∷_ id x {p} (xs >:> ys)

_>:>'_ : CMState v w → CMState w v' → CMState v v'
cMS block >:>' cMS block₁ = cMS (block >:> block₁)

open RawIMonad {{...}}

instance
  CM'Monad : RawIMonad CM
  RawIMonad.return CM'Monad x = cM emptyState x
  (CM'Monad RawIMonad.>>= cM s a) f with f a
  ... | cM s₁ a₁ = cM (s >:>' s₁) a₁


negOne : Num T → toSet T
negOne NumInt    = negsuc 0 -- -1
negOne NumDouble = -1.0

lookupPtr' : BlockList Δ → (id , t) ∈ Δ → Ptr t
lookupPtr' (x :+ b) (here refl) = x
lookupPtr' (_ :+ b) (there x)   = lookupPtr' b x

lookupPtr : CtxList Γ → (id , t) ∈' Γ → Ptr t
lookupPtr (x :+ xs) (here p)  = lookupPtr' x p
lookupPtr (x :+ xs) (there s) = lookupPtr xs s

-- not sure if functions are Ptr
lookupFun : SymTab Σ → (id , Ts , T) ∈ Σ → Ptr (fun T Ts)
lookupFun (x :+ _)  (here refl) = x
lookupFun (_ :+ xs) (there p)   = lookupFun xs p


emit : Instruction (toBlock v) T → CM v (T ∷ v) (Operand T (toBlock (T ∷ v)))
emit {v = v}x = let id = length v
                in cM (cMS (_:=_∷_ id x {lemmaNextVar v} []))
                      (var id (here refl))

with⊆ : CM v w A → CM v w ((toBlock v ⊆ toBlock w) × A)
with⊆ (cM (cMS s) a) = cM (cMS s) (block'⊆ s , a)


module _ where
  open Typed
  
  newList : (e : Exp Σ Γ T) → List Type → List Type
  foldNewList : TList (Exp Σ Γ) Ts → List Type → List Type
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
  newList (EAPP {_} {T} id es x₁) v = T ∷ foldNewList es v

  foldNewList NIL v = v
  foldNewList (x :+ es) v = newList x (foldNewList es v)
  

module _ (σ : SymTab Σ) (γ : CtxList Γ) where
  open Typed Σ 

  compileExp : {v : List Type} → (e : Exp Γ T) → CM v (newList e v) (Operand T (toBlock (newList e v)))
  compileExp (EValue x) = pure (const x)
  compileExp (EId id x) = emit (load (lookupPtr γ x))
  compileExp (EArith p x op y) = do x' ← compileExp x
                                    py , y' ← with⊆ $ compileExp y
                                    emit (arith p op x' {py}  y' {eq})
  compileExp (EMod e e₁) = {!!}
  compileExp (EOrd x e x₁ e₁) = {!!}
  compileExp (EEq x e x₁ e₁) = {!!}
  compileExp (ELogic e x e₁) = {!!}
  compileExp (ENeg p e) = do e' ← compileExp e
                             emit (arith p * e' {eq} (const (negOne p)) {eq})
  compileExp (ENot e) = {!!}
  compileExp (EStr x) = {!!}
  compileExp (EAPP id es p) = do os ← foldr es
                                 emit (call (lookupFun σ p) os)
    where
      mapTList : {v w : A → Set} → (∀ {x} → v x → w x) → TList v xs → TList w xs
      mapTList f NIL = NIL
      mapTList f (x :+ xs) = f x :+ mapTList f xs

      foldr : (es : TList (Exp Γ) Ts) → CM v (foldNewList es v) (TList (λ T → ∃ (λ Δ' → (Δ' ⊆ toBlock (foldNewList es v)) × Operand T Δ')) Ts)
      foldr NIL       = pure NIL
      foldr (e :+ es) = do es' ← foldr es
                           p , e' ← with⊆ (compileExp e)
                           let es'' = mapTList (λ (_ , p' , e') → (_ , trans⊆ p' p  , e')) es'
                           pure ((_ , eq , e') :+ es'')
  
