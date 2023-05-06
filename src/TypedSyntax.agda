module TypedSyntax (Id : Set) where

open import Agda.Builtin.Bool  using (Bool)
open import Agda.Builtin.Int   using (Int)
open import Agda.Builtin.Float using () renaming (Float to Double)

open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Javalette.AST using (Type; String) 
open Type 

variable
  A B : Set
  x y : A
  xs ys : List A


FunType : Set
FunType = ((List Type) × Type)

SymbolTab : Set
SymbolTab = List (Id × FunType)

Block : Set
Block = List (Id × Type)

Ctx : Set
Ctx = List Block

TList : (A → Set) → List A → Set
TList = All

variable
  T t : Type
  Ts ts : List Type
  Δ Δ' Δ'' Δ₁ Δ₂ : Block
  Γ Γ' : Ctx
  Σ : SymbolTab
  id : Id


infix 1 _∈_
_∈_ : (e : A) → List A → Set
e ∈ xs = Any (e ≡_) xs

_∉_ : {A : Set} (id : Id) → List (Id × A) → Set
id ∉ xs = All (λ (id' , _) → id ≢ id') xs

_∈'_ : (e : A) → List (List A) → Set
e ∈' xs = Any (e ∈_) xs

data Unique {A : Set} : (l : List (Id × A)) → Set where
  []  : Unique []
  _∷_ : ∀ {id xs x} → id ∉ xs → Unique xs → Unique ((id , x) ∷ xs)

--------------------------------------------------------------------------------
-- Basic defs


toSet : Type → Set
toSet bool = Bool
toSet int = Int
toSet doub = Double
toSet void = ⊥
toSet (fun t ts) = ⊥ -- toFun t ts
  where
    toFun : Type → List Type → Set
    toFun x [] = toSet x
    toFun x (x₁ ∷ xs) = toSet x₁ → toFun x xs

data LogicOp  : Set where && ||     : LogicOp
data EqOp     : Set where == !=     : EqOp
data OrdOp    : Set where < <= > >= : OrdOp
data ArithOp  : Set where + - * /   : ArithOp


data Eq : (T : Type) → Set where
  EqInt : Eq int
  EqBool : Eq bool
  EqDouble : Eq doub

data Ord : (T : Type) → Set where
  OrdInt : Ord int
  OrdDouble : Ord doub

data Num : (T : Type) → Set where
  NumInt : Num int
  NumDouble : Num doub

data Return (P : (Type → Set)) : Type -> Set where
  vRet : Return P void
  Ret : P t -> Return P t


--------------------------------------------------------------------------------
-- EXPRESSIONS AND STATEMENTS
module Typed (Σ : SymbolTab) where
  data Exp (Γ : Ctx) : Type → Set where
    EValue : toSet T  → Exp Γ T
    EId    : (id : Id) → (id , T) ∈' Γ → Exp Γ T
    EAPP   : (id : Id) → TList (Exp Γ) ts → (id , (ts , T)) ∈ Σ → Exp Γ T
    EArith : Num T   → Exp Γ T → ArithOp → Exp Γ T → Exp Γ T
    EMod   : Exp Γ int → Exp Γ int → Exp Γ int
    EOrd   : Ord T → Exp Γ T → OrdOp → Exp Γ T → Exp Γ bool
    EEq    : Eq T  → Exp Γ T → EqOp  → Exp Γ T → Exp Γ bool
    ELogic : Exp Γ bool → LogicOp → Exp Γ bool → Exp Γ bool
    ENeg   : Num T → Exp Γ T → Exp Γ T
    ENot   : Exp Γ bool → Exp Γ bool
    EStr   : String → Exp Γ void -- Hack to get string


module Valid (T : Type) (Σ : SymbolTab) where
  open Typed Σ

  mutual
    data Stm : (Γ : Ctx) → Set  where
      SExp    : Exp Γ void → Stm Γ
      SDecl   : (t : Type) → (id : Id) → toSet t → id ∉ Δ → Stm (Δ ∷ Γ)
      SAss    : (id : Id) → (e : Exp Γ t) → (id , t) ∈' Γ → Stm Γ
      SWhile  : Exp Γ bool  → Stms ([] ∷ Γ) → Stm Γ
      SBlock  : Stms ([] ∷ Γ) → Stm Γ
      SIfElse : Exp Γ bool → Stms ([] ∷ Γ) → Stms ([] ∷ Γ) → Stm Γ
      SReturn : Return (Exp Γ) T → Stm Γ

    nextCtx : {Γ : Ctx} → Stm Γ → Ctx
    nextCtx {.(_∷_) Δ Γ} (SDecl t id x _) = ((id , t) ∷ Δ) ∷ Γ
    nextCtx {Γ} (SExp x) = Γ
    nextCtx {Γ} (SAss id e x) = Γ
    nextCtx {Γ} (SWhile x x₁) = Γ
    nextCtx {Γ} (SBlock x) = Γ
    nextCtx {Γ} (SIfElse x x₁ x₂) = Γ
    nextCtx {Γ} (SReturn x) = Γ

    data Stms (Γ : Ctx) : Set where
      SEmpty  : Stms Γ
      _SCons_ : (s : Stm Γ) → Stms (nextCtx s) → Stms Γ

    lastCtx : Stms Γ → Ctx
    lastCtx {Γ} SEmpty = Γ
    lastCtx {Γ} (s SCons x) = lastCtx x

open Typed
open Valid

data returnStms {T Σ Γ} : (ss : Stms T Σ Γ) → Set
data returnStm  {  Σ Γ} : (s  : Stm  T Σ Γ) → Set where
  SReturn : {e : Return (Exp Σ Γ) T} → returnStm (SReturn e)
  SBlock  : {ss : Stms T Σ ([] ∷ Γ)} → returnStms ss → returnStm (SBlock ss)
  SIfElse : ∀ {e} → ∀ {s1 s2 : Stms T Σ ([] ∷ Γ)} → returnStms s1 → returnStms s2 → returnStm (SIfElse e s1 s2)
data returnStms where
  SHead : ∀ {s ss} → returnStm  s  → returnStms (s SCons ss)
  SCon  : ∀ {s ss} → returnStms ss → returnStms (s SCons ss)


record Def (Σ : SymbolTab) (Ts : List Type) (T : Type) : Set  where
  field
    idents : List Id

  params = zip idents Ts

  field
    body      : Stms T Σ (params ∷ [])
    voidparam : All (_≢ void) Ts
    unique    : Unique params
    return    : returnStms body


-- FunList contains a function parameterized by Σ' for each element in Σ.
FunList : (Σ' Σ : SymbolTab) → Set
FunList Σ' = TList (λ (_ , (ts , t)) → Def Σ' ts t)

record Program : Set where
  field
    BuiltIn : SymbolTab
    Defs    : SymbolTab
  Σ' = BuiltIn ++ Defs

  field
    -- hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
    hasDefs    : FunList Σ' Defs
    uniqueDefs : Unique Σ'
