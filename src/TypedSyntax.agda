module TypedSyntax where

import Data.Bool    as Bool
import Data.Integer as Int
import Data.Float   as Doub
import Data.Nat     as Nat

open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; reverse; [_])
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Javalette.AST using (Type; String) renaming (Ident to Id)
open Type


variable
  A B : Set
  x y : A
  xs ys : List A


FunType : Set
FunType = ((List Type) × Type)

SymbolTab : Set
SymbolTab = List (Id × FunType)

TypeTab : Set
TypeTab = List (Id × (Id × List (Id × Type)))



Block : Set
Block = List Type

Ctx : Set
Ctx = List Block

Params : ∀ {A} → List A → Set
Params = All (λ _ → Id)

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

Ptr = Nat.ℕ  -- What should be the type of Ptr?


toSet : Type → Set
toSet bool = Bool.Bool
toSet int = Int.ℤ
toSet doub = Doub.Float
toSet void = ⊥
toSet (array t) = Ptr
toSet (structT x) = Ptr
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
  EqStruct : ∀ {n} → Eq (structT n)

data Ord : (T : Type) → Set where
  OrdInt : Ord int
  OrdDouble : Ord doub

data Num : (T : Type) → Set where
  NumInt : Num int
  NumDouble : Num doub

data NonVoid (χ : TypeTab) : (T : Type) → Set where
  NonVoidInt    : NonVoid χ int
  NonVoidDoub   : NonVoid χ doub
  NonVoidBool   : NonVoid χ bool
  NonVoidArray  : NonVoid χ t → NonVoid χ (array t)
  NonVoidStruct : ∀ {n c fs} → (n , c , fs) ∈ χ → NonVoid χ (structT n)

data Basic (χ : TypeTab) : (T : Type) → Set where
  BasicInt   : Basic χ int
  BasicDoub  : Basic χ doub
  BasicBool  : Basic χ bool
  BasicStruct : ∀ {n c fs} → (n , c , fs) ∈ χ → Basic χ (structT n)


data Return (P : (Type → Set)) : Type -> Set where
  vRet : Return P void
  Ret : P t -> Return P t

data WFNew {T : Set} (E : Set) (w : T → T) : T → Set where
  nType  : (t : T)             → E → WFNew E w (w t)
  nArray : ∀ {t} → WFNew E w t → E → WFNew E w (w t)


--------------------------------------------------------------------------------
-- EXPRESSIONS AND STATEMENTS
module Typed (Σ : SymbolTab) (χ : TypeTab) where

  data Exp (Γ : Ctx) : Type → Set where
    EValue  : toSet T  → Exp Γ T
    EId     : T ∈' Γ → Exp Γ T
    EAPP    : (id : Id) → TList (Exp Γ) ts → (id , (ts , T)) ∈ Σ → Exp Γ T
    EArith  : Num T   → Exp Γ T → ArithOp → Exp Γ T → Exp Γ T
    EMod    : Exp Γ int → Exp Γ int → Exp Γ int
    EOrd    : Ord T → Exp Γ T → OrdOp → Exp Γ T → Exp Γ bool
    EEq     : Eq T  → Exp Γ T → EqOp  → Exp Γ T → Exp Γ bool
    ELogic  : Exp Γ bool → LogicOp → Exp Γ bool → Exp Γ bool
    EIdx    : Exp Γ (array t) → Exp Γ int → Exp Γ t
    EArray  : ∀ {t} → WFNew (Exp Γ int) array t → Exp Γ t
    EStruct : ∀ {n} → Exp Γ (structT n)
    ENull   : ∀ {n} → Exp Γ (structT n)
    ELength : Exp Γ (array t) → Exp Γ int
    EDeRef  : ∀ {n n' fs t c} → Exp Γ (structT n) → (n , c , fs) ∈ χ →  (n' , t) ∈ fs → Exp Γ t
    EPrintStr : String → Exp Γ void


module Valid (Σ : SymbolTab) (χ : TypeTab) (T : Type) where
  open Typed Σ χ

  mutual
    data Stm : (Γ : Ctx) → Set  where
      SExp    : Exp Γ void → Stm Γ
      SDecl   : (t : Type) → Exp (Δ ∷ Γ) t → Stm (Δ ∷ Γ)
      SAss    : (e : Exp Γ t) → t ∈' Γ → Stm Γ
      SAssIdx : (arr : Exp Γ (array t)) → (i : Exp Γ int) → Exp Γ t → Stm Γ
      SAssPtr : ∀ {fs f n c} → Exp Γ (structT n) → (n , c , fs) ∈ χ → (f , t) ∈ fs → Exp Γ t → Stm Γ
      SWhile  : Exp Γ bool  → Stms ([] ∷ Γ) → Stm Γ
      -- One could imagine replacing for with while, but that requires introducing new variables
      SFor    : Exp Γ (array t)  → Stms ([ t ] ∷ Γ) → Stm Γ
      SBlock  : Stms ([] ∷ Γ) → Stm Γ
      SIfElse : Exp Γ bool → Stms ([] ∷ Γ) → Stms ([] ∷ Γ) → Stm Γ
      SReturn : Return (Exp Γ) T → Stm Γ

    nextCtx : {Γ : Ctx} → Stm Γ → Ctx
    nextCtx {.(_∷_) Δ Γ} (SDecl t x) = (t ∷ Δ) ∷ Γ
    nextCtx {Γ} (SAssPtr e p q x) = Γ
    nextCtx {Γ} (SExp x)          = Γ
    nextCtx {Γ} (SAss e x)        = Γ
    nextCtx {Γ} (SAssIdx a i e)   = Γ
    nextCtx {Γ} (SWhile x x₁)     = Γ
    nextCtx {Γ} (SFor e ss)       = Γ
    nextCtx {Γ} (SBlock x)        = Γ
    nextCtx {Γ} (SIfElse _ _ _)   = Γ
    nextCtx {Γ} (SReturn x)       = Γ

    data Stms (Γ : Ctx) : Set where
      []  : Stms Γ
      _∷_ : (s : Stm Γ) → Stms (nextCtx s) → Stms Γ

    lastCtx : Stms Γ → Ctx
    lastCtx {Γ} [] = Γ
    lastCtx {Γ} (s ∷ x) = lastCtx x

open Typed
open Valid

data returnStms {T Σ χ Γ} : (ss : Stms Σ χ T Γ) → Set
data returnStm  {  Σ χ Γ} : (s  : Stm  Σ χ T Γ) → Set where
  SReturn : {e : Return (Exp Σ χ Γ) T} → returnStm (SReturn e)
  SBlock  : {ss : Stms Σ χ T ([] ∷ Γ)} → returnStms ss → returnStm (SBlock ss)
  SIfElse : ∀ {e} → ∀ {s1 s2 : Stms Σ χ T ([] ∷ Γ)} → returnStms s1 → returnStms s2 → returnStm (SIfElse e s1 s2)
data returnStms where
  SHead : ∀ {s ss} → returnStm  s  → returnStms (s ∷ ss)
  SCon  : ∀ {s ss} → returnStms ss → returnStms (s ∷ ss)


record Def (Σ : SymbolTab) (χ : TypeTab) (Ts : List Type) (T : Type) : Set  where
  field
    params : Params Ts

  field
    body      : Stms Σ χ T (Ts ∷ [])
    voidparam : All (_≢ void) Ts
    return    : returnStms body


-- FunList contains a function parameterized by Σ' for each element in Σ.
FunList : (χ : TypeTab) → (Σ' Σ : SymbolTab) → Set
FunList χ Σ' = TList (λ (_ , (ts , t)) → Def Σ' χ ts t)

record Program : Set where
  field
    BuiltIn : SymbolTab
    Defs    : SymbolTab
    χ       : TypeTab
  Σ' = BuiltIn ++ Defs

  field
    -- hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
    hasDefs    : FunList χ Σ' Defs
    uniqueDefs : Unique Σ'
