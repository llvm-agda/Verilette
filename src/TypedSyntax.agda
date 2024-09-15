module TypedSyntax where

import Data.Bool    as Bool
import Data.Integer as Int
import Data.Float   as Doub
import Data.Nat     as Nat

open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_; reverse; [_])
open import Data.List.Relation.Unary.All using (All) renaming (map to allMap); open All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
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
FunType = List Type × Type

SymbolTab : Set
SymbolTab = List FunType

TypeTab : Set
TypeTab = List (Id × (Id × List (Id × Type)))


Block : Set
Block = List Type

Ctx : Set
Ctx = List Block

Named : ∀ {A} → List A → Set
Named = All (λ _ → Id)


variable
  T T' t : Type
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

All× : (A → B → Set) → List (A × B) → Set
All× P = All (λ (a , b) → P a b)

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

data Op : Type → Type → Set where
  OpNum   : Num T → ArithOp → Op T T
  OpOrd   : Ord T → OrdOp   → Op T bool
  OpEq    : Eq  T → EqOp    → Op T bool
  OpLogic :         LogicOp → Op bool bool
  OpMod   :                   Op int int

data Return (P : Type → Set) : Type → Set where
  vRet : Return P void
  Ret : P t → Return P t

-- Nonempty-list that iterate w on the index for each item
data WFNew {T : Set} (E : Set) (w : T → T) : T → Set where
  nType  : ∀ {t} → E               →  WFNew E w (w t)
  nArray : ∀ {t} → E → WFNew E w t →  WFNew E w (w t)


--------------------------------------------------------------------------------
-- EXPRESSIONS AND STATEMENTS
module Typed (Σ : SymbolTab) (χ : TypeTab) where

  data Exp (Γ : Ctx) : Type → Set where
    EValue  : toSet T  → Exp Γ T
    EId     : T ∈' Γ → Exp Γ T
    EAPP    : (ts , T) ∈ Σ → All (Exp Γ) ts → Exp Γ T
    EOp     : Op T' T → (x y : Exp Γ T') → Exp Γ T
    EIdx    : Exp Γ (array t) → Exp Γ int → Exp Γ t
    EArray  : ∀ {t} → WFNew (Exp Γ int) array t → Exp Γ t
    EStruct : ∀ {n} → Exp Γ (structT n)
    ELength : Exp Γ (array t) → Exp Γ int
    EDeRef  : ∀ {n n' fs t c} → Exp Γ (structT n) → (n , c , fs) ∈ χ →  (n' , t) ∈ fs → Exp Γ t
    EPrintStr : String → Exp Γ void


module Valid (Σ : SymbolTab) (χ : TypeTab) (T : Type) where
  open Typed Σ χ

  mutual
    data Stm : (Γ : Ctx) → Set  where
      SExp    : Exp Γ void → Stm Γ
      SDecl   : (t : Type) → Exp (Δ ∷ Γ) t → Stm (Δ ∷ Γ)
      SAss    : t ∈' Γ → (e : Exp Γ t) → Stm Γ
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
data returnStm  {T Σ χ Γ} : (s  : Stm  Σ χ T Γ) → Set where
  SReturn : ∀ {e}  → returnStm (SReturn e)
  SBlock  : ∀ {ss} → returnStms ss → returnStm (SBlock ss)
  SIfElse : ∀ {e s1 s2} → returnStms s1 → returnStms s2 → returnStm (SIfElse e s1 s2)
data returnStms where
  SHead : ∀ {s ss} → returnStm  s  → returnStms (s ∷ ss)
  SCon  : ∀ {s ss} → returnStms ss → returnStms (s ∷ ss)


record Def (Σ : SymbolTab) (χ : TypeTab) (Ts : List Type) (T : Type) : Set  where
  field
    funId     : Id
    params    : Named Ts
    body      : Stms Σ χ T (Ts ∷ [])
    voidparam : All (_≢ void) Ts
    return    : returnStms body


record Program : Set where
  field
    {BuiltIn Defs} : SymbolTab
    χ            : TypeTab
    NamedBuiltIn : Named BuiltIn

  Σ' = BuiltIn ++ Defs

  field
    -- hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
    hasDefs    : All×  (Def Σ' χ) Defs
    -- uniqueDefs : Unique Σ'

  NamedFuns : Named Σ'
  NamedFuns = ++⁺ NamedBuiltIn (allMap Def.funId hasDefs)
