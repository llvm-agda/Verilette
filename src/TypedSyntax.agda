module TypedSyntax where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool  using (Bool)
open import Agda.Builtin.Int   using (Int)
open import Agda.Builtin.Float using () renaming (Float to Double)

open import Data.Product using (_×_; _,_)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Relation.Nullary.Negation.Core using (¬_)

open import Javalette.AST using (Type; String) renaming (Ident to Id)
open Type public

variable
  A B : Set
  xs : List A

  ys : List (List A)
  x y : A


data ⊥ : Set where

_≢_ : ∀ {A} → A → A → Set
x ≢ y = ¬ (x ≡ y)


FunType : Set
FunType = ((List Type) × Type)

SymbolTab : Set
SymbolTab = List (Id × FunType)

Block : Set
Block = List (Id × Type)

Ctx : Set
Ctx = List Block

variable
  T t : Type
  ts  : List Type
  Δ Δ₁ Δ₂ : Block
  Γ Γ' : Ctx
  Σ : SymbolTab


infix 1 _∈_
data _∈_ (e : A)  : List A → Set where
  zero : e ∈ e ∷ xs
  suc  : e ∈ xs → e ∈ x ∷ xs

_∉_ : {A : Set} (id : Id) → List (Id × A) → Set 
id ∉ xs = All (λ (id' , _) → id ≢ id') xs

data _∈'_ (e : A) : List (List A) → Set where
  zero : e ∈  xs → e ∈' (xs ∷ ys)
  suc  : e ∈' ys → e ∈' (xs ∷ ys)

data Unique {A : Set} : (l : List (Id × A)) → Set where
  unique[]  : Unique []
  uniqueSuc : ∀ {id xs x} → id ∉ xs → Unique xs → Unique ((id , x) ∷ xs)

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

-- LIFTED TypeD List
infixr 5 _:+_
data TList {A : Set} (e : A → Set) : (As : List A) → Set where
  NIL  : TList e []
  _:+_ : ∀ {A AS} → e A → TList e AS → TList e (A ∷ AS)



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


  mutual
    data Stm : (T : Type) → (Γ : Ctx) → Set  where
      SExp    : Exp Γ void → Stm T Γ
      SDecl   : (t : Type) → (id : Id) → toSet t → id ∉ Δ → Stm T (Δ ∷ Γ)
      SAss    : (id : Id) → (e : Exp Γ t) → (id , t) ∈' Γ → Stm T Γ
      SWhile  : Exp Γ bool  → Stms T ([] ∷ Γ) → Stm T Γ
      SBlock  : Stms T ([] ∷ Γ) → Stm T Γ
      SIfElse : Exp Γ bool → Stms T ([] ∷ Γ) → Stms T ([] ∷ Γ) → Stm T Γ
      SReturn : Exp Γ T  → Stm T Γ
      VReturn : Stm void Γ

    nextCtx : {Γ : Ctx} → Stm T Γ → Ctx
    nextCtx {_} {(Δ ∷ Γ)} (SDecl t id x _) = ((id , t) ∷ Δ) ∷ Γ
    nextCtx {_} {Γ}       _              = Γ

    data Stms (T : Type) (Γ : Ctx) : Set where
      SEmpty  : Stms T Γ
      _SCons_ : (s : Stm T Γ) → Stms T (nextCtx s) → Stms T Γ


  data returnStms {T Γ} : (ss : Stms T Γ) → Set
  data returnStm    {Γ} : (s  : Stm  T Γ) → Set where
    VReturn : returnStm VReturn
    SReturn : {e : Exp Γ T} → returnStm (SReturn e)
    SBlock  : {ss : Stms T ([] ∷ Γ)} → returnStms ss → returnStm (SBlock ss)
    SIFElse : ∀ {e} → {s1 s2 : Stms T ([] ∷ Γ)} → returnStms s1 → returnStms s2 → returnStm (SIfElse e s1 s2)
  data returnStms where
    SHead : ∀ {s ss} → returnStm  s  → returnStms (s SCons ss)
    SCon  : ∀ {s ss} → returnStms ss → returnStms (s SCons ss)


open Typed

record Def (Σ : SymbolTab) (ts : List Type) (T : Type) : Set  where
  field
    idents : List Id

  params = zip idents ts

  field
    body      : Stms Σ T (params ∷ [])
    -- voidparam : void ∉t ts
    voidparam : All (_≢ void) ts
    unique    : Unique params
    return    : returnStms Σ body


record Program : Set where
  field
    BuiltIn : SymbolTab
    Defs    : SymbolTab
  Σ' = BuiltIn ++ Defs

  field
    hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
    hasDefs    : TList (λ (id , (ts , t)) → Def Σ' ts t) Defs
    uniqueDefs : Unique Σ'
