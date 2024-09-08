open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; ≡-≟-identity; sym)
open import Data.String using (_≟_)

open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise); open Pointwise

open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.List using (List; _∷_; []; zip; _++_; reverse; [_]; foldr) renaming (_ʳ++_ to _++r_; _∷ʳ_ to _∷r_)
open import Data.List.Properties using (ʳ++-defn)

open import Data.Empty using (⊥)

open import Function using (_$_; _∘_; case_of_; case_return_of_; const)

open import Javalette.AST renaming (Ident to Id)
open import TypedSyntax as TS using (TypeTab;
                                    _∈'_; _∈_; _∉_;
                                    Num; Eq; Ord; NonVoid; Basic;
                                    T; Ts)
open NonVoid


module WellTyped where


Block : Set
Block = List (Id × Type)

Ctx : Set
Ctx = List Block


FunType : Set
FunType = List Type × Type

SymbolTab : Set
SymbolTab = List (Id × FunType)


variable
  e x y : Expr
  es : List Expr
  Δ Δ' : Block
  Γ Γ' Γ'' : Ctx


data OrdOp : RelOp → Set where
    lTH : OrdOp lTH
    lE  : OrdOp lE
    gTH : OrdOp gTH
    gE  : OrdOp gE

data EqOp : RelOp → Set where
    eQU : EqOp eQU
    nE  : EqOp nE

deLen : ArrDecl → Expr
deLen (arraySize e) = e

module Expression (Σ : SymbolTab) (χ : TypeTab) where


  -- Typing judgements
  data _⊢_∶_ (Γ : Ctx) : (e : Expr) → Type → Set where
    eLitInt   : ∀ x → Γ ⊢ eLitInt x ∶ int
    eLitDoub  : ∀ x → Γ ⊢ eLitDoub x ∶ doub
    eLitTrue  : Γ ⊢ eLitTrue ∶ bool
    eLitFalse : Γ ⊢ eLitFalse ∶ bool

    -- id should be unique in its block
    -- and the block should contain the first occurance of id in the context.
    -- This is needed for completeness, see checkProof
    eVar : ∀ {t} id → (id , t)      ∈' Γ                           → Γ ⊢ eVar id    ∶ t
    eApp : ∀     id → (id , Ts , T) ∈  Σ → Pointwise (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T

    neg : Num T → Γ ⊢ e ∶ T    → Γ ⊢ neg e ∶ T
    not :         Γ ⊢ e ∶ bool → Γ ⊢ not e ∶ bool

    eMod : (Γ ⊢ x ∶ int) → (Γ ⊢ y ∶ int) → Γ ⊢ eMul x mod y ∶ int
    eMul : Num T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eMul x times y ∶ T
    eDiv : Num T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eMul x div y ∶ T
    eAdd : Num T → (op : _) → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eAdd x op y ∶ T

    eIndex  : ∀ {t arr i} →  Γ ⊢ arr ∶ array t →  Γ ⊢ i ∶ int →  Γ ⊢ eIndex arr i ∶ t
    eArray  : ∀ {t n ns} → Basic χ t → All (Γ ⊢_∶ int ∘ deLen) (n ∷ ns) → Γ ⊢ eNew t (n ∷ ns) ∶ foldr (const array) t (n ∷ ns)
    eLength : ∀ {e t}   →  Γ ⊢ e ∶ array t →  Γ ⊢ eAttrib e (ident "length") ∶ int

    eStruct : ∀ {c n fs} → (n , c , fs) ∈ χ  → Γ ⊢ eNew (structT c) [] ∶ structT n
    eNull   : ∀ {c n fs} → (n , c , fs) ∈ χ  → Γ ⊢ eNull (eVar n) ∶ structT n
    eDeRef  : ∀ {n f c fs t} →  Γ ⊢ e ∶ structT n →  (n , c , fs) ∈ χ →  (f , t) ∈ fs →   Γ ⊢ eDeRef e f ∶ t

    eOrd : ∀ {op} → OrdOp op → Ord T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool
    eEq  : ∀ {op} → EqOp  op → Eq  T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool

    eAnd : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eAnd x y ∶ bool
    eOr  : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eOr  x y ∶ bool

    -- eString is not wellTyped on its own
    ePrintString : ∀ s → Γ ⊢ eApp (ident "printString") (eString s ∷ []) ∶ void


-- Reflexiv Transitive closure over list, i.e. a chain
module _ {A O : Set} (P : A → O → A → Set) where

  data Star' (x : A) : List O → A → Set where
    []  : Star' x [] x
    _∷_ : ∀ {o os y z} → P x o y → Star' y os z → Star' x (o ∷ os) z

module Declarations (Σ : SymbolTab) (χ : TypeTab) (t : Type) where
  open Expression Σ χ

  data DeclP : Ctx → Item → Ctx → Set where
    noInit : ∀ {id  } → id ∉ Δ                   → DeclP (Δ ∷ Γ) (noInit id) (((id , t) ∷ Δ) ∷ Γ)
    init   : ∀ {id e} → id ∉ Δ → (Δ ∷ Γ) ⊢ e ∶ t → DeclP (Δ ∷ Γ) (init id e) (((id , t) ∷ Δ) ∷ Γ)


module Statements (Σ : SymbolTab) (χ : TypeTab) (T : Type) where
  open Expression Σ χ
  open Declarations Σ χ


  data _⊢_⇒_  (Γ : Ctx) :    Stmt → Ctx → Set

  -- Reflexive transitive closure of _⊢_⇒_, i.e. a link of statments
  _⊢_⇒⇒_ : (Γ : Ctx) → List Stmt → Ctx → Set
  _⊢_⇒⇒_ = Star' _⊢_⇒_

  data _⊢_⇒_ Γ where
    empty  : Γ ⊢ empty ⇒ Γ
    sExp   : Γ ⊢ e ∶ void  →  Γ ⊢ sExp e ⇒ Γ
    bStmt  : ∀ {ss} → ([] ∷ Γ) ⊢ ss ⇒⇒ Γ' → Γ ⊢ bStmt (block ss) ⇒ Γ
    decl   : ∀ {t is} → NonVoid χ t → Star' (DeclP t) Γ is Γ' → Γ ⊢ decl t is ⇒ Γ'
    ass    : ∀ {t} id → (id , t) ∈' Γ  →  Γ ⊢ e ∶ t    →  Γ ⊢ ass (eVar id) e ⇒ Γ
    assIdx : ∀ {t arr i x}  → Γ ⊢ arr ∶ array t →  Γ ⊢ i ∶ int →  Γ ⊢ x ∶ t  →  Γ ⊢ ass (eIndex arr i) x ⇒ Γ
    assPtr : ∀ {t s e fs f n c} → Γ ⊢ s ∶ structT n → (n , c , fs) ∈ χ → (f , t) ∈ fs → Γ ⊢ e ∶ t → Γ ⊢ ass (eDeRef s f) e ⇒ Γ
    incr   : ∀ id → (id , int) ∈' Γ  →  Γ ⊢ incr id ⇒ Γ
    decr   : ∀ id → (id , int) ∈' Γ  →  Γ ⊢ decr id ⇒ Γ
    ret    : Γ ⊢ e ∶ T  →  Γ ⊢ ret e ⇒ Γ
    vRet   : T ≡ void    →  Γ ⊢ vRet  ⇒ Γ
    cond     : ∀ {s}   → Γ ⊢ e ∶ bool →  ([] ∷ Γ) ⊢ s ⇒ Γ' →                        Γ ⊢ cond     e s   ⇒ Γ
    condElse : ∀ {t f} → Γ ⊢ e ∶ bool →  ([] ∷ Γ) ⊢ t ⇒ Γ' →  ([] ∷ Γ) ⊢ f ⇒ Γ'' →  Γ ⊢ condElse e t f ⇒ Γ
    while    : ∀ {s}   → Γ ⊢ e ∶ bool →  ([] ∷ Γ) ⊢ s ⇒ Γ' →                        Γ ⊢ while e s ⇒ Γ
    for      : ∀ {t e s} id →  Γ ⊢ e ∶ array t  →  ([ id , t ] ∷ Γ) ⊢ s ⇒ Γ'  →  Γ ⊢ for t id e s ⇒ Γ


-- Witness of return statments
module Return {Σ : SymbolTab} {χ : TypeTab} where

  open Statements Σ χ
  open Expression Σ χ

  private
    variable
      s s1 s2 : Stmt
      ss      : List Stmt

      s' s1' s2' : _⊢_⇒_  T Γ s Γ'
      ss' : _⊢_⇒⇒_ T Γ ss Γ'

      e' : Γ ⊢ e ∶ T

  data Returns' {Γ : Ctx} : ∀ {  T} → (_⊢_⇒_  T Γ s  Γ') → Set
  data Returns            : ∀ {Γ T} → (_⊢_⇒⇒_ T Γ ss Γ') → Set where
    here  : Returns' s' → Returns (s' ∷ ss')
    there : Returns ss' → Returns (s' ∷ ss')
    vEnd  : Returns {Γ = Δ ∷ []} {T = void} []

  data Returns' where
    ret      : Returns' (ret e')
    vRet     : Returns' (vRet refl)
    bStmt    : Returns ss' → Returns' (bStmt ss')
    condElse : Returns' s1' → Returns' s2' → Returns' (condElse e' s1' s2')


fromArgs : List Arg → Block
fromArgs [] = []
fromArgs (argument t x ∷ as) = (x , t) ∷ fromArgs as

module FunDef (Σ : SymbolTab) (χ : TypeTab) (T : Type) where

  open Statements Σ χ T
  open Return {Σ} {χ}

  data ValidFun : TopDef → Set where
    fnDef : ∀ {id as ss} → (ss' : (fromArgs as ∷ []) ⊢ ss ⇒⇒ Γ')
                           → Returns ss' →  ValidFun (fnDef T id as (block ss))

--    typeDef : ∀ {n c : Ident} → ValidFun (typeDef n c)
--    -- struct  : ∀ {c fs} → WFBlock χ (fromArgs fs) → TopDef (struct c fs)
