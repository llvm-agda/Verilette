{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; ≡-≟-identity; sym)
open import Data.String using (_≟_)

open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.List using (List; _∷_; []; zip; _++_; reverse; [_]) renaming (_ʳ++_ to _++r_; _∷ʳ_ to _∷r_)
open import Data.List.Properties using (ʳ++-defn)

open import Data.Empty using (⊥)

open import Function using (_$_; _∘_; case_of_; case_return_of_)

open import Javalette.AST
open import TypedSyntax Ident as TS using (Block; Ctx; SymbolTab;
                                           _∈'_; _∈_; _∉_;
                                           Num; Eq; Ord; NonVoid; Basic;
                                           Γ; Δ; Δ'; T; Ts) 
open NonVoid

open import TypeCheckerMonad
open import Util

module WellTyped where

variable
  e e' x y : Expr
  es : List Expr


data AllPair {A B : Set} (P : A → B → Set) : List A → List B → Set where
  []  : AllPair P [] []
  _∷_ : ∀ {x y xs ys} → P x y → AllPair P xs ys → AllPair P (x ∷ xs) (y ∷ ys)


data OrdOp : RelOp → Set where
    lTH : OrdOp lTH
    lE  : OrdOp lE
    gTH : OrdOp gTH
    gE  : OrdOp gE

data EqOp : RelOp → Set where
    eQU : EqOp eQU
    nE  : EqOp nE
  

-- Well formed block
data WFBlock : (Δ : Block) → Set where
  []  : WFBlock []
  _∷_ : ∀ {id t Δ} → id ∉ Δ × NonVoid t → WFBlock Δ → WFBlock ((id , t) ∷ Δ)


module Expression (Σ : SymbolTab) where


  data _⊢_∶_ (Γ : Ctx) : (e : Expr) → Type → Set
  data WFNew (Γ : Ctx) : New → Type → Set where
    nType  : ∀ {t}     → Basic t → WFNew Γ (nType t) t
    nArray : ∀ {e n t} → WFNew Γ n t → Γ ⊢ e ∶ int → WFNew Γ (nArray n e) (array t)

  -- Typing judgements 
  data _⊢_∶_ Γ where
    eLitInt   : ∀ x → Γ ⊢ eLitInt x ∶ int
    eLitDoub  : ∀ x → Γ ⊢ eLitDoub x ∶ doub
    eLitTrue  : Γ ⊢ eLitTrue ∶ bool
    eLitFalse : Γ ⊢ eLitFalse ∶ bool

    -- id should be unique in its block
    -- and the block should contain the first occurance of id in the context.
    -- This is needed for completeness, see checkProof
    eVar : ∀ {t} id → (id , t)      ∈' Γ → NonVoid t               → Γ ⊢ eVar id    ∶ t
    eApp : ∀     id → (id , Ts , T) ∈  Σ → AllPair (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T

    neg : Num T → Γ ⊢ e ∶ T    → Γ ⊢ neg e ∶ T
    not :         Γ ⊢ e ∶ bool → Γ ⊢ not e ∶ bool

    eMod : (Γ ⊢ x ∶ int) → (Γ ⊢ y ∶ int) → Γ ⊢ eMul x mod y ∶ int
    eMul : Num T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eMul x times y ∶ T
    eDiv : Num T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eMul x div y ∶ T
    eAdd : Num T → (op : _) → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eAdd x op y ∶ T

    eIndex  : ∀ {t arr i} →  Γ ⊢ arr ∶ array t →  Γ ⊢ i ∶ int →  Γ ⊢ eIndex arr i ∶ t
    eNew    : ∀ {new t}   →  WFNew Γ new t      →  Γ ⊢ eNew new ∶ t
    eLength : ∀ {e t}     →  Γ ⊢ e   ∶ array t →  Γ ⊢ eAttrib e (ident "length") ∶ int

    eOrd : ∀ {op} → OrdOp op → Ord T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool
    eEq  : ∀ {op} → EqOp  op → Eq  T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool

    eAnd : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eAnd x y ∶ bool
    eOr  : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eOr  x y ∶ bool

    -- eString is not wellTyped on its own
    ePrintString : ∀ s → Γ ⊢ eApp (ident "printString") (eString s ∷ []) ∶ void


_,,_ : Block → Ctx → Ctx
Δ ,, [] = Δ ∷ []
Δ ,, (Δ' ∷ Γ) = (Δ ++ Δ') ∷ Γ


ItemP : (Σ : SymbolTab) → Type → Ctx → Item → Set
ItemP _ _ [] _      = ⊥
ItemP _ _ (Δ ∷ Γ) (noInit id) =  id ∉ Δ
ItemP Σ t (Δ ∷ Γ) (init id e) = (id ∉ Δ) × ((Δ ∷ Γ) ⊢ e ∶ t)
  where open Expression Σ

itemId : Item → Ident
itemId (noInit x) = x
itemId (init x e) = x

data DeclP (Σ : SymbolTab) (T : Type) : List Item → (Γ : Ctx) → Block → Set where
  []  : DeclP Σ T [] Γ []
  _∷_ : ∀ {i is} → ItemP Σ T (Δ ∷ Γ) i → DeclP Σ T is (((itemId i , T) ∷ Δ) ∷ Γ) Δ' → DeclP Σ T (i ∷ is) (Δ ∷ Γ) ((itemId i , T) ∷ Δ')


module Statements (Σ : SymbolTab) (T : Type) where

  open Expression Σ

  data _⊢_⇒⇒_ (Γ : Ctx) : List Stmt → Block → Set
  data _⊢_⇒_  (Γ : Ctx) :      Stmt → Block → Set where
    empty  : Γ ⊢ empty ⇒ []
    sExp   : Γ ⊢ e ∶ void  →  Γ ⊢ sExp e ⇒ []
    bStmt  : ∀ {ss} → ([] ∷ Γ) ⊢ ss ⇒⇒ Δ → Γ ⊢ bStmt (block ss) ⇒ []
    decl   : ∀ t {is} → NonVoid t → DeclP Σ t is Γ Δ' → Γ ⊢ decl t is ⇒ reverse Δ'
    ass    : ∀ {t} id → (id , t) ∈' Γ  →  Γ ⊢ e ∶ t    →  Γ ⊢ ass id e ⇒ []
    assIdx : ∀ {t arr i x} → Γ ⊢ arr ∶ array t →  Γ ⊢ i ∶ int →  Γ ⊢ x ∶ t  →  Γ ⊢ assIdx arr i x ⇒ []
    incr   : ∀ id → (id , int) ∈' Γ  →  Γ ⊢ incr id ⇒ []
    decr   : ∀ id → (id , int) ∈' Γ  →  Γ ⊢ decr id ⇒ []
    ret    : Γ ⊢ e ∶ T  →  Γ ⊢ ret e ⇒ []
    vRet   : T ≡ void    →  Γ ⊢ vRet  ⇒ []
    cond     : ∀ {s}   → Γ ⊢ e ∶ bool →  ([] ∷ Γ) ⊢ s ⇒ Δ  →                       Γ ⊢ cond     e s   ⇒ []
    condElse : ∀ {t f} → Γ ⊢ e ∶ bool →  ([] ∷ Γ) ⊢ t ⇒ Δ  →  ([] ∷ Γ) ⊢ f ⇒ Δ' →  Γ ⊢ condElse e t f ⇒ []
    while    : ∀ {s}   → Γ ⊢ e ∶ bool →  ([] ∷ Γ) ⊢ s ⇒ Δ →                        Γ ⊢ while e s ⇒ []
    for      : ∀ {t e s} id →  Γ ⊢ e ∶ array t  →  ([ id , t ] ∷ Γ) ⊢ s ⇒ Δ'  →  Γ ⊢ for t id e s ⇒ []
    
  data _⊢_⇒⇒_ Γ where
    []  : Γ ⊢ [] ⇒⇒ []
    _∷_ : ∀ {s ss} → Γ ⊢ s ⇒ Δ  →  (Δ ,, Γ) ⊢ ss ⇒⇒ Δ'  →  Γ ⊢ s ∷ ss ⇒⇒ (Δ' ++ Δ)


module Return where

  open Statements
  open Expression

  data Returns' {Σ : SymbolTab} {Γ : Ctx} : ∀ {  T} {s  :      Stmt} → (_⊢_⇒_  Σ T Γ s   Δ) → Set
  data Returns  {Σ : SymbolTab}           : ∀ {Γ T} {ss : List Stmt} → (_⊢_⇒⇒_ Σ T Γ ss  Δ) → Set where
    here  : ∀ {s ss} → {s' : _⊢_⇒_ Σ T Γ s Δ} → {ss' : _⊢_⇒⇒_ Σ T (Δ ,, Γ) ss Δ'}
                       → Returns' s' → Returns (s' ∷ ss')
    there : ∀ {s ss} → {s' : _⊢_⇒_ Σ T Γ s Δ} → {ss' : _⊢_⇒⇒_ Σ T (Δ ,, Γ) ss Δ'}
                      → Returns ss' → Returns (s' ∷ ss')
    vEnd : ∀ {Δ} → Returns {Γ = Δ ∷ []} {T = void} []

  data Returns' {Σ} {Γ} where
    ret   : (e' : _⊢_∶_ Σ Γ e T) → Returns' (ret e')
    vRet  : Returns' (vRet refl)
    bStmt : ∀ {ss} → {ss' : _⊢_⇒⇒_ Σ T ([] ∷ Γ) ss Δ} → Returns ss' →  Returns' (bStmt ss')
    condElse : ∀ {s1 s2} → { eB : _⊢_∶_ Σ Γ e bool } → {s1' : _⊢_⇒_ Σ T ([] ∷ Γ) s1 Δ} → {s2' : _⊢_⇒_ Σ T ([] ∷ Γ) s2 Δ'}
                     → Returns' s1' → Returns' s2' → Returns' (condElse eB s1' s2')


module FunDef where

  open Statements
  open Return

  fromArgs : List Arg → Block
  fromArgs [] = []
  fromArgs (argument t x ∷ as) = (x , t) ∷ fromArgs as

  data ValidFun (Σ : SymbolTab) : TopDef → Set where
    validFun : ∀ {t id as ss Δ} → WFBlock (fromArgs as) → (ss' : _⊢_⇒⇒_ Σ t (fromArgs as ∷ []) ss Δ)
                                → Returns ss' →  ValidFun Σ (fnDef t id as (block ss))
