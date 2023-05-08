
open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Data.Product using (_×_; _,_; ∃)
open import Data.List  using (List; _∷_; []; _++_)
open import Data.String using (String; fromList)

import Data.Bool as Bool
import Data.Integer as Int
import Data.Float as Doub


open import Javalette.AST using (Ident; Type); open Type
open import TypedSyntax Ident as TS using (Block; Ctx; SymbolTab; _∈'_; _∈_; _∉_; Num; Eq; Ord; Return; toSet) 
open import WellTyped

module Semantics (Σ : SymbolTab) where 


open Expression Σ

-- Source operational semantics: well typed expr yields value with side effect
-- Potentially we should split it into two semantics to better support void
module Source {Γ : Ctx} where
  private
    variable
      eT : Γ ⊢ e ∶ T

  data _↓_ : (Γ ⊢ e ∶ T) → toSet T → Set where
    eLitInt   : ∀ x → eLitInt  x ↓ x
    eLitDoub  : ∀ x → eLitDoub x ↓ x
    eLitTrue  : eLitTrue  ↓ Bool.true 
    eLitFalse : eLitFalse ↓ Bool.false

    -- eVar : ∀ {t} id p → eVar id p ↓ {!!}
    -- eApp : ∀ id → (id , Ts , T) ∈ Σ → AllPair (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T

    negInt  : ∀ {x p} → {eT : Γ ⊢ e ∶ int}  → eT ↓ x → neg p eT ↓ (Int.- x)
    negDoub : ∀ {x p} → {eT : Γ ⊢ e ∶ doub} → eT ↓ x → neg p eT ↓ (Doub.-_ x)

    not : ∀ {x} → eT ↓ x → not eT ↓ (Bool.not x)

    -- eMod : (Γ ⊢ x ∶ int) → (Γ ⊢ y ∶ int) → Γ ⊢ eMul x mod y ∶ int
    eMulInt : ∀ {e1' e2' v1 v2} → {e1 : Γ ⊢ e1' ∶ int} → {e2 : Γ ⊢ e2' ∶ int} →
                      e1 ↓ v1 → e2 ↓ v2 → eMul TS.NumInt e1 e2 ↓ (v1 Int.+ v2)
    -- eDiv : Num T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eMul x div y ∶ T
    -- eAdd : Num T → (op : _) → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eAdd x op y ∶ T

    -- eOrd : ∀ {op} → OrdOp op → Ord T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool
    -- eEq  : ∀ {op} → EqOp  op → Eq  T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool

    -- eAnd : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eAnd x y ∶ bool
    -- eOr  : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eOr  x y ∶ bool

    -- -- eString is not wellTyped on its own
    -- ePrintString : ∀ s → Γ ⊢ eApp (ident "printString") (eString s ∷ []) ∶ void


  -- Side effect semantics
  data _⇓_ : (Γ ⊢ e ∶ T) → List String → Set where
    eLitInt   : ∀ {x} → eLitInt  x ⇓ []
    eLitDoub  : ∀ {x} → eLitDoub x ⇓ []
    eLitTrue  : eLitTrue  ⇓ []
    eLitFalse : eLitFalse ⇓ []
    eVar : ∀ {t id} → {p : (id , t) ∈' Γ} → eVar id p ⇓ []

    negInt  : ∀ {x p} → {eT : Γ ⊢ e ∶ int}  → eT ⇓ x → neg p eT ⇓ x
    negDoub : ∀ {x p} → {eT : Γ ⊢ e ∶ doub} → eT ⇓ x → neg p eT ⇓ x
    not : ∀ {x} → eT ⇓ x → not eT ⇓ x

    eAnd : ∀ {e1' e2' v1 v2}      → {e1 : Γ ⊢ e1' ∶ bool}   → {e2 : Γ ⊢ e2' ∶ bool}    → e1 ⇓ v1 → e2 ⇓ v2 → eAnd      e1 e2 ⇓ (v2 ++ v1)
    eOr  : ∀ {e1' e2' v1 v2}      → {e1 : Γ ⊢ e1' ∶ bool}   → {e2 : Γ ⊢ e2' ∶ bool}    → e1 ⇓ v1 → e2 ⇓ v2 → eOr       e1 e2 ⇓ (v2 ++ v1)
    eMod : ∀ {e1' e2' v1 v2}      → {e1 : Γ ⊢ e1' ∶ int} → {e2 : Γ ⊢ e2' ∶ int}  → e1 ⇓ v1 → e2 ⇓ v2 → eMod      e1 e2 ⇓ (v2 ++ v1)
    eMul : ∀ {e1' e2' v1 v2 p}    → {e1 : Γ ⊢ e1' ∶ T}   → {e2 : Γ ⊢ e2' ∶ T}    → e1 ⇓ v1 → e2 ⇓ v2 → eMul p    e1 e2 ⇓ (v2 ++ v1)
    eDiv : ∀ {e1' e2' v1 v2 p}    → {e1 : Γ ⊢ e1' ∶ T}   → {e2 : Γ ⊢ e2' ∶ T}    → e1 ⇓ v1 → e2 ⇓ v2 → eDiv p    e1 e2 ⇓ (v2 ++ v1)
    eAdd : ∀ {e1' e2' v1 v2 p op} → {e1 : Γ ⊢ e1' ∶ T}   → {e2 : Γ ⊢ e2' ∶ T}    → e1 ⇓ v1 → e2 ⇓ v2 → eAdd p op e1 e2 ⇓ (v2 ++ v1)
    eOrd : ∀ {e1' e2' v1 v2 p op} → {opP : OrdOp op} → {e1 : Γ ⊢ e1' ∶ T} → {e2 : Γ ⊢ e2' ∶ T} → e1 ⇓ v1 → e2 ⇓ v2 → eOrd opP p e1 e2 ⇓ (v2 ++ v1)
    eEq  : ∀ {e1' e2' v1 v2 p op} → {opP : EqOp  op} → {e1 : Γ ⊢ e1' ∶ T} → {e2 : Γ ⊢ e2' ∶ T} → e1 ⇓ v1 → e2 ⇓ v2 → eEq  opP p e1 e2 ⇓ (v2 ++ v1)


    -- eApp : ∀ id → (id , Ts , T) ∈ Σ → AllPair (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T
    ePrintString : ∀ {s} → ePrintString s ⇓ (fromList s ∷ [])



module Target {Γ : Ctx} where
  open TS.Typed Σ

  data _↓_ : (Exp Γ T) → (toSet T) → Set where
    EValue : ∀ {t} → (x : toSet t) → EValue x ↓ x

    -- eVar : ∀ {t} id p → eVar id p ↓ {!!}
    -- eApp : ∀ id → (id , Ts , T) ∈ Σ → AllPair (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T

    ENegInt  : ∀ {x p} → {eT : Exp Γ int}  → eT ↓ x → ENeg p eT ↓ (Int.- x)
    ENegDoub : ∀ {x p} → {eT : Exp Γ doub} → eT ↓ x → ENeg p eT ↓ (Doub.- x)

    ENot : ∀ {eT x} → eT ↓ x → ENot eT ↓ (Bool.not x)
    eMulInt : ∀ {v1 v2} → {e1 : Exp Γ int} → {e2 : Exp Γ int} →
                      e1 ↓ v1 → e2 ↓ v2 → EArith Num.NumInt e1 TS.ArithOp.* e2 ↓ (v1 Int.+ v2)


module SemanticsTest (Γ : Ctx) where
  open Source {Γ}
  open Target {Γ} renaming (_↓_ to _↓t_)
  open TS.Typed Σ

  
  private
    variable
      r r' : toSet T
      s s' : List String

  proof : {e : Γ ⊢ e' ∶ T}
             → e ↓ r  →  toExp e ↓t r'  →  (r ≡ r')
  proof (eLitInt x) (EValue .x) = refl
  proof (eLitDoub x) (EValue .x) = refl
  proof eLitTrue (EValue .Bool.true) = refl
  proof eLitFalse (EValue .Bool.false) = refl
  proof (negInt x) (ENegInt y)   rewrite proof x y = refl
  proof (negDoub x) (ENegDoub y) rewrite proof x y = refl
  proof (not x) (ENot y) rewrite proof x y = refl
  proof (eMulInt x x₁) (eMulInt y y₁) rewrite proof x y rewrite proof x₁ y₁ = refl
