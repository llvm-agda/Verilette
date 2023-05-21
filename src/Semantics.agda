
open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Data.Product using (_×_; _,_; ∃)
open import Data.List  using (List; _∷_; []; _++_)
open import Data.String using (String; fromList)

import Data.Bool as Bool
import Data.Integer as Int
import Data.Float as Doub


open import Javalette.AST using (Ident; Type; Stmt); open Type
open import TypedSyntax  as TS using (Block; Ctx; SymbolTab; TypeTab
                                             ; _∈'_; _∈_; _∉_
                                             ; T; Γ; Δ; Δ'
                                             ; Num; Eq; Ord; Return; toSet)
open import WellTyped
open import TypeCheck.CheckExp
open import Translate

module Semantics (Σ : SymbolTab) (χ : TypeTab) where


open Expression Σ χ

-- Source operational semantics: well typed expr yields value with side effect
-- Potentially we should split it into two semantics to better support void
module SourceExp {Γ : Ctx} where
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
    eVar : ∀ {t id} {p : (id , t) ∈' Γ} → eVar id p ⇓ []

    negInt  : ∀ {x p} → {eT : Γ ⊢ e ∶ int}  → eT ⇓ x → neg p eT ⇓ x
    negDoub : ∀ {x p} → {eT : Γ ⊢ e ∶ doub} → eT ⇓ x → neg p eT ⇓ x
    not : ∀ {x} → eT ⇓ x → not eT ⇓ x

    eAnd : ∀ {e1' e2' v1 v2}      → {e1 : Γ ⊢ e1' ∶ bool}   → {e2 : Γ ⊢ e2' ∶ bool}    → e1 ⇓ v1 → e2 ⇓ v2         → eAnd       e1 e2 ⇓ (v1 ++ v2)
    eOr  : ∀ {e1' e2' v1 v2}      → {e1 : Γ ⊢ e1' ∶ bool}   → {e2 : Γ ⊢ e2' ∶ bool}    → e1 ⇓ v1 → e2 ⇓ v2         → eOr        e1 e2 ⇓ (v1 ++ v2)
    eMod : ∀ {e1' e2' v1 v2}      → {e1 : Γ ⊢ e1' ∶ int} → {e2 : Γ ⊢ e2' ∶ int}  → e1 ⇓ v1 → e2 ⇓ v2               → eMod       e1 e2 ⇓ (v1 ++ v2)
    eMul : ∀ {e1' e2' v1 v2 p}    → {e1 : Γ ⊢ e1' ∶ T}   → {e2 : Γ ⊢ e2' ∶ T}    → e1 ⇓ v1 → e2 ⇓ v2               → eMul p     e1 e2 ⇓ (v1 ++ v2)
    eDiv : ∀ {e1' e2' v1 v2 p}    → {e1 : Γ ⊢ e1' ∶ T}   → {e2 : Γ ⊢ e2' ∶ T}    → e1 ⇓ v1 → e2 ⇓ v2               → eDiv p     e1 e2 ⇓ (v1 ++ v2)
    eAdd : ∀ {e1' e2' v1 v2 p op} → {e1 : Γ ⊢ e1' ∶ T}   → {e2 : Γ ⊢ e2' ∶ T}    → e1 ⇓ v1 → e2 ⇓ v2               → eAdd p op  e1 e2 ⇓ (v1 ++ v2)
    eOrd : ∀ {e1' e2' v1 v2 p op} → {opP : OrdOp op} → {e1 : Γ ⊢ e1' ∶ T} → {e2 : Γ ⊢ e2' ∶ T} → e1 ⇓ v1 → e2 ⇓ v2 → eOrd opP p e1 e2 ⇓ (v1 ++ v2)
    eEq  : ∀ {e1' e2' v1 v2 p op} → {opP : EqOp  op} → {e1 : Γ ⊢ e1' ∶ T} → {e2 : Γ ⊢ e2' ∶ T} → e1 ⇓ v1 → e2 ⇓ v2 → eEq  opP p e1 e2 ⇓ (v1 ++ v2)

    -- eApp : ∀ id → (id , Ts , T) ∈ Σ → AllPair (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T
    ePrintString : ∀ {s} → ePrintString s ⇓ (fromList s ∷ [])



module TargetExp {Γ : Ctx} where
  open TS.Typed Σ χ

  data _↓_ : (Exp Γ T) → (toSet T) → Set where
    EValue : ∀ {t} → (x : toSet t) → EValue x ↓ x

    -- eVar : ∀ {t} id p → eVar id p ↓ {!!}
    -- eApp : ∀ id → (id , Ts , T) ∈ Σ → AllPair (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T

    ENegInt  : ∀ {x p} → {eT : Exp Γ int}  → eT ↓ x → ENeg p eT ↓ (Int.- x)
    ENegDoub : ∀ {x p} → {eT : Exp Γ doub} → eT ↓ x → ENeg p eT ↓ (Doub.- x)

    ENot : ∀ {eT x} → eT ↓ x → ENot eT ↓ (Bool.not x)
    eMulInt : ∀ {v1 v2} → {e1 : Exp Γ int} → {e2 : Exp Γ int} →
                      e1 ↓ v1 → e2 ↓ v2 → EArith Num.NumInt e1 TS.ArithOp.* e2 ↓ (v1 Int.+ v2)

  data _⇓_ : (Exp Γ T) → List String → Set where
    EValue : ∀ {t} → {x : toSet t}            → EValue x ⇓ []
    EId    : ∀ {id t} → (p : (id , t) ∈' Γ)  → EId id p ⇓ []
    -- EAPP   : (id : Id) → TList (Exp Γ) ts → (id , (ts , T)) ∈ Σ → Exp Γ T
    EMod   : ∀ {e1 e2 s1 s2} → e1 ⇓ s1 → e2 ⇓ s2 → EMod e1 e2 ⇓ (s1 ++ s2)
    EArith : ∀ {op s1 s2 t} → {p : Num t} → {e1 e2 : Exp Γ t} →  e1 ⇓ s1 → e2 ⇓ s2 → EArith p e1 op e2 ⇓ (s1 ++ s2)
    EOrd   : ∀ {op s1 s2 t} → {p : Ord t} → {e1 e2 : Exp Γ t} →  e1 ⇓ s1 → e2 ⇓ s2 → EOrd   p e1 op e2 ⇓ (s1 ++ s2)
    EEq    : ∀ {op s1 s2 t} → {p : Eq  t} → {e1 e2 : Exp Γ t} →  e1 ⇓ s1 → e2 ⇓ s2 → EEq    p e1 op e2 ⇓ (s1 ++ s2)
    ELogic : ∀ {op e1 e2 s1 s2} → e1 ⇓ s1 → e2 ⇓ s2 → ELogic e1 op e2 ⇓ (s1 ++ s2)
    ENeg   : ∀ {s t} → {p : Num t} → {e : Exp Γ t} →  e ⇓ s → ENeg p e ⇓ s
    ENot   : ∀ {e s} →  e ⇓ s → ENot e ⇓ s
    EPrintStr : ∀ {s} → EPrintStr s ⇓ (fromList s ∷ [])


module SemanticsExp (Γ : Ctx) where
  open SourceExp {Γ}
  open TargetExp {Γ} renaming (_↓_ to _↓t_; _⇓_ to _⇓t_)
  open TS.Typed Σ χ

  private
    variable
      r r' : toSet T
      s s' : List String

  proof : {e : Γ ⊢ e' ∶ T} → e ↓ r  →  toExp Σ χ e ↓t r'  →  (r ≡ r')
  proof (eLitInt x) (EValue .x) = refl
  proof (eLitDoub x) (EValue .x) = refl
  proof eLitTrue (EValue .Bool.true) = refl
  proof eLitFalse (EValue .Bool.false) = refl
  proof (negInt x) (ENegInt y)   rewrite proof x y = refl
  proof (negDoub x) (ENegDoub y) rewrite proof x y = refl
  proof (not x) (ENot y) rewrite proof x y = refl
  proof (eMulInt x x₁) (eMulInt y y₁) rewrite proof x y rewrite proof x₁ y₁ = refl


  -- Side Effect
  proofSE : {e : Γ ⊢ e' ∶ T} → e ⇓ s  →  toExp Σ χ e ⇓t s'  →  (s ≡ s')
  proofSE eLitInt   EValue = refl
  proofSE eLitDoub  EValue = refl
  proofSE eLitTrue  EValue = refl
  proofSE eLitFalse EValue = refl
  proofSE eVar (EId _) = refl
  proofSE (negInt x)  (ENeg x₁) = proofSE x x₁
  proofSE (negDoub x) (ENeg x₁) = proofSE x x₁
  proofSE (not x)     (ENot x₁) = proofSE x x₁
  proofSE (eAnd x x₂) (ELogic x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eOr x x₂)  (ELogic x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eMod x x₂) (EMod x₁ x₃)   rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eMul x x₂) (EArith x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eDiv x x₂) (EArith x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eAdd {op = Javalette.AST.plus} x x₂)  (EArith x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eAdd {op = Javalette.AST.minus} x x₂) (EArith x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eOrd {opP = lTH} x x₂) (EOrd x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eOrd {opP = lE}  x x₂) (EOrd x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eOrd {opP = gTH} x x₂) (EOrd x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eOrd {opP = gE}  x x₂) (EOrd x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eEq  {opP = eQU} x x₂) (EEq  x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE (eEq  {opP = nE}  x x₂) (EEq  x₁ x₃) rewrite proofSE x x₁ rewrite proofSE x₂ x₃ = refl
  proofSE ePrintString EPrintStr = refl




module SourceStms (T : Type) where
  open Statements Σ χ T
  open SourceExp
  open Bool using (true; false)

  private
    variable
      s  : Stmt
      ss : List Stmt

  data _⤋_ {Γ : Ctx} : (Γ ⊢ s  ⇒  Δ) → List String → Set
  data _⇊_ {Γ : Ctx} : (Γ ⊢ ss ⇒⇒ Δ) → List String → Set where
    []  : [] ⇊ []
    _∷_ : ∀ {v1 v2} → {s : Γ ⊢ s ⇒ Δ} → {ss : (Δ ,, Γ) ⊢ ss ⇒⇒ Δ'} → s ⤋ v1 → ss ⇊ v2  →  (s ∷ ss) ⇊ (v1 ++ v2)

  data _⤋_ {Γ} where
    empty : empty ⤋ []
    bStmt : ∀ {v} → {ss : ([] ∷ Γ) ⊢ ss ⇒⇒ Δ} → ss ⇊ v →  bStmt ss ⤋ v
    decl : ∀ {t is} → {n : TS.NonVoid χ t} → {p : DeclP Σ χ t is Γ Δ} →  decl t n p ⤋ []
    ass  : ∀ {t id v} → {p : (id , t  ) ∈' Γ} → {e' : Γ ⊢ e ∶ t  } → e' ⇓ v  → ass  id p e' ⤋ v
    incr : ∀ {  id  } → {p : (id , int) ∈' Γ} → {e' : Γ ⊢ e ∶ int}           → incr id p ⤋ []
    decr : ∀ {  id  } → {p : (id , int) ∈' Γ} → {e' : Γ ⊢ e ∶ int}           → decr id p ⤋ []
    ret  : ∀ {v} → {e' : Γ ⊢ e ∶ T} → e' ⇓ v → ret e' ⤋ v
    vRet  : ∀ {v} → {p : T ≡ void} →  vRet p ⤋ v
    condTrue  : ∀ {e s v1 v2} → {eB : Γ ⊢ e ∶ bool} → eB ↓ true  → eB ⇓ v1 → {s' : ([] ∷ Γ) ⊢ s ⇒ Δ} → s' ⤋ v2 → cond eB s' ⤋ (v1 ++ v2)
    condFalse : ∀ {e s v1   } → {eB : Γ ⊢ e ∶ bool} → eB ↓ false → eB ⇓ v1 → {s' : ([] ∷ Γ) ⊢ s ⇒ Δ}           → cond eB s' ⤋ v1
    condElseTrue  : ∀ {e s1 s2 v1 v2} → {eB : Γ ⊢ e ∶ bool} → eB ↓ true  → eB ⇓ v1 → {s1' : ([] ∷ Γ) ⊢ s1 ⇒ Δ} → s1' ⤋ v2
                                                                                    → {s2' : ([] ∷ Γ) ⊢ s2 ⇒ Δ}            → condElse eB s1' s2' ⤋ (v1 ++ v2)
    condElseFalse : ∀ {e s1 s2 v1 v2} → {eB : Γ ⊢ e ∶ bool} → eB ↓ false → eB ⇓ v1 → {s1' : ([] ∷ Γ) ⊢ s1 ⇒ Δ}
                                                                                    → {s2' : ([] ∷ Γ) ⊢ s2 ⇒ Δ} → s1' ⤋ v2 → condElse eB s1' s2' ⤋ (v1 ++ v2)
    whileNoLoop : ∀ {e v s}        → {eB : Γ ⊢ e ∶ bool} → eB ↓ false → eB ⇓ v  → {s' : ([] ∷ Γ) ⊢ s ⇒ Δ} → while eB s' ⤋ v
    whileLoop   : ∀ {e v1 s v2 v3} → {eB : Γ ⊢ e ∶ bool} → eB ↓ true  → eB ⇓ v1 → {s' : ([] ∷ Γ) ⊢ s ⇒ Δ} → s' ⤋ v2
                                → while eB s' ⤋ v3 →  while eB s' ⤋ (v1 ++ v2 ++ v3) -- Does this handle the loop??
    sExp : ∀ {v} → {e' : Γ ⊢ e ∶ void} → e' ⇓ v  → sExp e' ⤋ v


module TargetStms (T : Type) where
  open TargetExp
  open TS.Typed Σ χ
  open TS.Valid Σ χ T
  open Bool using (true; false)

  data _⤋_ : (Stm  Γ) → List String → Set
  data _⇊_ {Γ : Ctx} : (Stms Γ) → List String → Set where
    []  : SEmpty ⇊ []
    _∷_ : ∀ {s ss v1 v2} → s ⤋ v1 → ss ⇊ v2 → (s SCons ss) ⇊ (v1 ++ v2)

  data _⤋_ where
    SExp    : ∀ {v} → {e : Exp Γ void} →  e ⇓ v → SExp e ⤋ v
    SDecl   : ∀ {t id p v} → {e : Exp (Δ ∷ Γ) _} → e ⇓ v → SDecl t id e p ⤋ v
    SAss    : ∀ {id t p v} → {e : Exp Γ t} → e ⇓ v → SAss id e p ⤋ v
    SWhileNoLoop : ∀ {v  ss}       → {eB : Exp Γ bool} → eB ↓ false → eB ⇓ v  →  SWhile eB ss ⤋ v
    SWhileLoop   : ∀ {v1 ss v2 v3} → {eB : Exp Γ bool} → eB ↓ true  → eB ⇓ v1 → ss ⇊ v2
                                → SWhile eB ss ⤋ v3 →  SWhile eB ss ⤋ (v1 ++ v2 ++ v3) -- Does this handle the loop??
    SBlock  : ∀ {v} → {ss : Stms ([] ∷ Γ)} → ss ⇊ v → SBlock ss ⤋ v
    -- SIfElse : Exp Γ bool → Stms ([] ∷ Γ) → Stms ([] ∷ Γ) → Stm Γ
    -- SReturn : Return (Exp Γ) T → Stm Γ
