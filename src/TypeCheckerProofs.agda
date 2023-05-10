

open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Binary.PropositionalEquality using (_≢_; ≡-≟-identity; sym)
open import Data.String using (_≟_)

open import Data.Product using (_×_; _,_; ∃; proj₂)

open import Javalette.AST using (Ident; ident; Type); open Type
open import Util 
open import TypedSyntax Ident using (SymbolTab; Ctx; Num; Ord; Eq) 
open import WellTyped 
open import CheckExp 


module TypeCheckerProofs where

module ExpressionProofs (Σ : SymbolTab) (Γ : Ctx) where

  open CheckExp.CheckExp Σ Γ
  open WellTyped.Expression Σ


  eqIdRefl : ∀ id → id eqId id ≡ inj₂ refl
  eqIdRefl (ident x) with p ← refl {_} {_} {x} rewrite ≡-≟-identity _≟_ p rewrite p = refl


  =T=Refl     : (t  :      Type) → t =T= t        ≡ inj₁ refl
  eqListsRefl : (ts : List Type) → eqLists' ts ts ≡ inj₁ refl
  eqListsRefl [] = refl
  eqListsRefl (t ∷ ts) rewrite =T=Refl t rewrite eqListsRefl ts = refl

  =T=Refl int = refl
  =T=Refl doub = refl
  =T=Refl bool = refl
  =T=Refl void = refl
  =T=Refl (fun t ts) rewrite =T=Refl t rewrite eqListsRefl ts = refl
  
  -- Every well typed expression can be infered
  inferProof : ∀ {e t} → (eT : Γ ⊢ e ∶ t) → infer e ≡ inj₂ (t , eT)
  inferProof (eLitInt x) = refl
  inferProof (eLitDoub x) = refl
  inferProof eLitTrue = refl
  inferProof eLitFalse = refl
  inferProof (eVar id x n) = {!!}
  inferProof (eApp id x n xs) = {!!}
  inferProof (neg Num.NumInt eT)    rewrite inferProof eT = refl
  inferProof (neg Num.NumDouble eT) rewrite inferProof eT = refl
  inferProof (not eT) rewrite inferProof eT = refl
  inferProof (eMod eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eMul Num.NumInt        eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eMul Num.NumDouble     eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eDiv Num.NumInt        eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eDiv Num.NumDouble     eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eAdd Num.NumInt     op eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eAdd Num.NumDouble  op eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd lTH Ord.OrdInt    eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd lE  Ord.OrdInt    eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd gTH Ord.OrdInt    eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd gE  Ord.OrdInt    eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd lTH Ord.OrdDouble eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd lE  Ord.OrdDouble eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd gTH Ord.OrdDouble eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOrd gE  Ord.OrdDouble eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eEq eQU Eq.EqInt       eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eEq eQU Eq.EqBool      eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eEq eQU Eq.EqDouble    eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eEq nE Eq.EqInt        eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eEq nE Eq.EqBool       eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eEq nE Eq.EqDouble     eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eAnd eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOr  eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (ePrintString s) = refl

  -- Every well typed expression will type check to itself -- completeness
  checkProof : ∀ {e t} → (eT : Γ ⊢ e ∶ t) → checkExp t e ≡ inj₂ eT
  checkProof {t = t} x rewrite inferProof x rewrite =T=Refl t = refl


  -- returnProof : {ssT : (Δ ∷ Γ) ⊢ ss ⇒⇒ Δ'} → Returns ssT → TS.returnStms (toStms ssT)
  -- returnProof (here (ret e')) = SHead SReturn
  -- returnProof (here (vRet {p = p}) ) rewrite p = SHead SReturn
  -- returnProof (here (bStmt ss)) = SHead (SBlock (returnProof ss))
  -- returnProof (here (condElse x x₁)) = SHead (SIfElse {!SHead!} {!!})
  -- returnProof (there {s' = s'} {ss'} x) with p ← returnProof x = {!!}
  -- returnProof (vEnd refl) = {!!}
