{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; ≡-≟-identity; sym)
open import Data.String using (_≟_)

open import Data.List using (List; _∷_; []; _++_) renaming (_ʳ++_ to _++r_)
open import Data.List.Properties using (ʳ++-defn)

open import Javalette.AST using (Ident; ident; Type); open Type
open import Util 
open import TypedSyntax Ident as TS using (SymbolTab; Ctx; Num; Ord; Eq
                                          ; Γ; Δ; Δ'; Δ'')
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
  inferProof (eApp id x xs) = {!!}
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



module ReturnsProof (Σ : SymbolTab) where

  open WellTyped.Statements Σ
  open WellTyped.Return

  open TS.Valid Σ
  open TS.Typed Σ
  open TS.returnStm
  open TS.returnStms

  open Javalette.AST.Item

  open import Translate Σ using (toExp; toStms; _SCons'_; toDecls)


  returnDecl : ∀ {T Γ Δ Δ' t is} (n : TS.NonVoid t)
               {ss : Stms T ((Δ' ++r Δ) ∷ Γ)}
               (is' : DeclP Σ t is (Δ ∷ Γ) Δ')
                    → TS.returnStms ss → TS.returnStms (toDecls n is' ss)
  returnDecl n [] p = p
  returnDecl n (_∷_ {i = noInit x} px is) p = SCon (returnDecl n is p)
  returnDecl n (_∷_ {i = init x e} px is) p = SCon (returnDecl n is p)

  returnProofThere : ∀ {T s ss Δ Δ' Δ''} {sT : _⊢_⇒_ T (Δ ∷ Γ) s Δ'} {ssT : _⊢_⇒⇒_ T _ ss Δ''}
                            → TS.returnStms (toStms ssT) → TS.returnStms (toStms (sT ∷ ssT))
  returnProofThere {sT = Statements.empty} x = x
  returnProofThere {sT = Statements.ret x₁} x       = SHead SReturn
  returnProofThere {sT = Statements.vRet refl} x    = SHead SReturn
  returnProofThere {sT = Statements.condElse x₁ sT sT₁} x = SCon x
  returnProofThere {sT = Statements.bStmt x₁} x     = SCon x
  returnProofThere {sT = Statements.ass id x₁ x₂} x = SCon x
  returnProofThere {sT = Statements.incr id x₁} x   = SCon x
  returnProofThere {sT = Statements.decr id x₁} x   = SCon x
  returnProofThere {sT = Statements.cond x₁ sT} x   = SCon x
  returnProofThere {sT = Statements.while x₁ sT} x  = SCon x
  returnProofThere {sT = Statements.sExp x₁} x      = SCon x
  returnProofThere {Δ = Δ} {sT = Statements.decl {Δ' = Δ'} t n is} x
                       rewrite sym (ʳ++-defn Δ' {Δ}) = returnDecl n is x -- Why is this rewrite necessary?


  returnProof     : ∀ {T ss}    {ssT : _⊢_⇒⇒_ T (Δ ∷ Γ) ss Δ'} → Returns ssT → TS.returnStms (toStms ssT)
  returnProofHere : ∀ {T s ssT} {sT  : _⊢_⇒_  T (Δ ∷ Γ) s  Δ'} → Returns' sT → TS.returnStms (sT SCons' ssT)
  returnProofHere (ret e')  = SHead SReturn
  returnProofHere vRet      = SHead SReturn
  returnProofHere (bStmt x) = SHead (SBlock (returnProof x))
  returnProofHere (condElse x x₁) = SHead (SIfElse (returnProofHere x) (returnProofHere x₁))

  returnProof (there {s' = s'} {ss' = ss'} x) = returnProofThere {sT = s'} {ssT = ss'} (returnProof x)
  returnProof (here x) = returnProofHere  x
  returnProof vEnd     = SHead SReturn



  returnProofReverseDecl : ∀ {T t is} {ssT : Stms T _} {n : TS.NonVoid t} {is' : DeclP Σ t is (Δ ∷ Γ) Δ''}
                                → ¬ TS.returnStms ssT → ¬ TS.returnStms (decl t n is' SCons' ssT)
  returnProofReverseDecl  p = {!!}

  noReturns'Decl : ∀ {T t id p} {e : Exp (Δ ∷ Γ) t}
                        → ¬ (TS.returnStm {T = T} (SDecl t id e p))
  noReturns'Decl ()

  returnProofReverse : ∀ {T ss} {ssT : _⊢_⇒⇒_ T (Δ ∷ Γ) ss Δ'} → TS.returnStms (toStms ssT) → Returns ssT
  returnProofThereReverse : ∀ {T s} {sT : _⊢_⇒_ T (Δ ∷ Γ) s Δ'} → TS.returnStms (sT SCons' SEmpty) → Returns' sT
  returnProofThereReverse {sT = bStmt x₁} (SHead (SBlock x)) = bStmt (returnProofReverse x)
  -- returnProofThereReverse {sT = decl t x₁ x₂} x with () ← returnProofReverseDecl {n = x₁} {is' = x₂} test
  returnProofThereReverse {sT = Statements.decl t x₁ (_∷_ {i = noInit x₂} p is)} x = {!!}
  returnProofThereReverse {sT = Statements.decl t x₁ (_∷_ {i = init x₂ e} p is)} x = {!!}
  returnProofThereReverse {sT = ass id x₁ x₂} (SHead ())
  returnProofThereReverse {sT = ass id x₁ x₂} (SCon ())
  returnProofThereReverse {sT = incr id x₁} (SHead ())
  returnProofThereReverse {sT = incr id x₁} (SCon ())
  returnProofThereReverse {sT = decr id x₁} (SHead ())
  returnProofThereReverse {sT = decr id x₁} (SCon ())
  returnProofThereReverse {sT = ret x₁} (SHead SReturn) = ret _
  returnProofThereReverse {sT = vRet refl} (SHead SReturn) = vRet
  returnProofThereReverse {sT = cond x₁ sT} (SHead (SIfElse x ()))
  returnProofThereReverse {sT = condElse x₁ sT sT₁} (SHead (SIfElse x x₂)) = condElse (returnProofThereReverse x) (returnProofThereReverse x₂)
  returnProofThereReverse {sT = while x₁ sT} (SHead ())
  returnProofThereReverse {sT = while x₁ sT} (SCon ())
  returnProofThereReverse {sT = sExp x₁} (SHead ())
  returnProofThereReverse {sT = sExp x₁} (SCon ())

  returnProofReverse {Γ = []} {T = void} {ssT = []} x = vEnd
  returnProofReverse {Γ = x₁ ∷ Γ} {T = int} {ssT = []} ()
  returnProofReverse {Γ = x₁ ∷ Γ} {T = doub} {ssT = []} ()
  returnProofReverse {Γ = x₁ ∷ Γ} {T = bool} {ssT = []} ()
  returnProofReverse {Γ = x₁ ∷ Γ} {T = void} {ssT = []} ()
  returnProofReverse {Γ = x₁ ∷ Γ} {T = fun T ts} {ssT = []} ()
  returnProofReverse {ssT = empty ∷ ssT} x = there (returnProofReverse x)
  returnProofReverse {ssT = bStmt x₁ ∷ ssT} (SHead (SBlock x)) = here (bStmt (returnProofReverse x))
  returnProofReverse {ssT = bStmt x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = Statements.decl t x₁ is Statements.∷ ssT} x = {!!}
  returnProofReverse {ssT = ass id x₁ x₂ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = incr id x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = decr id x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = ret x₁ ∷ ssT} (SHead SReturn) = here (ret _)
  returnProofReverse {ssT = ret x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {T = .void} {ssT = vRet refl ∷ ssT} (SHead SReturn) = here vRet
  returnProofReverse {T = .void} {ssT = vRet refl ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = cond x₁ x₂ ∷ ssT} (SHead (SIfElse x ()))
  returnProofReverse {ssT = cond x₁ x₂ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = condElse x₁ x₂ x₃ ∷ ssT} (SHead (SIfElse x x₄)) = here (condElse (returnProofThereReverse x) (returnProofThereReverse x₄))
  returnProofReverse {ssT = condElse x₁ x₂ x₃ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = while x₁ x₂ ∷ ssT} (SCon x) = there (returnProofReverse x)
  returnProofReverse {ssT = sExp x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
