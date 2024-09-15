{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_; ≡-≟-identity; sym)
open import Data.String using (_≟_)

open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Properties using (ʳ++-defn)
open import Data.Product using (_×_; _,_; proj₂)

open import Javalette.AST using (Ident; ident; Type); open Type
open import TypeCheck.Util
open import TypedSyntax as TS using (TypeTab; Num; Ord; Eq)

open import WellTyped
open import TypeCheck.CheckExp


module TypeCheck.Proofs where

module ExpressionProofs (Σ : SymbolTab) (χ : TypeTab) (Γ : Ctx) where

  open TypeCheck.CheckExp.CheckExp Σ χ Γ
  open WellTyped.Expression Σ χ


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
  =T=Refl (structT x) rewrite eqIdRefl x = refl
  =T=Refl (array t) rewrite =T=Refl t = refl
  =T=Refl (fun t ts) rewrite =T=Refl t rewrite eqListsRefl ts = refl

  -- Every well typed expression can be infered
  inferProof : ∀ {e t} → (eT : Γ ⊢ e ∶ t) → infer e ≡ inj₂ (eT ::: t)
  inferProof (eLitInt x) = refl
  inferProof (eLitDoub x) = refl
  inferProof eLitTrue = refl
  inferProof eLitFalse = refl
  inferProof (eVar id x) = {!!}
  inferProof (eApp id x xs) = {!!}
  inferProof (neg Num.NumInt eT)    rewrite inferProof eT = refl
  inferProof (neg Num.NumDouble eT) rewrite inferProof eT = refl
  inferProof (not eT) rewrite inferProof eT = refl
  inferProof (eMod eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eIndex x x₁) rewrite inferProof x₁ rewrite inferProof x = refl
  inferProof (eArray p x) = {!!}
  inferProof (eStruct x) = {!!}
  inferProof (eNull x) = {!!}
  inferProof (eDeRef x x₁ x₂) = {!!}
  inferProof (eLength x)   rewrite inferProof x = refl
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
  inferProof (eEq x x₁ x₂ x₃) = {!!}
  inferProof (eAnd eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (eOr  eT eT₁) rewrite inferProof eT rewrite inferProof eT₁ = refl
  inferProof (ePrintString s) = refl

  -- Every well typed expression will type check to itself -- completeness
  checkProof : ∀ {e t} → (eT : Γ ⊢ e ∶ t) → checkExp t e ≡ inj₂ eT
  checkProof {t = t} x rewrite inferProof x rewrite =T=Refl t = refl



module ReturnsProof {Σ : SymbolTab} {χ : TypeTab} {T : Type} where

  open WellTyped.Statements Σ χ T
  open WellTyped.Declarations Σ χ
  open WellTyped.Return

  open TS.Valid (map proj₂ Σ) χ T
  open TS.Typed (map proj₂ Σ) χ
  open TS.returnStm
  open TS.returnStms

  open import Translate Σ χ using (dropAllId; toExp; toStms; _SCons'_; toDecls)


  returnDecl : ∀ {t is} (n : TS.NonVoid χ t)
               {ss : Stms (dropAllId Γ')}
               (is' : Star' (DeclP t) Γ is Γ')
                    → TS.returnStms ss → TS.returnStms (toDecls n is' ss)
  returnDecl n [] p = p
  returnDecl n (noInit px   ∷ is) p = there (returnDecl n is p)
  returnDecl n (init   px e ∷ is) p = there (returnDecl n is p)


  returnProof     :         {ssT : Γ ⊢ ss ⇒⇒ Γ'} → Returns ssT → TS.returnStms (toStms ssT)
  returnProofHere : ∀ {ssT} {sT  : Γ ⊢ s  ⇒  Γ'} → Returns' sT → TS.returnStms (sT SCons' ssT)
  returnProofHere ret         = here SReturn
  returnProofHere (vRet refl) = here SReturn
  returnProofHere (bStmt x)   = here (SBlock (returnProof x))
  returnProofHere (condElse t f) = here (SIfElse (returnProofHere t) (returnProofHere f))

  returnProof (here x)    = returnProofHere  x
  returnProof (vEnd refl) = here SReturn
  returnProof {ssT = s' ∷ _} (there x) with x' ← returnProof x with s'
  ... | empty     = x'
  ... | ret _     = here SReturn
  ... | vRet refl = here SReturn
  ... | decl n is = returnDecl n is x'
  ... | condElse _ _ _ = there x'
  ... | bStmt _        = there x'
  ... | ass _ _ _      = there x'
  ... | incr _ _       = there x'
  ... | decr _ _       = there x'
  ... | cond _ _       = there x'
  ... | while _ _      = there x'
  ... | assIdx _ _ _   = there x'
  ... | for _ _ _      = there x'
  ... | sExp _         = there x'
  ... | assPtr _ _ _ _ = there x'



  -- returnProofReverseDecl : ∀ {T t is} {ssT : Stms T _} {n : TS.NonVoid t} {is' : DeclP Σ t is (Δ ∷ Γ) Δ''}
  --                               → ¬ TS.returnStms ssT → ¬ TS.returnStms (decl t n is' SCons' ssT)
  -- returnProofReverseDecl  p = {!!}

  -- noReturns'Decl : ∀ {T t id p} {e : Exp (Δ ∷ Γ) t}
  --                       → ¬ (TS.returnStm {T = T} (SDecl t id e p))
  -- noReturns'Decl ()

  -- returnProofReverse : ∀ {T ss} {ssT : _⊢_⇒⇒_ T (Δ ∷ Γ) ss Δ'} → TS.returnStms (toStms ssT) → Returns ssT
  -- returnProofThereReverse : ∀ {T s} {sT : _⊢_⇒_ T (Δ ∷ Γ) s Δ'} → TS.returnStms (sT SCons' SEmpty) → Returns' sT
  -- returnProofThereReverse {sT = bStmt x₁} (SHead (SBlock x)) = bStmt (returnProofReverse x)
  -- -- returnProofThereReverse {sT = decl t x₁ x₂} x with () ← returnProofReverseDecl {n = x₁} {is' = x₂} test
  -- returnProofThereReverse {sT = Statements.decl t x₁ (_∷_ {i = noInit x₂} p is)} x = {!!}
  -- returnProofThereReverse {sT = Statements.decl t x₁ (_∷_ {i = init x₂ e} p is)} x = {!!}
  -- returnProofThereReverse {sT = ass id x₁ x₂} (SHead ())
  -- returnProofThereReverse {sT = ass id x₁ x₂} (SCon ())
  -- returnProofThereReverse {sT = incr id x₁} (SHead ())
  -- returnProofThereReverse {sT = incr id x₁} (SCon ())
  -- returnProofThereReverse {sT = decr id x₁} (SHead ())
  -- returnProofThereReverse {sT = decr id x₁} (SCon ())
  -- returnProofThereReverse {sT = ret x₁} (SHead SReturn) = ret _
  -- returnProofThereReverse {sT = vRet refl} (SHead SReturn) = vRet
  -- returnProofThereReverse {sT = cond x₁ sT} (SHead (SIfElse x ()))
  -- returnProofThereReverse {sT = condElse x₁ sT sT₁} (SHead (SIfElse x x₂)) = condElse (returnProofThereReverse x) (returnProofThereReverse x₂)
  -- returnProofThereReverse {sT = while x₁ sT} (SHead ())
  -- returnProofThereReverse {sT = while x₁ sT} (SCon ())
  -- returnProofThereReverse {sT = sExp x₁} (SHead ())
  -- returnProofThereReverse {sT = sExp x₁} (SCon ())

  -- returnProofReverse {Γ = []} {T = void} {ssT = []} x = vEnd
  -- returnProofReverse {Γ = x₁ ∷ Γ} {T = int} {ssT = []} ()
  -- returnProofReverse {Γ = x₁ ∷ Γ} {T = doub} {ssT = []} ()
  -- returnProofReverse {Γ = x₁ ∷ Γ} {T = bool} {ssT = []} ()
  -- returnProofReverse {Γ = x₁ ∷ Γ} {T = void} {ssT = []} ()
  -- returnProofReverse {Γ = x₁ ∷ Γ} {T = fun T ts} {ssT = []} ()
  -- returnProofReverse {ssT = empty ∷ ssT} x = there (returnProofReverse x)
  -- returnProofReverse {ssT = bStmt x₁ ∷ ssT} (SHead (SBlock x)) = here (bStmt (returnProofReverse x))
  -- returnProofReverse {ssT = bStmt x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = Statements.decl t x₁ is Statements.∷ ssT} x = {!!}
  -- returnProofReverse {ssT = ass id x₁ x₂ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = incr id x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = decr id x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = ret x₁ ∷ ssT} (SHead SReturn) = here (ret _)
  -- returnProofReverse {ssT = ret x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {T = .void} {ssT = vRet refl ∷ ssT} (SHead SReturn) = here vRet
  -- returnProofReverse {T = .void} {ssT = vRet refl ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = cond x₁ x₂ ∷ ssT} (SHead (SIfElse x ()))
  -- returnProofReverse {ssT = cond x₁ x₂ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = condElse x₁ x₂ x₃ ∷ ssT} (SHead (SIfElse x x₄)) = here (condElse (returnProofThereReverse x) (returnProofThereReverse x₄))
  -- returnProofReverse {ssT = condElse x₁ x₂ x₃ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = while x₁ x₂ ∷ ssT} (SCon x) = there (returnProofReverse x)
  -- returnProofReverse {ssT = sExp x₁ ∷ ssT} (SCon x) = there (returnProofReverse x)
