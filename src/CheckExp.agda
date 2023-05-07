
open import Agda.Builtin.Equality using (refl; _≡_)
open import Data.List.Relation.Unary.All using (All; reduce); open All
open import Agda.Builtin.Bool using (true; false)

open import TypeCheckerMonad 
open import Util 
open import Javalette.AST renaming (Expr to Exp)
open import TypedSyntax Ident



module CheckExp (Σ : SymbolTab) (Γ : Ctx) where

open Typed Σ renaming (Exp to TypedExp)


unType      :        TypedExp Γ  T  → Exp
unTypeTList : TList (TypedExp Γ) ts → List Exp
unTypeTList []       = []
unTypeTList (x ∷ xs) = unType x ∷ unTypeTList xs

unType (EValue {T} x) with T
...    | int            = eLitInt x
...    | doub           = eLitDoub x
...    | bool   with x
...             | true  = eLitTrue
...             | false = eLitFalse
unType (ENeg p  x)      = neg (unType x)
unType (ENot x)         = not (unType x)
unType (EId id₁ x)      = eVar id₁
unType (EArith p x + y) = eAdd (unType x) plus  (unType y)
unType (EArith p x - y) = eAdd (unType x) minus (unType y)
unType (EArith p x * y) = eMul (unType x) times (unType y)
unType (EArith p x / y) = eMul (unType x) div   (unType y)
unType (EMod x y)       = eMul (unType x) mod   (unType y)
unType (EOrd _ x < y )  = eRel (unType x) lTH   (unType y)
unType (EOrd _ x <= y ) = eRel (unType x) lE    (unType y)
unType (EOrd _ x > y )  = eRel (unType x) gTH   (unType y)
unType (EOrd _ x >= y ) = eRel (unType x) gE    (unType y)
unType (EEq _ x == y)   = eRel (unType x) eQU   (unType y)
unType (EEq _ x != y)   = eRel (unType x) nE    (unType y)
unType (ELogic x && y)  = eAnd (unType x) (unType y)
unType (ELogic x || y)  = eOr  (unType x) (unType y)
unType (EAPP id xs p)   = eApp id (unTypeTList xs)
unType (EPrintStr s)    = eApp (ident "printString") (eString s ∷ [])


data WellTyped (e : Exp) : Set where
  inferred : (T : Type) → (eT : TypedExp Γ T) → (unType eT) ≡ e →  WellTyped e 

data WellTypedList (es : List Exp) : Set where
  inferred : (Ts : List Type) → (eTs : TList (TypedExp Γ) Ts) → unTypeTList eTs ≡ es →  WellTypedList es

pattern _:::_ e t = inferred t e refl

data WellTypedPair (e1 e2 : Exp) : Set where
  inferredP : (T : Type) → (eT1 eT2 : TypedExp Γ T) → (unType eT1) ≡ e1
                                                    → (unType eT2) ≡ e2 → WellTypedPair e1 e2

pattern infP e1 e2 t = inferredP t e1 e2 refl refl



-- Typeching of expressions uses a given context, Γ

inferExp  : (e  :      Exp) → TCM (WellTyped     e )
inferList : (es : List Exp) → TCM (WellTypedList es)
inferList [] = pure (inferred [] [] refl)
inferList (e ∷ es) = do e'  ::: t  ← inferExp e
                        es' ::: ts ← inferList es
                        pure ((e' ∷ es') ::: (t ∷ ts))

inferPair : (e1 e2 : Exp) → TCM (WellTypedPair e1 e2)
inferPair e1 e2 = do e1' ::: t1 ← inferExp e1
                     e2' ::: t2 ← inferExp e2
                     refl ← t1 =?= t2
                     pure (infP e1' e2' t1)


inferExp (eLitFalse)  = pure (EValue false ::: bool)
inferExp (eLitTrue)   = pure (EValue true  ::: bool)
inferExp (eLitInt x)  = pure (EValue x     ::: int)
inferExp (eLitDoub x) = pure (EValue x     ::: doub)
inferExp (eVar x)     = do inScope t p ← lookupCtx x Γ
                           pure (EId x p ::: t)

inferExp (eApp (ident "printString") (eString s ∷ [])) with lookup (ident "printString") Σ
... | just (inList (void ∷ [] , void)  p) = pure (EPrintStr s ::: void)
... | _                                   = error "Mismatch in printString"
inferExp (eApp x es)   = do inList (ts , t) p ← lookupTCM x Σ
                            es' ::: ts' ← inferList es
                            refl ← eqLists ts ts'
                            pure (EAPP x es' p ::: t)

inferExp (eMul e1 op e2) with inferPair e1 e2
... | inj₁ s = error s
... | inj₂ (infP e1' e2' t) with op
...      | times = ifNum   t >>= λ  p    → pure (EArith p e1' (*) e2' ::: t)
...      | div   = ifNum   t >>= λ  p    → pure (EArith p e1' (/) e2' ::: t)
...      | mod   = int =?= t >>= λ {refl → pure (EMod     e1'     e2' ::: t)}

inferExp (eAdd e1 op e2) with inferPair e1 e2
... | inj₁ s = error s
... | inj₂ (infP e1' e2' t) with op
...      | plus  = ifNum t >>= λ p → pure (EArith p e1' (+) e2' ::: t)
...      | minus = ifNum t >>= λ p → pure (EArith p e1' (-) e2' ::: t)

inferExp (eRel e1 op e2) with inferPair e1 e2
... | inj₁ s = error s
... | inj₂ (infP e1' e2' t) with op
...      | lTH = ifOrd t >>= λ p → pure (EOrd p e1' (<)  e2' ::: bool)
...      | lE  = ifOrd t >>= λ p → pure (EOrd p e1' (<=) e2' ::: bool)
...      | gTH = ifOrd t >>= λ p → pure (EOrd p e1' (>)  e2' ::: bool)
...      | gE  = ifOrd t >>= λ p → pure (EOrd p e1' (>=) e2' ::: bool)
...      | eQU = ifEq  t >>= λ p → pure (EEq  p e1' (==) e2' ::: bool)
...      | nE  = ifEq  t >>= λ p → pure (EEq  p e1' (!=) e2' ::: bool)

inferExp (eAnd e1 e2)   = do infP e1' e2' bool ← inferPair e1 e2
                                  where _ → error "And applied to nonBool args"
                             pure (ELogic e1' && e2' ::: bool)
inferExp (eOr e1 e2)    = do infP e1' e2' bool ← inferPair e1 e2
                                  where _ → error "Or applied to nonBool args"
                             pure (ELogic e1' || e2' ::: bool)

inferExp (eString x)   = error "Found string outside of call to printString"
inferExp (neg e) = do e' ::: t ← inferExp e
                      p ← ifNum t
                      pure (ENeg p e' ::: t)
inferExp (not e) = do e' ::: t ← inferExp e
                      refl ← t =?= bool
                      pure (ENot e'  ::: t)


checkExp : (T : Type) → Exp → TCM (TypedExp Γ T)
checkExp t x = do e ::: t' ← inferExp x
                  refl ← t =?= t'
                  pure e
