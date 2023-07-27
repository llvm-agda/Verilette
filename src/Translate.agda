{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any
open import Data.Product using (_×_; _,_; proj₂)

import Data.Bool    as Bool
import Data.Integer as Int
import Data.Float   as Doub

open import Data.List using (List; _∷_; []; _++_; [_]; map) renaming (_ʳ++_ to _++r_)
open import Data.List.Properties using (ʳ++-defn)

open import WellTyped
open import Javalette.AST using (Type; Ident; Item; plus; minus); open Type; open Item
open import TypedSyntax hiding (Γ; Δ; Δ') renaming (Block to newBlock; Ctx to newCtx)


-- Translating from WellTyped to TypedSyntax
module Translate (Σ : SymbolTab) (χ : TypeTab) where

open Expression Σ χ renaming (WFNew to OldWFNew)
open Statements Σ
open WellTyped.Return

open Typed Σ χ
open Valid Σ χ

dropAllId' : Block → newBlock
dropAllId' = map proj₂

dropAllId : Ctx → newCtx
dropAllId = map dropAllId'

simplifyLookup' : (id , t) ∈ Δ → t ∈ (dropAllId' Δ)
simplifyLookup' (here refl) = here refl
simplifyLookup' (there x) = there (simplifyLookup' x)

simplifyLookup : (id , t) ∈' Γ → t ∈' (dropAllId Γ)
simplifyLookup (here px) = here (simplifyLookup' px)
simplifyLookup (there x) = there (simplifyLookup x)

zero : Num T → toSet T
zero NumInt    = Int.0ℤ
zero NumDouble = 0.0


-- Every well typed expression can be transformed into our representation
toExp : Γ ⊢ e ∶ T → Exp (dropAllId Γ) T
toExp (eVar id x)   = EId (simplifyLookup x)
toExp (eLitInt x)   = EValue x
toExp (eLitDoub x)  = EValue x
toExp eLitTrue      = EValue Bool.true
toExp eLitFalse     = EValue Bool.false
toExp (neg p x)     = EArith p   (EValue (zero p)) ArithOp.- (toExp x)
toExp (not x)       = EEq EqBool (EValue Bool.false) EqOp.== (toExp x)
toExp (eIndex a i)  = EIdx (toExp a) (toExp i)
toExp (eDeRef x p p') = EDeRef (toExp x) p p'
toExp (eNull x)     = ENull
toExp (eStruct x)   = EStruct
toExp (eArray n)    = EArray (toNew n)
  where toNew : ∀ {n t t'} → OldWFNew Γ t n t' → WFNew (Exp (dropAllId Γ) int) array t'
        toNew (nType  x _)  = nType _ (toExp x)
        toNew (nArray x ns) = nArray (toNew ns) (toExp x)
toExp (eLength x)        = ELength (toExp x)  -- Transform to normal function call?
toExp (eMod x y)         = EMod     (toExp x)            (toExp y)
toExp (eMul p x y)       = EArith p (toExp x) ArithOp.*  (toExp y)
toExp (eDiv p x y)       = EArith p (toExp x) ArithOp./  (toExp y)
toExp (eAdd p plus  x y) = EArith p (toExp x) ArithOp.+  (toExp y)
toExp (eAdd p minus x y) = EArith p (toExp x) ArithOp.-  (toExp y)
toExp (eEq  opP p x y) with opP
... | eQU                = EEq    p (toExp x) EqOp.==    (toExp y)
... | nE                 = EEq    p (toExp x) EqOp.!=    (toExp y)
toExp (eOrd opP p x y) with opP
... | lTH                = EOrd   p (toExp x) OrdOp.<    (toExp y)
... | lE                 = EOrd   p (toExp x) OrdOp.<=   (toExp y)
... | gTH                = EOrd   p (toExp x) OrdOp.>    (toExp y)
... | gE                 = EOrd   p (toExp x) OrdOp.>=   (toExp y)
toExp (eAnd x y)         = ELogic   (toExp x) LogicOp.&& (toExp y)
toExp (eOr  x y)         = ELogic   (toExp x) LogicOp.|| (toExp y)
toExp (ePrintString s) = EPrintStr s
toExp (eApp id p xs)   = EAPP id (mapToExp xs) p
  where mapToExp : ∀ {es Ts} → AllPair (Γ ⊢_∶_) es Ts → All (Exp (dropAllId Γ)) Ts
        mapToExp [] = []
        mapToExp (x ∷ xs) = toExp x ∷ mapToExp xs


defInit : ∀ {Γ'} → NonVoid χ T → Exp Γ' T
defInit NonVoidInt  = EValue Int.0ℤ
defInit NonVoidDoub = EValue 0.0
defInit NonVoidBool = EValue Bool.false
defInit (NonVoidArray  _) = EArray (nType _ (EValue Int.0ℤ))
defInit (NonVoidStruct _) = EStruct

toDecls : ∀ {is t} → NonVoid χ t → DeclP Σ χ t is (Δ ∷ Γ) Δ' → Stms T (dropAllId ((Δ' ++r Δ) ∷ Γ)) → Stms T (dropAllId (Δ ∷ Γ))
toDecls n [] ss = ss
toDecls n (_∷_ {i = noInit x}  px       is) ss = SDecl _ (defInit n) ∷ toDecls n is ss
toDecls n (_∷_ {i = init x _} (px , e') is) ss = SDecl _ (toExp  e') ∷ toDecls n is ss


toStms : ∀ {T Γ ss Δ Δ'} → _⊢_⇒⇒_ χ T (Δ ∷ Γ) ss Δ' → Stms T (dropAllId (Δ ∷ Γ))
_SCons'_ : ∀ {s} → _⊢_⇒_ χ T (Δ ∷ Γ) s Δ' → Stms T (dropAllId ((Δ' ++ Δ) ∷ Γ)) → Stms T (dropAllId (Δ ∷ Γ))
toStms (x ∷ ss) = x SCons' (toStms ss)
toStms {void} {[]} [] = SReturn vRet ∷ []
toStms {_}    {_}  [] = []

_SCons'_ {Δ = Δ} (decl {Δ' = Δ'} t n is) ss rewrite sym (ʳ++-defn Δ' {Δ}) = toDecls n is ss
empty          SCons' ss = ss
bStmt x        SCons' ss = (SBlock (toStms x)) ∷ ss
ass id x e     SCons' ss = SAss (toExp e) (simplifyLookup x) ∷ ss
assIdx arr i e SCons' ss = (SAssIdx (toExp arr) (toExp i) (toExp e)) ∷ ss
incr id x      SCons' ss = SAss (EArith NumInt (EId (simplifyLookup x)) ArithOp.+ (EValue (Int.+ 1))) (simplifyLookup x) ∷ ss
decr id x      SCons' ss = SAss (EArith NumInt (EId (simplifyLookup x)) ArithOp.- (EValue (Int.+ 1))) (simplifyLookup x) ∷ ss
ret x          SCons' ss = SReturn (Ret (toExp x)) ∷ ss
vRet refl      SCons' ss = SReturn vRet            ∷ ss
cond x s       SCons' ss = SIfElse (toExp x) (s SCons' []) []      ∷ ss
condElse x t f SCons' ss = SIfElse (toExp x) (t SCons' []) (f SCons' []) ∷ ss
while x s      SCons' ss = SWhile (toExp x) (s SCons' []) ∷ ss
sExp x         SCons' ss = SExp (toExp x) ∷ ss
assPtr x p q y SCons' ss = SAssPtr (toExp x) p q (toExp y) ∷ ss
for id e s     SCons' ss = SFor (toExp e) (s SCons' []) ∷ ss
