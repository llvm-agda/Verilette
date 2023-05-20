{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.Product using (_×_; _,_)

import Data.Bool    as Bool
import Data.Integer as Int
import Data.Float   as Doub

open import Data.List using (List; _∷_; []; _++_; [_]) renaming (_ʳ++_ to _++r_)
open import Data.List.Properties using (ʳ++-defn)

open import WellTyped
open import Javalette.AST using (Type; Ident; Item; plus; minus); open Type; open Item
open import TypedSyntax


-- Translating from WellTyped to TypedSyntax
module Translate (Σ : SymbolTab) (χ : TypeTab) where

open Expression Σ  renaming (WFNew to OldWFNew)
open Statements Σ
open WellTyped.Return

open Typed Σ
open Valid Σ χ


-- Every well typed expression can be transformed into our representation
toExp : _⊢_∶_ χ Γ e T → Exp χ Γ T
toExp (eVar id x p) = EId id x
toExp (eLitInt x)   = EValue x
toExp (eLitDoub x)  = EValue x
toExp eLitTrue      = EValue Bool.true
toExp eLitFalse     = EValue Bool.false
toExp (neg p x)     = ENeg p (toExp x)
toExp (not x)       = ENot   (toExp x)
toExp (eIndex a i)  = EIdx (toExp a) (toExp i)
toExp (eDeRef x p p') = EDeRef (toExp x) p p'
toExp (eNull x)     = ENull
toExp (eStruct x)   = EStruct
toExp (eArray n)    = EArray (toNew n)
  where toNew : ∀ {n t t'} → OldWFNew χ Γ t n t' → WFNew χ Γ t'
        toNew (nType  x _)  = nType _ (toExp x)
        toNew (nArray x ns) = nArray (toNew ns) (toExp x)
toExp (eLength x)   = ELength (toExp x)  -- Transform to normal function call?
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
  where mapToExp : ∀ {es Ts} → AllPair (_⊢_∶_ χ Γ) es Ts → All (Exp χ Γ) Ts
        mapToExp [] = []
        mapToExp (x ∷ xs) = toExp x ∷ mapToExp xs

toZero : NonVoid T → Exp χ Γ T
toZero NonVoidInt  = EValue Int.0ℤ
toZero NonVoidDoub = EValue 0.0
toZero NonVoidBool = EValue Bool.false
toZero (NonVoidArray  _) = EArray (nType _ (EValue Int.0ℤ))
toZero NonVoidStruct = EStruct


toDecls : ∀ {is t} → NonVoid t → DeclP Σ χ t is (Δ ∷ Γ) Δ' → Stms T ((Δ' ++r Δ) ∷ Γ) → Stms T (Δ ∷ Γ)
toDecls n [] ss = ss
toDecls n (_∷_ {i = noInit x}  px       is) ss = (SDecl _ _ (toZero n) px) SCons toDecls n is ss
toDecls n (_∷_ {i = init x _} (px , e') is) ss = (SDecl _ _ (toExp e')          px) SCons toDecls n is ss


toStms : ∀ {T Γ ss Δ Δ'} → _⊢_⇒⇒_ χ T (Δ ∷ Γ) ss Δ' → Stms T (Δ ∷ Γ)
_SCons'_ : ∀ {s} → _⊢_⇒_ χ T (Δ ∷ Γ) s Δ' → Stms T ((Δ' ++ Δ) ∷ Γ) → Stms T (Δ ∷ Γ)
toStms (x ∷ ss) = x SCons' (toStms ss)
toStms {void} {[]} [] = (SReturn vRet) SCons SEmpty
toStms {_}    {_}  [] = SEmpty

_SCons'_ {Δ = Δ} (decl {Δ' = Δ'} t n is) ss rewrite sym (ʳ++-defn Δ' {Δ}) = toDecls n is ss
empty          SCons' ss = ss
bStmt x        SCons' ss = (SBlock (toStms x)) SCons ss
ass id x e     SCons' ss = SAss id (toExp e) x SCons ss
assIdx arr i e SCons' ss = (SAssIdx (toExp arr) (toExp i) (toExp e)) SCons ss
incr id x      SCons' ss = SAss id (EArith NumInt (EId id x) ArithOp.+ (EValue (Int.+ 1))) x SCons ss
decr id x      SCons' ss = SAss id (EArith NumInt (EId id x) ArithOp.- (EValue (Int.+ 1))) x SCons ss
ret x          SCons' ss = SReturn (Ret (toExp x)) SCons ss
vRet refl      SCons' ss = SReturn vRet            SCons ss
cond x s       SCons' ss = SIfElse (toExp x) (s SCons' SEmpty) SEmpty      SCons ss
condElse x t f SCons' ss = SIfElse (toExp x) (t SCons' SEmpty) (f SCons' SEmpty) SCons ss
while x s      SCons' ss = SWhile (toExp x) (s SCons' SEmpty) SCons ss
for id e s     SCons' ss = SFor id (toExp e) (s SCons' SEmpty) SCons ss
sExp x         SCons' ss = SExp (toExp x) SCons ss
assPtr x p q y SCons' ss = SAssPtr (toExp x) p q (toExp y) SCons ss
