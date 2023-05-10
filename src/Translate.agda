
open import Agda.Builtin.Equality using (refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.Product using (_×_; _,_)

import Data.Bool    as Bool
import Data.Integer as Int
import Data.Float   as Doub

open import Data.List using (List; _∷_; []; _++_) renaming (_ʳ++_ to _++r_)
open import Data.List.Properties using (ʳ++-defn)

open import WellTyped
open import Javalette.AST using (Type; Ident; Item; plus; minus); open Type; open Item
open import TypedSyntax Ident


-- Translating from WellTyped to TypedSyntax
module Translate (Σ : SymbolTab) where

open Typed Σ
open Valid Σ

open Expression Σ
open Statements Σ


toZero : NonVoid T → toSet T
toZero {.int}  NonVoidInt  = Int.0ℤ
toZero {.doub} NonVoidDoub = 0.0
toZero {.bool} NonVoidBool = Bool.false

-- Every well typed expression can be transformed into our representation
toExp : Γ ⊢ e ∶ T → Exp Γ T
toExp (eVar id x p) = EId id x
toExp (eLitInt x)   = EValue x
toExp (eLitDoub x)  = EValue x
toExp eLitTrue      = EValue Bool.true
toExp eLitFalse     = EValue Bool.false
toExp (neg p x)     = ENeg p (toExp x)
toExp (not x)       = ENot   (toExp x)
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
  where mapToExp : ∀ {es Ts} → AllPair (Γ ⊢_∶_) es Ts → All (Exp Γ) Ts
        mapToExp [] = []
        mapToExp (x ∷ xs) = toExp x ∷ mapToExp xs


toDecls : ∀ {is t} → NonVoid t → DeclP Σ t is (Δ ∷ Γ) Δ' → Stms T ((Δ' ++r Δ) ∷ Γ) → Stms T (Δ ∷ Γ)
toDecls n [] ss = ss
toDecls n (_∷_ {i = noInit x}  px       is) ss = (SDecl _ _ (EValue (toZero n)) px) SCons toDecls n is ss
toDecls n (_∷_ {i = init x _} (px , e') is) ss = (SDecl _ _ (toExp e')          px) SCons toDecls n is ss

toStms : ∀ {ss Δ Δ'} → _⊢_⇒⇒_ T (Δ ∷ Γ) ss Δ' → Stms T (Δ ∷ Γ)
_SCons'_ : ∀ {s} → _⊢_⇒_ T (Δ ∷ Γ) s Δ' → Stms T ((Δ' ++ Δ) ∷ Γ) → Stms T (Δ ∷ Γ)
toStms []       = SEmpty
toStms (x ∷ ss) = x SCons' (toStms ss)

_SCons'_ {Δ = Δ} (decl {Δ' = Δ'} t n is) ss rewrite sym (ʳ++-defn Δ' {Δ}) = toDecls n is ss
empty          SCons' ss = ss
bStmt x        SCons' ss = (SBlock (toStms x)) SCons ss
ass id x e     SCons' ss = SAss id (toExp e) x SCons ss
incr id x      SCons' ss = SAss id (EArith NumInt (EId id x) ArithOp.+ (EValue (Int.+ 1))) x SCons ss
decr id x      SCons' ss = SAss id (EArith NumInt (EId id x) ArithOp.- (EValue (Int.+ 1))) x SCons ss
ret x          SCons' ss = SReturn (Ret (toExp x)) SCons ss
vRet refl      SCons' ss = SReturn vRet            SCons ss
cond x s       SCons' ss = SIfElse (toExp x) (s SCons' SEmpty) SEmpty      SCons ss
condElse x t f SCons' ss = SIfElse (toExp x) (t SCons' SEmpty) (f SCons' SEmpty) SCons ss
while x s      SCons' ss = SWhile (toExp x) (s SCons' SEmpty) SCons ss
sExp x         SCons' ss = SExp (toExp x) SCons ss


-- checkToStms : ∀ Δ Γ → (ss : List Stmt) → TCM (TS.Valid.Stms T Σ (Δ ∷ Γ))
-- checkToStms {T = T} Δ Γ ss = toStms ∘ proj₂ <$> checkStms T (Δ ∷ Γ) ss 
