open import Agda.Builtin.Equality using (refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any
open import Data.List.Relation.Unary.Any.Properties using () renaming (gmap to anyMap)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise); open Pointwise
open import Data.Product using (_×_; _,_; proj₂)

import Data.Bool    as Bool
import Data.Integer as Int
import Data.Float   as Doub

open import Data.List using (List; _∷_; []; _++_; [_]; map; foldr) renaming (_ʳ++_ to _++r_)
open import Data.List.Properties using (ʳ++-defn)
open import Function using (_∘_; const; case_of_)

open import WellTyped
open import Javalette.AST using (Type; Ident; Item; plus; minus); open Type; open Item
open import TypedSyntax hiding (Γ; Γ'; Δ; Δ') renaming (Block to newBlock; Ctx to newCtx; SymbolTab to newSymbolTab)


-- Translating from WellTyped to TypedSyntax
module Translate (Σ : SymbolTab) (χ : TypeTab) where

open Expression Σ χ
open Statements Σ χ
open Declarations Σ χ
open WellTyped.Return

open Typed (map proj₂ Σ) χ
open Valid (map proj₂ Σ) χ

dropAllId' : Block → newBlock
dropAllId' = map proj₂

dropAllId : Ctx → newCtx
dropAllId = map dropAllId'

simplifyLookup : (id , t) ∈' Γ → t ∈' (dropAllId Γ)
simplifyLookup = anyMap (anyMap λ {refl → refl})

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
toExp (neg p x)     = EOp (OpNum p ArithOp.-)   (EValue (zero p))   (toExp x)
toExp (not x)       = EOp (OpEq EqBool EqOp.==) (EValue Bool.false) (toExp x)
toExp (eIndex a i)  = EIdx (toExp a) (toExp i)
toExp (eDeRef x p p') = EDeRef (toExp x) p p'
toExp (eNull x)     = EValue 0
toExp (eStruct x)   = EStruct
toExp (eArray _ ns) = EArray (toNew ns)
  where toNew : ∀ {n ns t} → All (Γ ⊢_∶ int ∘ deLen) (n ∷ ns) → WFNew (Exp (dropAllId Γ) int) array (foldr (const array) t (n ∷ ns))
        toNew (px ∷ [])          = nType  (toExp px)
        toNew (px ∷ pxs@(_ ∷ _)) = nArray (toExp px) (toNew pxs)
toExp (eLength x)        = ELength (toExp x)  -- Transform to normal function call?
toExp (eMod x y)         = EOp OpMod     (toExp x)            (toExp y)
toExp (eMul p x y)       = EOp (OpNum p ArithOp.*) (toExp x) (toExp y)
toExp (eDiv p x y)       = EOp (OpNum p ArithOp./) (toExp x) (toExp y)
toExp (eAdd p plus  x y) = EOp (OpNum p ArithOp.+) (toExp x) (toExp y)
toExp (eAdd p minus x y) = EOp (OpNum p ArithOp.-) (toExp x) (toExp y)
toExp (eEq  op p x y)    = EOp (OpEq p op') (toExp x) (toExp y)
  where op' = case op of λ {eQU → EqOp.==; nE → EqOp.!=}
toExp (eOrd op p x y)    = EOp (OpOrd p op')    (toExp x) (toExp y)
  where op' = case op of λ {lTH → OrdOp.< ; lE → OrdOp.<= ; gTH → OrdOp.> ; gE → OrdOp.>=}
toExp (eAnd x y)         = EOp (OpLogic LogicOp.&&) (toExp x) (toExp y)
toExp (eOr  x y)         = EOp (OpLogic LogicOp.||) (toExp x) (toExp y)
toExp (ePrintString s) = EPrintStr s
toExp (eApp id p xs)   = EAPP (anyMap (λ {refl → refl}) p) (mapToExp xs)
  where mapToExp : ∀ {es Ts} → Pointwise (Γ ⊢_∶_) es Ts → All (Exp (dropAllId Γ)) Ts
        mapToExp [] = []
        mapToExp (x ∷ xs) = toExp x ∷ mapToExp xs


defInit : ∀ {Γ'} → NonVoid χ T → Exp Γ' T
defInit NonVoidInt  = EValue Int.0ℤ
defInit NonVoidDoub = EValue 0.0
defInit NonVoidBool = EValue Bool.false
defInit (NonVoidArray  _) = EArray (nType (EValue Int.0ℤ))
defInit (NonVoidStruct _) = EValue 0

toDecls : ∀ {is t} → NonVoid χ t → Star' (DeclP t) Γ is Γ' → Stms T (dropAllId Γ') → Stms T (dropAllId Γ)
toDecls n  []                ss = ss
toDecls n (noInit id   ∷ ds) ss = SDecl _ (defInit n) ∷ toDecls n ds ss
toDecls n (init   id e ∷ ds) ss = SDecl _ (toExp e)   ∷ toDecls n ds ss


toStms   : ∀ {ss} → _⊢_⇒⇒_ T Γ ss Γ'                         → Stms T (dropAllId Γ)
_SCons'_ : ∀ {s}  → _⊢_⇒_  T Γ s  Γ' → Stms T (dropAllId Γ') → Stms T (dropAllId Γ)
toStms (x ∷ ss)                  = x SCons' (toStms ss)
toStms {T = void} {Γ = _ ∷ _} [] = SReturn vRet ∷ []
toStms {_}        {_}         [] = []

decl n is      SCons' ss = toDecls n is ss
empty          SCons' ss = ss
bStmt x        SCons' ss = SBlock (toStms x) ∷ ss
ass id x e     SCons' ss = SAss (simplifyLookup x) (toExp e) ∷ ss
assIdx arr i e SCons' ss = SAssIdx (toExp arr) (toExp i) (toExp e) ∷ ss
incr id x      SCons' ss = let x' = simplifyLookup x in SAss x' (EOp (OpNum NumInt ArithOp.+) (EId x') (EValue Int.1ℤ)) ∷ ss
decr id x      SCons' ss = let x' = simplifyLookup x in SAss x' (EOp (OpNum NumInt ArithOp.-) (EId x') (EValue Int.1ℤ)) ∷ ss
ret x          SCons' ss = SReturn (Ret (toExp x)) ∷ ss
vRet refl      SCons' ss = SReturn vRet            ∷ ss
cond x s       SCons' ss = SIfElse (toExp x) (s SCons' []) []      ∷ ss
condElse x t f SCons' ss = SIfElse (toExp x) (t SCons' []) (f SCons' []) ∷ ss
while x s      SCons' ss = SWhile  (toExp x) (s SCons' []) ∷ ss
sExp x         SCons' ss = SExp (toExp x) ∷ ss
assPtr x p q y SCons' ss = SAssPtr (toExp x) p q (toExp y) ∷ ss
for id e s     SCons' ss = SFor (toExp e) (s SCons' []) ∷ ss
