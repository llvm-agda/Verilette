
open import Data.String using (String; unwords; unlines; intersperse; _++_; length)
open import Data.List using (List; _∷_; []; map)

open import Data.Product using (_×_; _,_)
open import Data.List.Relation.Unary.Any using (Any); open Any
open import Data.List.Relation.Unary.All using (All); open All

open import Data.Nat using (ℕ; suc; zero)

open import Data.Nat.Show     using () renaming (show to showℕ)
open import Data.Bool.Show    using () renaming (show to showB)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Float        using () renaming (show to showℝ)

open import Function using (_$_; _∘_)

open import Javalette.AST using (ident; RelOp) renaming (Ident to Id; Type to OldType)
open import Code
open import TypedSyntax using (ArithOp; _∈_)
open ArithOp renaming (* to mul)


-- printing llvm code
module Compile.Print where

pType :      Type → String
pTypeList : List Type → String
pType (lint n)    = "i" ++ showℕ (suc n)
pType float       = "double"
pType void        = "void"
pType (t *)       = pType t ++ "*"
pType (array n t) = "[ " ++ showℕ n ++ " x " ++ pType t ++ " ]"
pType (struct ts) = "{ " ++ pTypeList ts ++ " }"
pType (named (ident x)) = "%" ++ x
pType (fun t ts)  = pType t ++ " (" ++ pTypeList ts ++ ")"

pTypeList [] = ""
pTypeList (x ∷ []) = pType x
pTypeList (y ∷ x ∷ xs) = pType y ++ ", " ++ pTypeList (x ∷ xs)


pOperand : Operand T → String
pOperand {T} (const x) with T
... | float = showℝ x
... | t *   = "null"  -- is null the only ptr constant?
... | (lint n) with n
... | suc _ = showℤ x
... | zero  = showB x
pOperand {_} (local  (ident x)) = "%" ++ x
pOperand {_} (global (ident x)) = "@" ++ x

pPairOperand : (x y : Operand T) → String
pPairOperand {T} x y = pType T ++ " " ++ pOperand x ++ " , " ++ pOperand y

pTypeOper : Operand T → String
pTypeOper {T} x = pType T ++ " " ++ pOperand x

pLabel : Label → String
pLabel (ident x) = "label %" ++ x

-- Helper functions for pInst
private
  pArith : FirstClass T → ArithOp → String
  pArith (lint n)  = λ { + →  "add"; - →  "sub"; mul →  "mul"; / → "sdiv"}
  pArith (ptrFC t) = λ { + →  "add"; - →  "sub"; mul →  "mul"; / → "sdiv"} -- Unreachable
  pArith float     = λ { + → "fadd"; - → "fsub"; mul → "fmul"; / → "fdiv"}

  open RelOp
  pCmp : FirstClass T → RelOp → String
  pCmp (lint  _)  = ("icmp " ++_) ∘ λ { lTH → "slt"; lE → "sle"; gTH → "sgt"; gE → "sge"; eQU →  "eq"; nE →  "ne"}
  pCmp (ptrFC _)  = ("icmp " ++_) ∘ λ { lTH → "slt"; lE → "sle"; gTH → "sgt"; gE → "sge"; eQU →  "eq"; nE →  "ne"}
  pCmp float      = ("fcmp " ++_) ∘ λ { lTH → "ult"; lE → "ule"; gTH → "ugt"; gE → "uge"; eQU → "ueq"; nE → "une"}

  pCall : All Operand Ts → String
  pCall (_∷_ {t} y (x ∷ xs)) = pType t ++ " " ++ pOperand y ++ ", " ++ pCall (x ∷ xs)
  pCall (_∷_ {t} x [])       = pType t ++ " " ++ pOperand x
  pCall [] = ""

  pPhi : List (Operand T × Id) → List String
  pPhi = map λ {(x , ident l) → "[ " ++ pOperand x ++ ", %" ++ l ++ " ]"}

  pTypeDeptr : ∀ {t} → Operand (t *) → String
  pTypeDeptr {t} x = pType t

  pGetElem : ∀ {t t'} → GetElem t t' → List String
  pGetElem [] = []
  pGetElem (array  x ∷ xs) = pTypeOper x ∷ pGetElem xs
  pGetElem (struct x ∷ xs) = ("i32 " ++ showℕ (toℕ x)) ∷ pGetElem xs
    where toℕ : ∀ {t : Type} {ts} → t ∈ ts → ℕ
          toℕ (here px) = 0
          toℕ (there x) = suc (toℕ x)


pInst : Instruction T → String
pInst {T} inst with inst
... | arith p op x y = unwords $ pArith p op ∷ pPairOperand x y ∷ []
... | cmp   p op x y = unwords $ pCmp   p op ∷ pPairOperand x y ∷ []
... | srem       x y = unwords $ "srem"      ∷ pPairOperand x y ∷ []
... | alloc t        = unwords $ "alloca" ∷ pType t     ∷ []
... | load x         = unwords $ "load"   ∷ pType T     ∷ "," ∷ pTypeOper x ∷ []
... | store o p      = unwords $ "store"  ∷ pTypeOper o ∷ "," ∷ pTypeOper p ∷ []
... | call (global (ident "printString")) (x ∷ []) = "call void @printString( i8* " ++ pOperand x ++ ")"
... | call {T} x xs  = unwords $ "call"   ∷ pType T ∷ (pOperand x ++ "(" ) ∷ pCall xs ∷ ")" ∷ []
... | ptrToInt x     = unwords $ "ptrtoint" ∷ pTypeOper x ∷ "to" ∷ pType i32 ∷ []
... | bitCast x t'   = unwords $ "bitcast"  ∷ pTypeOper x ∷ "to" ∷ pType t' ∷ []
... | getElemPtr o i x = intersperse ", " $ ("getelementptr " ++ pTypeDeptr o) ∷ pTypeOper o ∷ ("i32 " ++ showℕ i) ∷ pGetElem x
... | phi x  = unwords $ "phi" ∷ pType T ∷ intersperse ", " (pPhi x) ∷ []
... | vret   = unwords $ "ret" ∷ "void" ∷ []
... | ret x  = unwords $ "ret" ∷ pTypeOper x ∷ []
... | jmp x  = unwords $ "br"  ∷ pLabel x ∷ []
... | branch x t f =  unwords $ "br" ∷ "i1" ∷ pOperand x ∷ "," ∷ pLabel t ∷ "," ∷ pLabel f ∷ []
... | label (ident x) = "error: lables should have been handled in pCode"

-- Should maybe reverse the order of code when compiling
pCode : Code → String
pCode [] = ""
pCode (label (ident l) ∷ xs) = pCode xs ++ l ++ ": \n"
pCode (x ∷ xs)      = pCode xs ++ "  " ++                        pInst x ++ "\n"
pCode (o := x ∷ xs) = pCode xs ++ "  " ++ pOperand o ++ " = " ++ pInst x ++ "\n"

pFun : {Σ : SymbolTab} → Id → FunDef Σ Ts T → String
pFun {T = T} (ident id) def =
     let header = unwords $ "define" ∷ pType T ∷ ("@" ++ id) ∷ pParams ∷ "{" ∷ []
     in intersperse "\n" $ header ∷ pCode body ∷ "}" ∷ []
  where open FunDef def
        pParams = "(" ++ intersperse ", " (map (λ {(ident i , t) → pType t ++ " %" ++ i}) params) ++ ")"

pProgram : llvmProgram → String
pProgram p = intersperse "\n\n" $ pCalloc ∷ unlines pBuiltIn ∷ unlines pTypes ∷ unlines pStrings ∷ pDefs hasDefs
  where open llvmProgram p
        pCalloc : String
        pCalloc = "declare i8* @calloc(i32, i32)"

        pStrings : List String
        pStrings = map (λ {(ident i , s) →
                       "@" ++ i ++ " = internal constant [ " ++ showℕ (length s) ++ " x i8 ] c\"" ++ s ++ "\""}) Strings

        pBuiltIn : List String
        pBuiltIn = map (λ
                     { (ident "printString" , _) → "declare void @printString(i8*)" -- since we use a "hack" for printString
                     ; (ident i , ts , t) →
                            "declare " ++ pType t ++ " @" ++ i ++ "(" ++ intersperse ", " (map pType ts) ++ ")" }) BuiltIn

        pDefs : ∀ {Σ' Σ} → FunList' Σ' Σ → List String
        pDefs []                 = []
        pDefs (_∷_ {i , _} x xs) = pFun i x ∷ pDefs xs

        pTypes : List String
        pTypes = map (λ { (ident x , ts) → "%" ++ x ++ " = type { " ++ intersperse ", " (map pType ts) ++ "}"  })  χ
