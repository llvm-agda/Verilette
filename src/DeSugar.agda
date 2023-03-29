module DeSugar where

open import Data.List using (List; [] ; _∷_; _++_)

open import Javalette.AST


data incDecOp : Set where inc dec : incDecOp

data Stm : Set where
    block    : (b : List Stm) → Stm
    decl     : (t : Type) (i : Ident) → Stm
    ass      : (x : Ident) (e : Expr) → Stm
    incDec   : (x : Ident) → incDecOp → Stm
    ret      : (e : Expr) → Stm
    vRet     : Stm
    ifElse   : (e : Expr) (s₁ s₂ : List Stm) → Stm
    while    : (e : Expr) (s : List Stm) → Stm
    sExp     : (e : Expr) → Stm

declr : (t : Type) → List Item → List Stm
declr t [] = []
declr t (noInit x ∷ xs) = decl t x ∷           declr t xs
declr t (init x e ∷ xs) = decl t x ∷ ass x e ∷ declr t xs

deSugar     :      Stmt → List Stm
deSugarList : List Stmt → List Stm
deSugar empty              = []
deSugar (decl t is)        = declr t is
deSugar (ass x e)          = ass x e                          ∷ []
deSugar (incr x)           = incDec x inc                     ∷ []
deSugar (decr x)           = incDec x dec                     ∷ []
deSugar (ret e)            = ret e                            ∷ []
deSugar (vRet)             = vRet                             ∷ []
deSugar (cond e y)         = ifElse e (deSugar y) []          ∷ []
deSugar (condElse e x y)   = ifElse e (deSugar x) (deSugar y) ∷ []
deSugar (while e y)        = while e (deSugar y)              ∷ []
deSugar (sExp e)           = sExp e                           ∷ []
deSugar (bStmt (block ss)) = block (deSugarList ss)           ∷ []

deSugarList []       = []
deSugarList (x ∷ xs) = deSugar x ++ deSugarList xs


-- data _⇓_ : (s : Stmt) → (s' : Stmt) → Set where
--   _d_ : cond ⇓ condElse
