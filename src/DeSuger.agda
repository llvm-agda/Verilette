

module DeSuger where

open import Data.List

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

deSuger : Stmt → List Stm
deSuger empty              = []
deSuger (decl t is)        = declr t is
deSuger (ass x e)          = ass x e                          ∷ []
deSuger (incr x)           = incDec x inc                     ∷ []
deSuger (decr x)           = incDec x dec                     ∷ []
deSuger (ret e)            = ret e                            ∷ []
deSuger (vRet)             = vRet                             ∷ []
deSuger (cond e y)         = ifElse e (deSuger y) []          ∷ []
deSuger (condElse e x y)   = ifElse e (deSuger x) (deSuger y) ∷ []
deSuger (while e y)        = while e (deSuger y)              ∷ []
deSuger (sExp e)           = sExp e                           ∷ []
deSuger (bStmt (block ss)) = block (deSugerList ss)           ∷ []
  where deSugerList : List Stmt → List Stm
        deSugerList []       = []
        deSugerList (x ∷ xs) = deSuger x ++ deSugerList xs


-- data _⇓_ : (s : Stmt) → (s' : Stmt) → Set where
--   _d_ : cond ⇓ condElse
