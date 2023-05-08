{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Product using (_×_; _,_; ∃)
open import Data.List using (List; _∷_; []; zip; _++_)

import Data.Bool as Bool
import Data.Integer as Int
import Data.Float as Doub
open import Data.Empty using (⊥)

open import Function using (_$_; _∘_; case_of_; case_return_of_)

open import Javalette.AST
open import TypedSyntax Ident as TS using (Block; Ctx; SymbolTab; _∈'_; _∈_; _∉_; Num; Eq; Ord; Return;  toSet) 
open Return 
open import TypeCheckerMonad
open import Util
open import TypeChecker using (_notIn_)

module WellTyped where

variable
  T  : Type
  Ts : List Type
  Γ : Ctx
  Δ Δ' : Block
  e e' x y : Expr
  es : List Expr


_++r_ : {A : Set} → List A → List A → List A
[] ++r ys = ys
(x ∷ xs) ++r ys = xs ++r (x ∷ ys)

data AllPair {A B : Set} (P : A → B → Set) : List A → List B → Set where
  [] : AllPair P [] []
  _∷_ : ∀ {x y xs ys} → P x y → AllPair P xs ys → AllPair P (x ∷ xs) (y ∷ ys)


data OrdOp : RelOp → Set where
    lTH : OrdOp lTH
    lE  : OrdOp lE
    gTH : OrdOp gTH
    gE  : OrdOp gE

data EqOp : RelOp → Set where
    eQU : EqOp eQU
    nE  : EqOp nE
  

module Expression (Σ : SymbolTab) where

  -- Typing judgements 
  data _⊢_∶_ (Γ : Ctx) : (e : Expr) → Type → Set where
    eLitInt   : ∀ x → Γ ⊢ eLitInt x ∶ int
    eLitDoub  : ∀ x → Γ ⊢ eLitDoub x ∶ doub
    eLitTrue  : Γ ⊢ eLitTrue ∶ bool
    eLitFalse : Γ ⊢ eLitFalse ∶ bool

    eVar : ∀ {t} id → (id , t) ∈' Γ → Γ ⊢ eVar id ∶ t
    eApp : ∀ id → (id , Ts , T) ∈ Σ → AllPair (Γ ⊢_∶_) es Ts → Γ ⊢ eApp id es ∶ T

    neg : Num T → Γ ⊢ e ∶ T    → Γ ⊢ neg e ∶ T
    not :         Γ ⊢ e ∶ bool → Γ ⊢ not e ∶ bool

    eMod : (Γ ⊢ x ∶ int) → (Γ ⊢ y ∶ int) → Γ ⊢ eMul x mod y ∶ int
    eMul : Num T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eMul x times y ∶ T
    eDiv : Num T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eMul x div y ∶ T
    eAdd : Num T → (op : _) → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eAdd x op y ∶ T

    eOrd : ∀ {op} → OrdOp op → Ord T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool
    eEq  : ∀ {op} → EqOp  op → Eq  T → (Γ ⊢ x ∶ T) → (Γ ⊢ y ∶ T) → Γ ⊢ eRel x op y ∶ bool

    eAnd : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eAnd x y ∶ bool
    eOr  : (Γ ⊢ x ∶ bool) → (Γ ⊢ y ∶ bool) → Γ ⊢ eOr  x y ∶ bool

    -- eString is not wellTyped on its own
    ePrintString : ∀ s → Γ ⊢ eApp (ident "printString") (eString s ∷ []) ∶ void

  liftCtx : Γ ⊢ e ∶ T  →  ([] ∷ Γ) ⊢ e ∶ T
  liftCtx (eLitInt x) = eLitInt x
  liftCtx (eLitDoub x) = eLitDoub x
  liftCtx eLitTrue = eLitTrue
  liftCtx eLitFalse = eLitFalse
  liftCtx (eVar id x) = eVar id (there x)
  liftCtx (eApp id x es) = eApp id x (mapLiftCtx es)
    where mapLiftCtx : ∀ {es ts} → AllPair (Γ ⊢_∶_) es ts → AllPair (([] ∷ Γ) ⊢_∶_) es ts
          mapLiftCtx [] = []
          mapLiftCtx (x ∷ xs) = liftCtx x ∷ mapLiftCtx xs
  liftCtx (neg x x₁) = neg x (liftCtx x₁)
  liftCtx (not x) = not (liftCtx x)
  liftCtx (eMod x y) = eMod (liftCtx x) (liftCtx y)
  liftCtx (eMul p x y) = eMul p (liftCtx x) (liftCtx y)
  liftCtx (eDiv p x y) = eDiv p (liftCtx x) (liftCtx y)
  liftCtx (eAdd p op x y) = eAdd p op (liftCtx x) (liftCtx y)
  liftCtx (eOrd p op x y) = eOrd p op (liftCtx x) (liftCtx y)
  liftCtx (eEq p p' x y) = eEq p p' (liftCtx x) (liftCtx y)
  liftCtx (eAnd x y) = eAnd (liftCtx x) (liftCtx y)
  liftCtx (eOr x y) = eOr (liftCtx x) (liftCtx y)
  liftCtx (ePrintString s) = ePrintString s


  module _ where
    open TS.Typed 

    -- Every well typed expression can be transformed into our representation
    toExp : Γ ⊢ e ∶ T → Exp Σ Γ T
    toExp (eVar id x)  = EId id x
    toExp (eLitInt x)  = EValue x
    toExp (eLitDoub x) = EValue x
    toExp eLitTrue     = EValue Bool.true
    toExp eLitFalse    = EValue Bool.false
    toExp (neg p x) = ENeg p (toExp x)
    toExp (not x)   = ENot (toExp x)
    toExp (eMod x y)   = EMod     (toExp x)      (toExp y)
    toExp (eMul p x y) = EArith p (toExp x) TS.* (toExp y)
    toExp (eDiv p x y) = EArith p (toExp x) TS./ (toExp y)
    toExp (eAdd p plus  x y) = EArith p (toExp x) TS.+ (toExp y)
    toExp (eAdd p minus x y) = EArith p (toExp x) TS.- (toExp y)
    toExp (eEq  opP p x y) with opP
    ... | eQU = EEq p (toExp x) TS.== (toExp y)
    ... | nE  = EEq p (toExp x) TS.!= (toExp y)
    toExp (eOrd opP p x y) with opP
    ... | lTH = EOrd p (toExp x) TS.<  (toExp y)
    ... | lE  = EOrd p (toExp x) TS.<= (toExp y)
    ... | gTH = EOrd p (toExp x) TS.>  (toExp y)
    ... | gE  = EOrd p (toExp x) TS.>= (toExp y)
    toExp (eAnd x y) = ELogic (toExp x) TS.&& (toExp y)
    toExp (eOr  x y) = ELogic (toExp x) TS.|| (toExp y)
    toExp (ePrintString s) = EPrintStr s
    toExp (eApp id p xs) = EAPP id (mapToExp xs) p
      where mapToExp : ∀ {es Ts} → AllPair (Γ ⊢_∶_) es Ts →  All (Exp Σ Γ) Ts
            mapToExp [] = []
            mapToExp (x ∷ xs) = toExp x ∷ mapToExp xs


  module _ (Γ : Ctx) where
    pattern _:::_ e t = t , e 

    infer : (e : Expr) → TCM (∃ (Γ ⊢ e ∶_))

    inferList : (es : List Expr) → TCM (∃ (AllPair (Γ ⊢_∶_) es) )
    inferList [] = pure ([] ::: [])
    inferList (e ∷ es) = do e'  ::: t  ← infer e
                            es' ::: ts ← inferList es
                            pure ((e' ∷ es') ::: (t ∷ ts))

    inferPair : (x y : Expr) → TCM (∃ (λ t → (Γ ⊢ x ∶ t) × (Γ ⊢ y ∶ t) ))
    inferPair x y = do x' ::: t1 ← infer x
                       y' ::: t2 ← infer y
                       refl ← t1 =?= t2
                       pure ((x' , y') ::: t1)

    infer (eVar x) = do inScope t p ← lookupCtx x Γ
                        pure ((eVar x p) ::: t)
    infer (eLitInt x ) = pure (eLitInt  x ::: int)
    infer (eLitDoub x) = pure (eLitDoub x ::: doub)
    infer (eLitTrue  ) = pure (eLitTrue  ::: bool)
    infer (eLitFalse ) = pure (eLitFalse ::: bool)
    infer (eString x) = error "encountered string outside of printString"
    infer (neg e) = do e' ::: t ← infer e
                       p ← ifNum t
                       pure (neg p e' ::: t)
    infer (not e) = do e' ::: bool ← infer e
                          where _ ::: t → error "non-bool expression found in not"
                       pure (not e' ::: bool)
    infer (eMul x op y) with inferPair x y
    ...   | inj₁ s = error s
    ...   | inj₂ ((x' , y') ::: t) with op
    ...     | times = ifNum   t >>= λ  p    → pure (eMul p x' y' ::: t)
    ...     | div   = ifNum   t >>= λ  p    → pure (eDiv p x' y' ::: t)
    ...     | mod   = int =?= t >>= λ {refl → pure (eMod   x' y' ::: t)}
    infer (eAdd x op y) = do (x' , y') ::: t ← inferPair x y
                             p ← ifNum t
                             pure (eAdd p op x' y' ::: t)

    infer (eRel x op y) with inferPair x y
    ... | inj₁ s = error s
    ... | inj₂ ((x' , y') ::: t) with op
    ...      | lTH = ifOrd t >>= λ p → pure (eOrd lTH p x' y' ::: bool)
    ...      | lE  = ifOrd t >>= λ p → pure (eOrd lE  p x' y' ::: bool)
    ...      | gTH = ifOrd t >>= λ p → pure (eOrd gTH p x' y' ::: bool)
    ...      | gE  = ifOrd t >>= λ p → pure (eOrd gE  p x' y' ::: bool)
    ...      | eQU = ifEq  t >>= λ p → pure (eEq  eQU p x' y' ::: bool)
    ...      | nE  = ifEq  t >>= λ p → pure (eEq  nE  p x' y' ::: bool)
    infer (eAnd x y) = do (x' , y') ::: bool ← inferPair x y
                              where _ ::: t → error "non-bool expression found in and"
                          pure (eAnd x' y' ::: bool)
    infer (eOr x y)  = do (x' , y') ::: bool ← inferPair x y
                              where _ ::: t → error "non-bool expression found in and"
                          pure (eOr  x' y' ::: bool)
    infer (eApp (ident "printString") (eString s ∷ [])) = pure (ePrintString s ::: void)
    infer (eApp x es) = do inList (ts , t) p ← lookupTCM x Σ
                           es' ::: ts' ← inferList es
                           refl ← eqLists ts ts'
                           pure (eApp x p es' ::: t)

    check : (t : Type) → (e : Expr) → TCM (Γ ⊢ e ∶ t)
    check t e = do e' ::: t' ← infer e
                   refl ← t =?= t'
                   pure e'



module Statements (Σ : SymbolTab) (T : Type) where

  open Expression Σ using (_⊢_∶_; toExp; liftCtx) renaming (check to checkExp; infer to inferExp)

  private
    variable
      s  : Stmt
      ss : List Stmt

  _,,_ : Block → Ctx → Ctx
  Δ ,, [] = Δ ∷ []
  Δ ,, (Δ' ∷ Γ) = (Δ ++r Δ') ∷ Γ


  ItemP : Type → Ctx → Item → Set
  ItemP _ [] _ = ⊥
  ItemP _ (Δ ∷ Γ) (noInit id) = id ∉ Δ
  ItemP t (Δ ∷ Γ) (init id e) = (id ∉ Δ) × ((Δ ∷ Γ) ⊢ e ∶ t)

  itemId : Item → Ident
  itemId (noInit x) = x
  itemId (init x e) = x
    

  newBlock : Type → List Item → Block
  newBlock t [] = []
  newBlock t (noInit id ∷ xs) = (id , t) ∷ newBlock t xs
  newBlock t (init id e ∷ xs) = (id , t) ∷ newBlock t xs

  -- 
  data DeclP (T : Type) : (Γ : Ctx) → Block → List Item → Set where
    []  : DeclP T Γ [] []
    _∷_ : ∀ {i is} → ItemP T (Δ ∷ Γ) i → DeclP T (((itemId i , T) ∷ Δ) ∷ Γ) Δ' is → DeclP T (Δ ∷ Γ) ((itemId i , T) ∷ Δ') (i ∷ is)

  data _⊢_⇒⇒_ (Γ : Ctx) : List Stmt → Block → Set
  data _⊢_⇒_ (Γ : Ctx) : Stmt → Block → Set where
    empty : Γ ⊢ empty ⇒ []
    bStmt : ([] ∷ Γ) ⊢ ss ⇒⇒ Δ → Γ ⊢ bStmt (block ss) ⇒ []
    decl : ∀ t {xs} → DeclP t Γ (newBlock t xs) xs → Γ ⊢ decl t xs ⇒ newBlock t xs
    ass  : ∀ {t} id → (id , t) ∈' Γ  →  Γ ⊢ e ∶ t    →  Γ ⊢ ass id e ⇒ []
    incr : ∀ id → (id , int) ∈' Γ  →  Γ ⊢ incr id ⇒ []
    decr : ∀ id → (id , int) ∈' Γ  →  Γ ⊢ decr id ⇒ []
    ret  : Γ ⊢ e ∶ T  →  Γ ⊢ ret e ⇒ []
    vRet : T ≡ void →  Γ ⊢ vRet ⇒ []
    cond : Γ ⊢ e ∶ bool → ([] ∷ Γ) ⊢ s ⇒ Δ → Γ ⊢ cond e s ⇒ []
    condElse : ∀ {t f} → Γ ⊢ e ∶ bool  →  ([] ∷ Γ) ⊢ t ⇒ Δ  →  ([] ∷ Γ) ⊢ f ⇒ Δ' →  Γ ⊢ condElse e t f ⇒ []
    while : Γ ⊢ e ∶ bool → ([] ∷ Γ) ⊢ s ⇒ Δ → Γ ⊢ while e s ⇒ []
    sExp : Γ ⊢ e ∶ void  →  Γ ⊢ sExp e ⇒ []
    
  data _⊢_⇒⇒_ Γ where
    []  : Γ ⊢ [] ⇒⇒ []
    _∷_ : ∀ {s ss} → Γ ⊢ s ⇒ Δ → (Δ ,, Γ) ⊢ ss ⇒⇒ Δ' → Γ ⊢ s ∷ ss ⇒⇒ (Δ ++r Δ')
  

  module _ where
    open TS.Valid T Σ
    open TS.Typed Σ

    toDecls : ∀ {is t} → DeclP t (Δ ∷ Γ) Δ' is → Stms ((Δ' ++r Δ) ∷ Γ) → Stms (Δ ∷ Γ)
    toDecls [] ss = ss
    toDecls (_∷_ {i = noInit x} px xs) ss        = SDecl _ x {!!} px SCons toDecls xs ss
    toDecls (_∷_ {i = init x e} (px , e') xs) ss = SDecl _ x {!!} px SCons toDecls xs ss


    toBlock : (Δ ∷ Γ) ⊢ s ⇒ Δ'  → Stms (Δ ∷ Γ)

    toStms : (Δ ∷ Γ) ⊢ ss ⇒⇒ Δ'  → Stms (Δ ∷ Γ)
    toStms [] = SEmpty
    toStms (s ∷ ss) with s
    ... | empty = toStms ss
    ... | (bStmt x) = SBlock (toStms x) SCons toStms ss
    ... | (decl t x) = toDecls x (toStms ss)
    ... | (ass id x x₁) = SAss id (toExp x₁) x SCons toStms ss
    ... | (incr id x) = SAss id (EArith TS.NumInt (EValue (Int.+ 1)) TS.+ (EId id x)) x SCons toStms ss
    ... | (decr id x) = SAss id (EArith TS.NumInt (EValue (Int.+ 1)) TS.- (EId id x)) x SCons toStms ss
    ... | (ret x)     = SReturn (Ret (toExp x)) SCons toStms ss
    ... | (vRet refl) = SReturn vRet            SCons toStms ss
    ... | (cond x s)       = SIfElse (toExp x) (toBlock s) SEmpty      SCons toStms ss
    ... | (condElse x t f) = SIfElse (toExp x) (toBlock t) (toBlock f) SCons toStms ss
    ... | (while x s) = SWhile (toExp x) (toBlock s) SCons toStms ss
    ... | (sExp x) = SExp (toExp x) SCons toStms ss

    toBlock empty = SEmpty
    toBlock (bStmt x) = SBlock (toStms x) SCons SEmpty
    toBlock (decl t x) = toDecls x SEmpty
    toBlock (ass id x x₁) = SAss id (toExp x₁) x SCons SEmpty
    toBlock (incr id x) = SAss id (EArith TS.NumInt (EValue (Int.+ 1)) TS.+ (EId id x)) x SCons SEmpty
    toBlock (decr id x) = SAss id (EArith TS.NumInt (EValue (Int.+ 1)) TS.- (EId id x)) x SCons SEmpty
    toBlock (ret x)     = SReturn (Ret (toExp x)) SCons SEmpty
    toBlock (vRet refl) = SReturn vRet            SCons SEmpty
    toBlock (cond x s)       = SIfElse (toExp x) (toBlock s) SEmpty      SCons SEmpty
    toBlock (condElse x t f) = SIfElse (toExp x) (toBlock t) (toBlock f) SCons SEmpty
    toBlock (while x s) = SWhile (toExp x) (toBlock s) SCons SEmpty
    toBlock (sExp x) = SExp (toExp x) SCons SEmpty

  

  check     : (Γ : Ctx) → (s  :      Stmt) → TCM (∃ (Γ ⊢ s ⇒_))

  checkStms : (Γ : Ctx) → (ss : List Stmt) → TCM (∃ (Γ ⊢ ss ⇒⇒_))
  checkStms Γ [] = pure ([] , [])
  checkStms Γ (s ∷ ss) = do Δ  , s'  ← check Γ s
                            Δ' , ss' ← checkStms (Δ ,, Γ) ss
                            pure (Δ ++r Δ' , s' ∷ ss')

  check Γ empty = pure ([] , empty)
  check Γ (bStmt (block ss)) = do _ , ss' ← checkStms ([] ∷ Γ) ss
                                  pure ([] , bStmt ss')
  check Γ (ass x e) = do inScope t p ← lookupCtx x Γ
                         e' ← checkExp Γ t e
                         pure ([] , ass x p e')
  check Γ (incr x) = do inScope t p ← lookupCtx x Γ
                        refl ← t =?= int
                        pure ([] , incr x p)
  check Γ (decr x) = do inScope t p ← lookupCtx x Γ
                        refl ← t =?= int
                        pure ([] , decr x p)
  check Γ (ret e) = do e' ← checkExp Γ T e
                       pure ([] , (ret e'))
  check Γ vRet = do refl ← T =?= void
                    pure ([] , vRet refl)
  check Γ (cond e t) = do e' ← checkExp Γ bool e
                          _ , t' ← check ([] ∷ Γ) t
                          pure ([] , cond e' t')
  check Γ (condElse e t f) = do e' ← checkExp Γ bool e
                                _ , t' ← check ([] ∷ Γ) t
                                _ , f' ← check ([] ∷ Γ) f
                                pure ([] , condElse e' t' f')
  check Γ (while e s) = do e' ← checkExp Γ bool e
                           _ , s' ← check ([] ∷ Γ) s
                           pure ([] , while e' s')
  check Γ (sExp e) = do e' ← checkExp Γ void e
                        pure ([] , sExp e')
  check Γ (decl t is) with Γ
  ... | []    = error "Can not declare variable in empty Ctx"
  ... | Δ ∷ Γ = do is' ← checkItems Δ Γ is
                   pure (newBlock t is , decl t is')
    where checkItems : ∀ Δ Γ → (is : List Item) → TCM (DeclP t (Δ ∷ Γ) (newBlock t is) is)
          checkItems Δ Γ [] = pure []
          checkItems Δ Γ (noInit id ∷ is) = do p ← id notIn Δ
                                               ps ← checkItems ((id , t) ∷ Δ) Γ is
                                               pure (p ∷ ps)
          checkItems Δ Γ (init id e ∷ is) = do p ← _,_ <$> id notIn Δ <*> checkExp (Δ ∷ Γ) t e
                                               ps ← checkItems ((id , t) ∷ Δ) Γ is
                                               pure (p ∷ ps)

