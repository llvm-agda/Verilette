{-# OPTIONS --allow-unsolved-metas #-} -- remove this later
module TypeChecker where

open import Agda.Builtin.Bool
open import Data.String
open import Agda.Primitive
open import Agda.Builtin.Equality


open import Relation.Nullary.Decidable
open import Relation.Nullary.Reflects

open import Effect.Monad.Error.Transformer
open import Effect.Monad

open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Sum.Effectful.Left String renaming (monad to monadSum)
open import Data.Sum.Base
open import Data.List hiding (lookup) renaming (_++_ to _+++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product hiding (_<*>_)

open import TypedSyntax renaming (Exp to TypedExp; Stm to TypedStm; Stms to TypedStms; Program to TypedProgram)
open import Javalette.AST hiding (String; Stmt) renaming (Expr to Exp; Ident to Id)
open import DeSugar

import TypedSyntax as T


cong : ∀  {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

TCM : Set → Set
TCM = (String ⊎_)

error : String → TCM A
error = inj₁


monadE : RawMonad (String ⊎_)
monadE = monadSum lzero

monadTCM : RawMonad TCM
monadTCM = monadSum lzero


open RawMonad {{...}}

instance
  monadTCM' : RawMonad TCM
  monadTCM' = monadTCM
  monadSum' : RawMonad (String ⊎_)
  monadSum' = monadE


builtin : SymbolTab
builtin = [] -- ((ident "readInt") × ([] × int)) ∷ []

typeCheck : (P : Prog) → TCM TypedProgram
typeCheck (program []) = error "Missing main function"
typeCheck (program ts) = {!!}


unType : {Γ : Ctx} {T : Type} → TypedExp Γ T → Exp
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
unType (EOrd x < y )    = eRel (unType x) lTH   (unType y)
unType (EOrd x <= y )   = eRel (unType x) lE    (unType y)
unType (EOrd x > y )    = eRel (unType x) gTH   (unType y)
unType (EOrd x >= y )   = eRel (unType x) gE    (unType y)
unType (EEq x == y)     = eRel (unType x) eQU   (unType y)
unType (EEq x != y)     = eRel (unType x) nE    (unType y)
unType (ELogic x && y)  = eAnd (unType x) (unType y)
unType (ELogic x || y)  = eOr  (unType x) (unType y)
unType (EAPP id xs p)   = eApp id (unTypeTList xs)
  where unTypeTList : TList (TypedExp Γ) ts → List Exp
        unTypeTList NIL       = []
        unTypeTList (x :+ xs) = unType x ∷ unTypeTList xs


mutual
  unValidStms : TypedStms T Γ → List Stm
  unValidStms SEmpty = []
  unValidStms (s SCons ss) = unValidStm s ∷ unValidStms ss


  unValidStm : TypedStm T Γ → Stm
  unValidStm (SExp x)          = sExp (unType x)
  unValidStm (SAss id e _)     = ass id (unType e)
  unValidStm (SWhile x s)      = while (unType x) (unValidStms s)
  unValidStm (SBlock s)        = block (unValidStms s)
  unValidStm (SIfElse e s1 s2) = ifElse (unType e) (unValidStms s1) (unValidStms s2)
  unValidStm (SReturn x)       = ret (unType x)
  unValidStm (SDecl t id x)    = decl t id
  unValidStm VReturn           = vRet


-- data ValidStms (s : List Stm) (T : Type) (Γ : Ctx) (Δ : Block) : Set where
--   valid : (Δ' : Block) → (vS : TypedStms T (Δ ∷ Γ) ((Δ' +++ Δ) ∷ Γ)) → unValidStms vS ≡ s → ValidStms s T Γ Δ
-- 
-- data ValidStm (s : Stm) (T : Type) (Γ : Ctx) (Δ : Block) : Set where
--   valid : (Δ' : Block) → (vS : TypedStm T (Δ ∷ Γ) ((Δ' +++ Δ) ∷ Γ)) → unValidStm vS ≡ s → ValidStm s T Γ Δ

data WellTyped (e : Exp) (Γ : Ctx) : Set where
  inferred : (T : Type) → (eT : TypedExp Γ T) → (unType eT) ≡ e →  WellTyped e Γ

pattern _:::_ e t = inferred t e refl

data InScope (Γ : Ctx) (x : Id) : Set where
  inScope : (t : Type) → (x , t) ∈' Γ → InScope Γ x

data InList {A : Set} (γ : List (Id × A)) (x : Id) : Set where
  inList : (t : A) → (x , t) ∈ γ → InList γ x


notidEq : (x y : Id) → Maybe  ( ¬ (x ≡ y))
notidEq (ident x) (ident y) with x ≟ y
... | .true  because ofʸ refl = nothing
... | .false because ofⁿ p   = nothing

lookup : (xs : List (Id × A)) → (x : Id) → Maybe (InList xs x)
lookup [] (ident x)   = nothing
lookup ((ident x' , a) ∷ xs) (ident x) with x' ≟ x
... | .true  because ofʸ refl = just (inList a zero)
... | .false because ofⁿ ¬p with lookup xs (ident x)
...         | just (inList t x₁) = just (inList t (suc x₁))
...         | nothing = nothing

lookupCtx : (Γ : Ctx) → (x : Id) → TCM (InScope Γ x)
lookupCtx [] (ident x)   = error ("Var " ++ x ++ " is not in scope")
lookupCtx (xs ∷ xss) x with lookup xs x
... | just (inList t x₁) = pure (inScope t (zero x₁))
... | nothing            = do inScope t p ← lookupCtx xss x
                              pure (inScope t (suc p))


ifEq : (T : Type) → TCM(Eq T)
ifEq bool       = pure EqBool
ifEq int        = pure EqInt
ifEq doub       = pure EqDouble
ifEq void       = error "Void is not Eq type"
ifEq (fun T ts) = error "Function is not Eq type"

ifOrd : (T : Type) → TCM(Ord T)
ifOrd bool   = error "Bool is not Ord type"
ifOrd int    = pure OrdInt
ifOrd doub   = pure OrdDouble
ifOrd void   = error "Void is not Ord type"
ifOrd (fun T ts) = error "Function is not Ord type"

ifNum : (T : Type) → TCM(Num T)
ifNum bool   = error "Bool is not nmeric"
ifNum int    = pure NumInt
ifNum doub   = pure NumDouble
ifNum void   = error "Void is not numeric"
ifNum (fun T ts) = error "Function is not Num type"


_=?=_ : (a b : Type) → TCM (a ≡ b)
bool       =?= bool       = pure refl
int        =?= int        = pure refl
doub       =?= doub       = pure refl
void       =?= void       = pure refl
(fun a as) =?= (fun b bs) = do refl ← a =?= b
                               refl ← eqLists as bs
                               pure refl
     where eqLists : (as : List Type) → (bs : List Type) → TCM (as ≡ bs)
           eqLists []       []       = pure refl
           eqLists (a ∷ as) (b ∷ bs) = do refl ← a =?= b
                                          refl ← eqLists as bs
                                          pure refl
           eqLists _ _               = error "Type mismatch in function"
a =?= b = error "Type mismatch"



-- Typeching of expressions uses a given context, Γ
module CheckExp (Γ : Ctx) where

  inferExp : (e : Exp) → TCM (WellTyped e Γ)
  inferExp (eLitFalse)  = pure (EValue false ::: bool)
  inferExp (eLitTrue)   = pure (EValue true ::: bool)
  inferExp (eLitInt x)  = pure (EValue x ::: int)
  inferExp (eLitDoub x) = pure (EValue x ::: doub)
  inferExp (eVar x) = do inScope t p ← lookupCtx Γ x
                         pure (EId x p ::: t)

  inferExp (eApp x es) = {!!}

  inferExp (eMul e1 op e2) = do e1' ::: t1 ← inferExp e1
                                e2' ::: t2 ← inferExp e2
                                refl ← t1 =?= t2
                                nump ← ifNum t1
                                let mulOp : (op : MulOp) → WellTyped (eMul e1 op e2) Γ
                                    mulOp = λ where
                                                times → EArith nump e1' (*) e2' ::: t1
                                                div   → EArith nump e1' (/) e2' ::: t1
                                                mod   → {!!}
                                pure (mulOp op)

  inferExp (eAdd e1 op e2) = do e1' ::: t1 ← inferExp e1
                                e2' ::: t2 ← inferExp e2
                                refl ← t1 =?= t2
                                nump ← ifNum t1
                                let addOp : (op : AddOp) → WellTyped (eAdd e1 op e2) Γ
                                    addOp = λ where plus  → EArith nump e1' (+) e2' ::: t1
                                                    minus → EArith nump e1' (-) e2' ::: t1
                                pure (addOp op)
  inferExp (eRel e c e₁) = {!!}
  inferExp (eAnd e e₁)   = {!!}
  inferExp (eOr e e₁)    = {!!}
  inferExp (eString x)   = error "Found string outside of call to printString"
  inferExp (neg e) = do e' ::: t ← inferExp e
                        p ← ifNum t
                        pure (ENeg p e' ::: t)
  inferExp (not e) = do e' ::: t ← inferExp e
                        refl ← t =?= bool
                        pure (ENot e'  ::: t)
  -- inferExp (eAss x e) = do inScope t p ← lookupCtx Γ x
  --                          e' ::: t' ← inferExp e
  --                          refl ← t =?= t'
  --                          pure (EAss x p e' ::: t)


  checkExp : (T : Type) → Exp → TCM (TypedExp Γ T)
  checkExp t x = do inferred t' e refl ← inferExp x
                    refl ← t =?= t'
                    pure e


  -- The ultimate proof
  checkExp-proof : {T : Type} (e : Exp) (eT : TypedExp Γ T) → checkExp T e ≡ inj₂ eT → unType eT ≡ e
  checkExp-proof e eT x = {!!}

_notIn_ : (x : Id) → (xs : Block) → TCM (x ∉ xs)
x notIn [] = pure zero
x notIn ((y , t) ∷ xs) with notidEq x y
... | nothing    = error "Variable already declared"
... | just p     = do p' ← x notIn xs
                      pure (suc p p')


open CheckExp
module CheckStm (sym : SymbolTab) (T : Type) where

  mutual
    checkStms : (Γ : Ctx) → (s : List Stm) → TCM (TypedStms T Γ)
    checkStms Γ []       = pure SEmpty
    checkStms Γ (s ∷ ss) = do s'  ← checkStm  Γ s
                              ss' ← checkStms (nextCtx s') ss
                              pure (s' SCons ss')

    checkStm : (Γ : Ctx) → (s : Stm) → TCM(TypedStm T Γ)
    checkStm Γ (sExp e)         = do e' ::: t ← inferExp Γ e
                                     pure (SExp e')
    checkStm Γ (ass x e)        = {!!}
    checkStm Γ (ret e)          = SReturn <$> checkExp Γ T e
    checkStm Γ (vRet)           = {!!}
    checkStm Γ (while e ss)     = SWhile  <$> checkExp Γ bool e <*> checkStms ([] ∷ Γ) ss
    checkStm Γ (block ss)       = SBlock  <$> checkStms ([] ∷ Γ) ss
    checkStm Γ (ifElse e s1 s2) = SIfElse <$> checkExp Γ bool e <*> checkStms ([] ∷ Γ) s1
                                                                <*> checkStms ([] ∷ Γ) s2 
    checkStm Γ (incDec x op)    = {!!}
    checkStm Γ (decl t x) with Γ
    ...                | []     = error "Empty context when declaring variables"
    ...                | Δ ∷ Γ  = SDecl t x <$> x notIn Δ

