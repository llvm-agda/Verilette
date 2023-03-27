{-# OPTIONS --allow-unsolved-metas #-} -- remove this later

module TypeChecker where

open import Agda.Builtin.Bool
open import Data.String
--open import Agda.Builtin.String
open import Agda.Primitive
open import Agda.Builtin.Int   -- using (Int) 
open import Agda.Builtin.Equality

open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Reflects
open import Relation.Nullary.Negation.Core using (¬_)

open import Effect.Monad.Error.Transformer
open import Effect.Monad

open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Sum.Effectful.Left String lzero renaming (monad to monadSum)
open import Data.Sum.Base hiding (map)
open import Data.List hiding (lookup) renaming (_++_ to _+++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_) 

open import TypedSyntax renaming (Program to TypedProgram)
open import Javalette.AST hiding (String; Stmt) renaming (Expr to Exp; Ident to Id)
open import DeSugar


-- | Type checker monad
TCM : Set → Set
TCM = String ⊎_

open RawMonad {{...}}
instance
  monadTCM' : RawMonad TCM
  monadTCM' = monadSum 

error : String → TCM A
error = inj₁


builtin : SymbolTab
builtin = (((ident "printInt") , ([] , int))) ∷ (((ident "printString") , ([] , int))) ∷ []


symDef : TopDef → (Id × FunType)
symDef (fnDef t x as b) = x , map fromArg as , t
  where fromArg : Arg → Type
        fromArg (argument t x) = t

typeCheck : (P : Prog) → TCM TypedProgram
typeCheck (program []) = error "Missing main function"
typeCheck (program ts) = do pure (record
                                    { BuiltIn = builtin ; Defs = map symDef ts ; main = {!lookup!} ; LDefs = {!!} ; unique = {!!} })


open Typed renaming (Exp to TypedExp; Stm to TypedStm; Stms to TypedStms)


unType      :        TypedExp Σ Γ  T  → Exp
unTypeTList : TList (TypedExp Σ Γ) ts → List Exp
unTypeTList NIL       = []
unTypeTList (x :+ xs) = unType x ∷ unTypeTList xs

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


unValidStm  : TypedStm  Σ T Γ → Stm
unValidStms : TypedStms Σ T Γ → List Stm
unValidStms SEmpty       = []
unValidStms (s SCons ss) = unValidStm s ∷ unValidStms ss

unValidStm (SExp x)          = sExp (unType x)
unValidStm (SAss id e _)     = ass id (unType e)
unValidStm (SWhile x s)      = while (unType x) (unValidStms s)
unValidStm (SBlock s)        = block (unValidStms s)
unValidStm (SIfElse e s1 s2) = ifElse (unType e) (unValidStms s1) (unValidStms s2)
unValidStm (SReturn x)       = ret (unType x)
unValidStm (SDecl t id x)    = decl t id
unValidStm VReturn           = vRet


data WellTyped (e : Exp) (Σ : SymbolTab) (Γ : Ctx) : Set where
  inferred : (T : Type) → (eT : TypedExp Σ Γ T) → (unType eT) ≡ e →  WellTyped e Σ Γ

pattern _:::_ e t = inferred t e refl

getType : ∀ {e} → WellTyped e Σ Γ → Type
getType (inferred T eT x) = T

getTyped : ∀ {e} → (vt : WellTyped e Σ Γ) → TypedExp Σ Γ (getType vt)
getTyped (inferred T eT x) = eT

getProof : (e : Exp) → {vt : WellTyped e Σ Γ} → unType (getTyped vt) ≡ e
getProof e {inferred T eT x} = x

toWellTyped : (eT : TypedExp Σ Γ T) → WellTyped (unType eT) Σ Γ
toWellTyped {T = T} eT = inferred T eT refl

data InScope (Γ : Ctx) (x : Id) : Set where
  inScope : (t : Type) → (x , t) ∈' Γ → InScope Γ x

data InList {A : Set} (γ : List (Id × A)) (x : Id) : Set where
  inList : (t : A) → (x , t) ∈ γ → InList γ x


showId : Id → String
showId (ident s) = s

_eqId_  : (x y : Id) → (x ≢ y) ⊎ (x ≡ y)
_eqId_  (ident x) (ident y) with x ≟ y
... | .true  because ofʸ refl = inj₂ refl
... | .false because ofⁿ p    = inj₁ (help p)
  where help : {x y : String} → ¬ (x ≡ y) → ¬ (ident x ≡ ident y)
        help p₁ refl = p₁ refl

lookup : (x : Id) → (xs : List (Id × A)) → Maybe (InList xs x)
lookup id [] = nothing
lookup id ((x' , a) ∷ xs) with x' eqId id
... | inj₂ refl  = just (inList a zero)
... | inj₁ _ with lookup id xs
...         | just (inList t x₁) = just (inList t (suc x₁))
...         | nothing            = nothing

lookupCtx : (x : Id) → (Γ : Ctx) → TCM (InScope Γ x)
lookupCtx x []   = error ("Var " ++ showId x ++ " is not in scope")
lookupCtx x (xs ∷ xss) with lookup x xs
... | just (inList t x₁) = pure (inScope t (zero x₁))
... | nothing            = do inScope t p ← lookupCtx x xss 
                              pure (inScope t (suc p))

_notIn_ : (x : Id) → (xs : Block) → TCM (x ∉ xs)
x notIn [] = pure zero
x notIn ((y , t) ∷ xs) with x eqId y
... | inj₂ _     = error "Variable already declared"
... | inj₁ p     = do p' ← x notIn xs
                      pure (suc p p')


ifEq : (T : Type) → TCM (Eq T)
ifEq bool       = pure EqBool
ifEq int        = pure EqInt
ifEq doub       = pure EqDouble
ifEq void       = error "Void is not Eq type"
ifEq (fun T ts) = error "Function is not Eq type"

ifOrd : (T : Type) → TCM (Ord T)
ifOrd bool   = error "Bool is not Ord type"
ifOrd int    = pure OrdInt
ifOrd doub   = pure OrdDouble
ifOrd void   = error "Void is not Ord type"
ifOrd (fun T ts) = error "Function is not Ord type"

ifNum : (T : Type) → TCM (Num T)
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
module CheckExp (Σ : SymbolTab) (Γ : Ctx) where

  checkExp  : (T :       Type) →      Exp → TCM (       TypedExp Σ Γ  T)
  checkList : (ts : List Type) → List Exp → TCM (TList (TypedExp Σ Γ) ts)

  inferExp : (e : Exp) → TCM (WellTyped e Σ Γ)
  inferExp (eLitFalse)  = pure (EValue false ::: bool)
  inferExp (eLitTrue)   = pure (EValue true ::: bool)
  inferExp (eLitInt x)  = pure (EValue x ::: int)
  inferExp (eLitDoub x) = pure (EValue x ::: doub)
  inferExp (eVar x) = do inScope t p ← lookupCtx x Γ 
                         pure (EId x p ::: t)

  inferExp (eApp x es) with lookup x Σ 
  ... | just (inList (ts , t) p) = do es' ← checkList ts es
                                      pure (inferred t (EAPP x es' p) {!!})
  ... | nothing = error "Function not defined"

  inferExp (eMul e1 op e2) = do e1' ::: t1 ← inferExp e1
                                e2' ::: t2 ← inferExp e2
                                refl ← t1 =?= t2
                                nump ← ifNum t1
                                let mulOp : (op : MulOp) → WellTyped (eMul e1 op e2) Σ Γ
                                    mulOp = λ where
                                                times → EArith nump e1' (*) e2' ::: t1
                                                div   → EArith nump e1' (/) e2' ::: t1
                                                mod   → {!!}
                                pure (mulOp op)

  inferExp (eAdd e1 op e2) = do e1' ::: t1 ← inferExp e1
                                e2' ::: t2 ← inferExp e2
                                refl ← t1 =?= t2
                                nump ← ifNum t1
                                let addOp : (op : AddOp) → WellTyped (eAdd e1 op e2) Σ Γ
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


  checkExp t x = do e ::: t' ← inferExp x
                    refl ← t =?= t'
                    pure e

  checkList []       []       = pure NIL
  checkList (t ∷ ts) (x ∷ xs) = _:+_ <$> checkExp t x <*> checkList ts xs
  checkList _ _  = error "The number of arguments did not match the function type"

  data IfJust {A : Set} : TCM A → Set where
    IsJust : (a : A) → IfJust (inj₂ a)

  fromJust : {tcm : TCM A} → IfJust (tcm) → A
  fromJust (IsJust a) = a

  -- The ultimate proof
  checkExp-proof : {T : Type} → (e : Exp) → (eT : (IfJust (checkExp T e))) → unType (fromJust eT) ≡ e
  checkExp-proof (eVar x) eT = {!!}
  checkExp-proof {int} (eLitInt x) (IsJust .(EValue x)) = refl
  checkExp-proof {doub} (eLitDoub x) (IsJust .(EValue x)) = refl
  checkExp-proof {bool} eLitTrue (IsJust .(EValue true)) = refl
  checkExp-proof {bool} eLitFalse (IsJust .(EValue false)) = refl
  checkExp-proof (eApp x es) eT = {!!}
  checkExp-proof {T} (neg e) eT = {!!}
  checkExp-proof (not e) eT = {!!}
  checkExp-proof (eMul e m e₁) eT = {!!}
  checkExp-proof (eAdd e a e₁) eT = {!!}
  checkExp-proof (eRel e r e₁) eT = {!!}
  checkExp-proof (eAnd e e₁) eT = {!!}
  checkExp-proof (eOr e e₁) eT = {!!}



-- Validating statments using a given SymbolTab and Return Type
module CheckStm (Σ : SymbolTab) (T : Type) where
  open CheckExp Σ

  checkStm  : (Γ : Ctx) → (s : Stm)      → TCM (TypedStm  Σ T Γ)
  checkStms : (Γ : Ctx) → (s : List Stm) → TCM (TypedStms Σ T Γ)

  checkStms Γ []       = pure SEmpty
  checkStms Γ (s ∷ ss) = do s'  ← checkStm  Γ s
                            ss' ← checkStms (nextCtx (Σ) s') ss
                            pure (s' SCons ss')


  checkStm Γ (sExp e)         = do e' ::: t ← inferExp Γ e
                                   pure (SExp e')
  checkStm Γ (ass id e)       = do inScope t p ← lookupCtx id Γ 
                                   e' ← checkExp Γ t e
                                   pure (SAss id e' p)
  checkStm Γ (ret e)          = SReturn <$> checkExp Γ T e
  checkStm Γ (vRet)           = do refl ← T =?= void
                                   pure VReturn
  checkStm Γ (while e ss)     = SWhile  <$> checkExp Γ bool e <*> checkStms ([] ∷ Γ) ss
  checkStm Γ (block ss)       = SBlock  <$> checkStms ([] ∷ Γ) ss
  checkStm Γ (ifElse e s1 s2) = SIfElse <$> checkExp Γ bool e <*> checkStms ([] ∷ Γ) s1
                                                              <*> checkStms ([] ∷ Γ) s2 
  checkStm Γ (incDec id op)   = do inScope t p ← lookupCtx id Γ 
                                   refl ← t =?= int
                                   let e : incDecOp → ArithOp
                                       e = λ where inc → +
                                                   dec → -
                                   pure (SAss id (EArith NumInt (EId id p) (e op) (EValue (pos 1))) p)
  checkStm Γ (decl t x) with Γ
  ...                | []     = error "Empty context when declaring variables"
  ...                | Δ ∷ Γ  = SDecl t x <$> x notIn Δ

