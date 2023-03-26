module TypeChecker where

open import Agda.Builtin.Bool
open import Data.String
open import Agda.Primitive
open import Agda.Builtin.Int   -- using (Int) 
open import Agda.Builtin.Equality

open import Relation.Nullary.Decidable
open import Relation.Nullary.Reflects
open import Relation.Nullary.Negation.Core using (¬_)

open import Effect.Monad.Error.Transformer
open import Effect.Monad

open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Sum.Effectful.Left String lzero renaming (monad to monadSum)
open import Data.Sum 

open import Data.List hiding (lookup) renaming (_++_ to _+++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product hiding (_<*>_)

open import Javalette.AST hiding (String; Stmt) renaming (Expr to Exp; Ident to Id)
open import TypedSyntax renaming (Exp to TypedExp; Stm to TypedStm; Stms to TypedStms)
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


unValidStm  : TypedStm  T Γ → Stm
unValidStms : TypedStms T Γ → List Stm
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


data WellTyped (e : Exp) (Γ : Ctx) : Set where
  inferred : (T : Type) → (eT : TypedExp Γ T) → (unType eT) ≡ e →  WellTyped e Γ

pattern _:::_ e t = inferred t e refl


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
module _ (Γ : Ctx) where

  inferExp : (e : Exp) → TCM (WellTyped e Γ)
  inferExp (eLitFalse)  = pure (EValue false ::: bool)
  inferExp (eLitTrue)   = pure (EValue true ::: bool)
  inferExp (eLitInt x)  = pure (EValue x ::: int)
  inferExp (eLitDoub x) = pure (EValue x ::: doub)
  inferExp (eVar x) = do inScope t p ← lookupCtx x Γ 
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


  checkExp : (T : Type) → Exp → TCM (TypedExp Γ T)
  checkExp t x = do e ::: t' ← inferExp x
                    refl ← t =?= t'
                    pure e


  -- The ultimate proof
  checkExp-proof : {T : Type} (e : Exp) (eT : TypedExp Γ T) → checkExp T e ≡ inj₂ eT → unType eT ≡ e
  checkExp-proof e eT x = {!!}



-- Validating statments using a given SymbolTab and Return Type
module _ (sym : SymbolTab) (T : Type) where

  checkStm  : (Γ : Ctx) → (s : Stm)      → TCM (TypedStm  T Γ)
  checkStms : (Γ : Ctx) → (s : List Stm) → TCM (TypedStms T Γ)

  checkStms Γ []       = pure SEmpty
  checkStms Γ (s ∷ ss) = do s'  ← checkStm  Γ s
                            ss' ← checkStms (nextCtx s') ss
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

