{-# OPTIONS --allow-unsolved-metas #-}
module TypeChecker where


open import Agda.Builtin.Bool
open import Agda.Primitive
open import Agda.Builtin.Int -- using (Int ; pos)
open import Agda.Builtin.Float renaming (Float to Double)
open import Agda.Builtin.Equality

open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Reflects
open import Relation.Nullary.Negation.Core using (¬_)

open import Effect.Monad.Error.Transformer
open import Effect.Monad

open import Data.String using (String; _≟_; _++_ )
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Sum.Effectful.Left String lzero renaming (monad to monadSum)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.List using (List; _∷_ ; []; map; zip; unzipWith) renaming (_++_ to _+++_)
open import Data.Product using (_×_; _,_)

open import TypedSyntax renaming (Program to TypedProgram)
open import Javalette.AST hiding (String; Stmt) renaming (Expr to Exp; Ident to Id)
open import DeSugar


-- | Type checker monad
TCM : Set → Set
TCM = String ⊎_

open RawMonad {{...}} hiding (zip)
instance
  monadTCM : RawMonad TCM
  monadTCM = monadSum

error : String → TCM A
error = inj₁


builtin : SymbolTab
builtin = (ident "printInt"    , (int  ∷ [] , void))
        ∷ (ident "printString" , (void ∷ [] , void)) -- HACK for string
        ∷ (ident "printDouble" , (doub ∷ [] , void))
        ∷ (ident "readInt"     , (       [] , int ))
        ∷ (ident "readDouble"  , (       [] , doub)) ∷ []


getSymEntry : TopDef → (Id × FunType)
getSymEntry (fnDef t x as b) = x , map fromArg as , t
  where fromArg : Arg → Type
        fromArg (argument t x) = t


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

_notIn_ : (x : Id) → (xs : List (Id × A)) → TCM (x ∉ xs)
x notIn [] = pure zero
x notIn ((y , t) ∷ xs) with x eqId y
... | inj₂ _     = error "Variable already declared"
... | inj₁ p     = do p' ← x notIn xs
                      pure (suc p p')

checkUnique : (xs : List (Id × A)) → TCM (Unique xs)
checkUnique []              = pure unique[]
checkUnique ((id , x) ∷ xs) = uniqueSuc <$> id notIn xs <*> checkUnique xs

lookup : (x : Id) → (xs : List (Id × A)) → Maybe (InList xs x)
lookup id [] = nothing
lookup id ((x' , a) ∷ xs) with x' eqId id
... | inj₂ refl  = just (inList a zero)
... | inj₁ _ with lookup id xs
...         | just (inList t x₁) = just (inList t (suc x₁))
...         | nothing            = nothing

lookupTCM : (x : Id) → (xs : List (Id × A)) → TCM (InList xs x)
lookupTCM x xs with lookup x xs
... | just p = pure p
... | nothing = error ("lookup failed: " ++ showId x ++ " was not found")


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
unType (EOrd _ x < y )  = eRel (unType x) lTH   (unType y)
unType (EOrd _ x <= y ) = eRel (unType x) lE    (unType y)
unType (EOrd _ x > y )  = eRel (unType x) gTH   (unType y)
unType (EOrd _ x >= y ) = eRel (unType x) gE    (unType y)
unType (EEq _ x == y)   = eRel (unType x) eQU   (unType y)
unType (EEq _ x != y)   = eRel (unType x) nE    (unType y)
unType (ELogic x && y)  = eAnd (unType x) (unType y)
unType (ELogic x || y)  = eOr  (unType x) (unType y)
unType (EAPP id xs p)   = eApp id (unTypeTList xs)
unType (EStr s)         = eString s


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
unValidStm (SDecl t id x _)  = decl t id
unValidStm VReturn           = vRet


data WellTyped (e : Exp) (Σ : SymbolTab) (Γ : Ctx) : Set where
  inferred : (T : Type) → (eT : TypedExp Σ Γ T) → (unType eT) ≡ e →  WellTyped e Σ Γ

data WellTypedList (es : List Exp) (Σ : SymbolTab) (Γ : Ctx) : Set where
  inferred : (Ts : List Type) → (eTs : TList (TypedExp Σ Γ) Ts) → unTypeTList eTs ≡ es →  WellTypedList es Σ Γ

pattern _:::_ e t = inferred t e refl

data WellTypedPair (e1 e2 : Exp) (Σ : SymbolTab) (Γ : Ctx) : Set where
  inferredP : (T : Type) → (eT1 eT2 : TypedExp Σ Γ T) → (unType eT1) ≡ e1
                                                      → (unType eT2) ≡ e2 → WellTypedPair e1 e2 Σ Γ

pattern infP e1 e2 t = inferredP t e1 e2 refl refl


data InScope (Γ : Ctx) (x : Id) : Set where
  inScope : (t : Type) → (x , t) ∈' Γ → InScope Γ x

lookupCtx : (x : Id) → (Γ : Ctx) → TCM (InScope Γ x)
lookupCtx x []   = error ("Var " ++ showId x ++ " is not in scope")
lookupCtx x (xs ∷ xss) with lookup x xs
... | just (inList t x₁) = pure (inScope t (zero x₁))
... | nothing            = do inScope t p ← lookupCtx x xss
                              pure (inScope t (suc p))


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


eqLists : (as : List Type) → (bs : List Type) → TCM (as ≡ bs)
_=?=_ : (a b : Type) → TCM (a ≡ b)
bool       =?= bool       = pure refl
int        =?= int        = pure refl
doub       =?= doub       = pure refl
void       =?= void       = pure refl
(fun a as) =?= (fun b bs) = do refl ← a =?= b
                               refl ← eqLists as bs
                               pure refl
a =?= b = error "Type mismatch"

eqLists []       []       = pure refl
eqLists (a ∷ as) (b ∷ bs) = do refl ← a =?= b
                               refl ← eqLists as bs
                               pure refl
eqLists _ _               = error "Type mismatch in function"

_=T=_ : (a b : Type) → (a ≡ b ⊎ a ≢ b) -- ⊎
int =T= int  = inj₁ refl
int =T= doub = inj₂ (λ ())
int =T= bool = inj₂ (λ ())
int =T= void = inj₂ (λ ())
int =T= fun b ts = inj₂ (λ ())
doub =T= int = inj₂ (λ ())
doub =T= doub = inj₁ refl
doub =T= bool = inj₂ (λ ())
doub =T= void = inj₂ (λ ())
doub =T= fun b ts = inj₂ (λ ())
bool =T= int = inj₂ (λ ())
bool =T= doub = inj₂ (λ ())
bool =T= bool = inj₁ refl
bool =T= void = inj₂ (λ ())
bool =T= fun b ts = inj₂ (λ ())
void =T= int = inj₂ (λ ())
void =T= doub = inj₂ (λ ())
void =T= bool = inj₂ (λ ())
void =T= void = inj₁ refl
void =T= fun b ts = inj₂ (λ ())
fun a ts =T= int = inj₂ (λ ())
fun a ts =T= doub = inj₂ (λ ())
fun a ts =T= bool = inj₂ (λ ())
fun a ts =T= void = inj₂ (λ ())
fun a ts =T= fun b ts₁ = {!!}



-- Typeching of expressions uses a given context, Γ
module CheckExp (Σ : SymbolTab) (Γ : Ctx) where

  inferExp  : (e  :      Exp) → TCM (WellTyped     e  Σ Γ)
  inferList : (es : List Exp) → TCM (WellTypedList es Σ Γ)
  inferList [] = pure (inferred [] NIL refl)
  inferList (e ∷ es) = do e'  ::: t  ← inferExp e
                          es' ::: ts ← inferList es
                          pure ((e' :+ es') ::: (t ∷ ts))

  inferPair : (e1 e2 : Exp) → TCM (WellTypedPair e1 e2 Σ Γ)
  inferPair e1 e2 = do e1' ::: t1 ← inferExp e1
                       e2' ::: t2 ← inferExp e2
                       refl ← t1 =?= t2
                       pure (inferredP t1 e1' e2' refl refl)


  inferExp (eLitFalse)  = pure (EValue false ::: bool)
  inferExp (eLitTrue)   = pure (EValue true  ::: bool)
  inferExp (eLitInt x)  = pure (EValue x     ::: int)
  inferExp (eLitDoub x) = pure (EValue x     ::: doub)
  inferExp (eVar x) = do inScope t p ← lookupCtx x Γ
                         pure (EId x p ::: t)

  inferExp (eApp (ident "printString") (eString s ∷ [])) with lookup (ident "printString") Σ
  ... | just (inList (void ∷ [] , void)  p) = pure (EAPP (ident "printString") ( EStr s :+ NIL) p ::: void)
  ... | _                                   = error "Mismatch in printString"
  inferExp (eApp x es) with lookup x Σ
  ... | nothing                  = error "Function not defined"
  ... | just (inList (ts , t) p) = do es' ::: ts' ← inferList es
                                      refl ← eqLists ts ts'
                                      pure (EAPP x es' p ::: t)

  inferExp (eMul e1 op e2) with inferPair e1 e2
  ... | inj₁ s = error s
  ... | inj₂ (infP e1' e2' t) with op
  ...      | times = ifNum   t >>= λ  p    → pure (EArith p e1' (*) e2' ::: t)
  ...      | div   = ifNum   t >>= λ  p    → pure (EArith p e1' (/) e2' ::: t)
  ...      | mod   = int =?= t >>= λ {refl → pure (EMod     e1'     e2' ::: t)}

  inferExp (eAdd e1 op e2) with inferPair e1 e2
  ... | inj₁ s = error s
  ... | inj₂ (infP e1' e2' t) with op
  ...      | plus  = ifNum t >>= λ p → pure (EArith p e1' (+) e2' ::: t)
  ...      | minus = ifNum t >>= λ p → pure (EArith p e1' (-) e2' ::: t)

  inferExp (eRel e1 op e2) with inferPair e1 e2
  ... | inj₁ s = error s
  ... | inj₂ (infP e1' e2' t) with op
  ...      | lTH = ifOrd t >>= λ p → pure (EOrd p e1' (<)  e2' ::: bool)
  ...      | lE  = ifOrd t >>= λ p → pure (EOrd p e1' (<=) e2' ::: bool)
  ...      | gTH = ifOrd t >>= λ p → pure (EOrd p e1' (>)  e2' ::: bool)
  ...      | gE  = ifOrd t >>= λ p → pure (EOrd p e1' (>=) e2' ::: bool)
  ...      | eQU = ifEq  t >>= λ p → pure (EEq  p e1' (==) e2' ::: bool)
  ...      | nE  = ifEq  t >>= λ p → pure (EEq  p e1' (!=) e2' ::: bool)

  inferExp (eAnd e1 e2)   = do infP e1' e2' bool ← inferPair e1 e2
                                    where _ → error "And applied to nonBool args"
                               pure (ELogic e1' && e2' ::: bool)
  inferExp (eOr e1 e2)    = do infP e1' e2' bool ← inferPair e1 e2
                                    where _ → error "Or applied to nonBool args"
                               pure (ELogic e1' || e2' ::: bool)

  inferExp (eString x)   = error "Found string outside of call to printString"
  inferExp (neg e) = do e' ::: t ← inferExp e
                        p ← ifNum t
                        pure (ENeg p e' ::: t)
  inferExp (not e) = do e' ::: t ← inferExp e
                        refl ← t =?= bool
                        pure (ENot e'  ::: t)


  checkExp : (T : Type) → Exp → TCM (TypedExp Σ Γ T)
  checkExp t x = do e ::: t' ← inferExp x
                    refl ← t =?= t'
                    pure e


-- Validating statments using a given SymbolTab and Return Type
module CheckStm (Σ : SymbolTab) (T : Type) where
  open CheckExp Σ

  checkStm  : (Γ : Ctx) → (s : Stm)      → TCM (TypedStm  Σ T Γ)
  checkStms : (Γ : Ctx) → (s : List Stm) → TCM (TypedStms Σ T Γ)

  checkStms Γ []       = pure SEmpty
  checkStms Γ (s ∷ ss) = do s'  ← checkStm  Γ s
                            ss' ← checkStms (nextCtx (Σ) s') ss
                            pure (s' SCons ss')


  checkStm Γ (sExp e)         = SExp <$> checkExp Γ void e
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
  ...           | []     = error "Empty context when declaring variables"
  ...           | Δ ∷ Γ with t
  ... | int  = SDecl int  x (pos 0) <$> x notIn Δ
  ... | doub = SDecl doub x 0.0     <$> x notIn Δ
  ... | bool = SDecl bool x false   <$> x notIn Δ
  ... | void = error "Cannot decl void"
  ... | fun y ts = error "Cannot decl fun type"


checkReturn  : (ss : TypedStms Σ T Γ) → TCM   (returnStms Σ ss)
checkReturn' : (s  : TypedStm  Σ T Γ) → Maybe (returnStm  Σ s)
checkReturn SEmpty = error "Function does not return"
checkReturn (s SCons ss) with checkReturn' s
... | just x  = pure (SHead x)
... | nothing = SCon <$> checkReturn ss

checkReturn' (SBlock ss) with checkReturn ss
... | inj₂ x  = just (SBlock x)
... | inj₁ _  = nothing
checkReturn' (SIfElse x s1 s2) with checkReturn s1 , checkReturn s2
... | inj₂ x₁ , inj₂ x₂ = just (SIFElse x₁ x₂)
... | _                 = nothing
checkReturn' (SReturn x) = just SReturn
checkReturn' (VReturn)   = just VReturn
checkReturn' (SExp x)         = nothing
checkReturn' (SDecl t id x _) = nothing
checkReturn' (SAss id e x)    = nothing
checkReturn' (SWhile x x₁)    = nothing

checkParam : (t : Type) → (ts : List Type) → TCM(t ∉t ts)
checkParam t []       = pure zero
checkParam t (x ∷ ts) with t =T= x
... | inj₁ x₁  = error "void in parameters"
... | inj₂ y   = do p ← checkParam t ts
                    pure (suc y p)
checkFun : (Σ : SymbolTab) (t : Type) (ts : List Type) → TopDef → TCM (Def Σ ts t)
checkFun Σ t ts (fnDef t' x as (block b)) = do
    refl ← t =?= t'
    let (ids , ts') = unzipWith (λ {(argument t id) → id , t}) as
    eqLists ts ts'
    let params = zip ids ts
    unique  ← checkUnique params
    ss'     ← addReturnVoid t <$> CheckStm.checkStms Σ t (params ∷ []) (deSugarList b)
    returns ← checkReturn ss'
    pparam  ← checkParam void ts
    pure (record { idents    = ids
                 ; body      = ss'
                 ; voidparam = pparam
                 ; unique    = unique
                 ; return    = returns })
  where addReturnVoid : (T : Type) → TypedStms Σ T Γ → TypedStms Σ T Γ
        addReturnVoid void SEmpty = VReturn SCons SEmpty
        addReturnVoid void (VReturn SCons x) = VReturn SCons x
        addReturnVoid void (s SCons x) = s SCons (addReturnVoid void x)
        addReturnVoid _    x = x


checkFuns : (Σ' Σ  : SymbolTab) → (def : List TopDef) → TCM (TList (λ (_ , (ts , t)) → Def Σ' ts t) Σ)
checkFuns Σ' [] [] = pure NIL
checkFuns Σ' [] (x ∷ def) = error "More functions than in SyTab"
checkFuns Σ' (x ∷ Σ) []   = error "More entries in symtab than defs"
checkFuns Σ' ((id , (ts , t)) ∷ Σ) (def ∷ defs) = do def'  ← checkFun  Σ' t ts def
                                                     defs' ← checkFuns Σ' Σ    defs
                                                     pure (def' :+ defs')

typeCheck : (builtin : SymbolTab) (P : Prog) → TCM TypedProgram
typeCheck b (program defs) = do
    let Σ = map getSymEntry defs
    inList ([] , int) p ← lookupTCM (ident "main") (b +++ Σ)
        where _ → error "Found main but with wrong type"
    unique ← checkUnique (b +++ Σ)
    defs' ← checkFuns (b +++ Σ) Σ defs
    pure (record { BuiltIn = b
                 ; Defs    = Σ
                 ; hasMain    = p
                 ; hasDefs    = defs'
                 ; uniqueDefs = unique })
