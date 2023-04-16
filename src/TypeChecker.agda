module TypeChecker where


open import Agda.Builtin.Bool
open import Agda.Primitive
open import Agda.Builtin.Int -- using (Int ; pos)
open import Agda.Builtin.Float renaming (Float to Double)
open import Agda.Builtin.Equality

open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Effect.Monad

open import Data.String using (String; _≟_; _++_ )
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Sum.Effectful.Left renaming (monad to monadSum)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.List using (List; _∷_ ; []; map; zip; unzipWith) renaming (_++_ to _+++_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Function using (case_of_)

open import TypedSyntax renaming (Program to TypedProgram)
open import Javalette.AST hiding (String; Stmt) renaming (Expr to Exp; Ident to Id)
open import DeSugar
open import TypeCheckerMonad
open import Util


checkAll : {P : A → Set} → ((a : A) → TCM (P a)) → (as : List A) → TCM (All P as)
checkAll P []       = pure []
checkAll P (x ∷ xs) = _∷_ <$> P x <*> checkAll P xs


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


_notIn_ : (x : Id) → (xs : List (Id × A)) → TCM (x ∉ xs)
id notIn xs = checkAll (λ (id' , _) → notEq id id') xs
  where notEq : (x y : Id) → TCM (x ≢ y)
        notEq id id' with id eqId id'
        ... | inj₁ x = pure x
        ... | inj₂ y = error (showId id ++ " was already in scope when delcaring new var")


checkUnique : (xs : List (Id × A)) → TCM (Unique xs)
checkUnique []              = pure unique[]
checkUnique ((id , x) ∷ xs) = uniqueSuc <$> id notIn xs <*> checkUnique xs


open Valid renaming (Stm to TypedStm; Stms to TypedStms)

-- Validating statments using a given SymbolTab and Return Type
module CheckStm (Σ : SymbolTab) (T : Type) where
  open Typed Σ using (EArith; EId; EValue)
  open import CheckExp Σ

  checkStm  : (Γ : Ctx) → (s : Stm)      → TCM (TypedStm  T Σ Γ)
  checkStms : (Γ : Ctx) → (s : List Stm) → TCM (TypedStms T Σ Γ)

  checkStms Γ []       = pure SEmpty
  checkStms Γ (s ∷ ss) = do s'  ← checkStm  Γ s
                            ss' ← checkStms (nextCtx T Σ s') ss
                            pure (s' SCons ss')


  checkStm Γ (sExp e)         = SExp <$> checkExp Γ void e
  checkStm Γ (ass id e)       = do inScope t p ← lookupCtx id Γ
                                   e' ← checkExp Γ t e
                                   pure (SAss id e' p)
  checkStm Γ (ret e)          = SReturn <$> (Ret <$> checkExp Γ T e)
  checkStm Γ (vRet)           = do refl ← T =?= void
                                   pure (SReturn vRet)
  checkStm Γ (while e ss)     = SWhile  <$> checkExp Γ bool e <*> checkStms ([] ∷ Γ) ss
  checkStm Γ (block ss)       = SBlock  <$> checkStms ([] ∷ Γ) ss
  checkStm Γ (ifElse e s1 s2) = SIfElse <$> checkExp Γ bool e <*> checkStms ([] ∷ Γ) s1
                                                              <*> checkStms ([] ∷ Γ) s2
  checkStm Γ (incDec id op)   = do inScope t p ← lookupCtx id Γ
                                   refl ← t =?= int
                                   let op' = case op of λ {inc → + ; dec → (-)}
                                   pure (SAss id (EArith NumInt (EId id p) op' (EValue (pos 1))) p)
  checkStm Γ (decl t x) with Γ
  ...           | []     = error "Empty context when declaring variables"
  ...           | Δ ∷ Γ with t
  ... | int  = SDecl int  x (pos 0) <$> x notIn Δ
  ... | doub = SDecl doub x 0.0     <$> x notIn Δ
  ... | bool = SDecl bool x false   <$> x notIn Δ
  ... | void = error "Cannot decl void"
  ... | fun y ts = error "Cannot decl fun type"


checkReturn  : (ss : TypedStms T Σ Γ) → TCM (returnStms ss)
checkReturn' : (s  : TypedStm  T Σ Γ) → TCM (returnStm  s)
checkReturn SEmpty = error "Function does not return"
checkReturn (s SCons ss) with checkReturn' s
... | inj₂ x = pure (SHead x)
... | inj₁ _ = SCon <$> checkReturn ss

checkReturn' (SBlock ss)       = SBlock  <$> checkReturn ss
checkReturn' (SIfElse x s1 s2) = SIfElse <$> checkReturn s1 <*> checkReturn s2
checkReturn' (SReturn x)       = pure SReturn
checkReturn' (SExp x)          = error "Exp does not return"
checkReturn' (SDecl t id x _)  = error "Exp does not return"
checkReturn' (SAss id e x)     = error "Exp does not return"
checkReturn' (SWhile x x₁)     = error "Exp does not return"

addReturnVoid : (T : Type) → TypedStms T Σ Γ → TypedStms T Σ Γ
addReturnVoid void SEmpty = SReturn vRet SCons SEmpty
addReturnVoid void (s SCons x) = s SCons (addReturnVoid void x)
addReturnVoid _    x = x


checkFun : (Σ : SymbolTab) (t : Type) (ts : List Type) → TopDef → TCM (Def Σ ts t)
checkFun Σ t ts (fnDef t' x as (block b)) = do
    refl ← t =?= t'
    let (ids , ts') = unzipWith (λ {(argument t id) → id , t}) as
    eqLists ts ts'
    let params = zip ids ts
    unique  ← checkUnique params
    ss'     ← addReturnVoid t <$> checkStms (params ∷ []) (deSugarList b)
    returns ← checkReturn ss'
    pparam  ← checkAll (_=/= void) ts
    pure (record { idents    = ids
                 ; body      = ss'
                 ; voidparam = pparam
                 ; unique    = unique
                 ; return    = returns })
  where open CheckStm Σ t


checkFuns : (Σ' Σ  : SymbolTab) → (def : List TopDef) → TCM (FunList Σ' Σ)
checkFuns Σ' [] [] = pure NIL
checkFuns Σ' [] (x ∷ def) = error "More functions than in SyTab"
checkFuns Σ' (x ∷ Σ) []   = error "More entries in symtab than defs"
checkFuns Σ' ((id , (ts , t)) ∷ Σ) (def ∷ defs) = do def'  ← checkFun  Σ' t ts def
                                                     defs' ← checkFuns Σ' Σ    defs
                                                     pure (def' :+ defs')

typeCheck : (builtin : SymbolTab) (P : Prog) → TCM TypedProgram
typeCheck b (program defs) = do
    let Σ = map getSymEntry defs
    let Σ' = b +++ Σ
    inList ([] , int) p ← lookupTCM (ident "main") Σ'
        where _ → error "Found main but with wrong type"
    unique ← checkUnique Σ'
    defs' ← checkFuns Σ' Σ defs
    pure (record { BuiltIn = b
                 ; Defs    = Σ
                 ; hasMain    = p
                 ; hasDefs    = defs'
                 ; uniqueDefs = unique })
