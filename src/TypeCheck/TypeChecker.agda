module TypeCheck.TypeChecker where

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
open import Data.List using (List; _∷_ ; []; map; zip; unzip; reverse) renaming (_++_ to _+++_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Function using (case_of_)

open import Javalette.AST hiding (String; Stmt) renaming (Expr to Exp; Ident to Id)
open import TypedSyntax renaming (Program to TypedProgram)
open import TypeCheck.Monad
open import TypeCheck.Util


builtin : SymbolTab
builtin = (ident "printInt"    , (int  ∷ [] , void))
        ∷ (ident "printString" , (void ∷ [] , void)) -- HACK for string
        ∷ (ident "printDouble" , (doub ∷ [] , void))
        ∷ (ident "readInt"     , (       [] , int ))
        ∷ (ident "readDouble"  , (       [] , doub)) ∷ []


mergeΧχ : List (Id × Id) → List (Id × List (Id × Type)) → TCM TypeTab
mergeΧχ [] χ            = pure []
mergeΧχ ((c , n) ∷ Χ) χ = do inList fs p ← lookupTCM c χ
                             rest ← mergeΧχ Χ χ
                             pure ((n , c , fs) ∷ rest)

getTopDef : List TopDef → (SymbolTab × List (Id × Id) × List (Id × List (Id × Type)))
getTopDef [] = [] , [] , []
getTopDef (x ∷ xs) with (Σ , Χ , χ) ← getTopDef xs with x
... | struct x fs = (Σ , Χ , (x , map (λ {(fieldE t x) → x , t}) fs) ∷ χ)
... | typeDef c n = (Σ , (c , n) ∷ Χ , χ)
... | fnDef t x as b = ((x , map fromArg as , t) ∷ Σ) , Χ , χ
  where fromArg : Arg → Type
        fromArg (argument t x) = t


checkUnique : (xs : List (Id × A)) → TCM (Unique xs)
checkUnique []              = pure []
checkUnique ((id , x) ∷ xs) = _∷_ <$> id notIn xs <*> checkUnique xs


open Valid renaming (Stm to TypedStm; Stms to TypedStms)


checkFun : (Σ : SymbolTab) (χ : TypeTab) (t : Type) (ts : List Type) → TopDef → TCM (Def Σ χ ts t)
checkFun Σ χ t ts (typeDef t₁ t₂) = error "TypeDef is not a function"
checkFun Σ χ t ts (struct x fs)   = error "struct  is not a function"
checkFun Σ χ t ts (fnDef t' x as (block b)) with
  params ← map (λ {(argument t id) → id , t}) as = do
    refl ← t =?= t'
    refl ← eqLists ts (dropAllId' params)
    unique  ← checkUnique params
    _ , ss' ← checkStms (params ∷ []) b
    returns ← CH.checkReturn ss'
    noVoid  ← checkAll (_=/= void) ts
    pure (record { params    = formatParams params
                 ; body      = toStms ss'
                 ; voidparam = noVoid
                 ; return    = returnProof returns
                 })
  where import TypeCheck.CheckExp Σ χ as CH
        open CH.CheckStatements t
        open import Translate Σ χ using (toStms; dropAllId')

        import TypeCheck.Proofs as TCP
        open TCP.ReturnsProof  Σ χ using (returnProof)

        formatParams : (Δ : List (Id × Type)) → Params (dropAllId' Δ)
        formatParams [] = []
        formatParams ((id , _) ∷ Δ) = id ∷ formatParams Δ

checkFuns : (χ : TypeTab) (Σ' Σ  : SymbolTab) → (def : List TopDef) → TCM (FunList χ Σ' Σ)
checkFuns χ Σ' [] [] = pure []
checkFuns χ Σ' [] (x ∷ def) = error "More functions than in SyTab"
checkFuns χ Σ' (x ∷ Σ) []   = error "More entries in symtab than defs"
checkFuns χ Σ' ((id , (ts , t)) ∷ Σ) (def ∷ defs) with def
... | typeDef x₁ x₂ = checkFuns χ Σ' ((id , ts , t) ∷ Σ) defs
... | struct x fs   = checkFuns χ Σ' ((id , ts , t) ∷ Σ) defs
... | def@(fnDef t₁ x as b) = do def'  ← checkFun  Σ' χ t ts def
                                 defs' ← checkFuns χ Σ' Σ    defs
                                 pure (def' ∷ defs')



typeCheck : (builtin : SymbolTab) (P : Prog) → TCM TypedProgram
typeCheck b (program defs) = do
    let Σ , Χ , χ = getTopDef defs
    let Σ' = b +++ Σ
    Ωχ ← mergeΧχ Χ χ
    inList ([] , int) p ← lookupTCM (ident "main") Σ'
        where _ → error "Found main but with wrong type"
    unique ← checkUnique Σ'
    defs' ← checkFuns Ωχ Σ' Σ defs
    pure (record { BuiltIn = b
                 ; Defs    = Σ
                 -- ; hasMain    = p
                 ; hasDefs    = defs'
                 ; uniqueDefs = unique })
