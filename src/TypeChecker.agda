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
open import Data.List using (List; _∷_ ; []; map; zip; unzipWith; reverse) renaming (_++_ to _+++_)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Function using (case_of_)

open import Javalette.AST hiding (String; Stmt) renaming (Expr to Exp; Ident to Id)
open import TypedSyntax Id renaming (Program to TypedProgram)
open import TypeCheckerMonad
open import Util


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


checkUnique : (xs : List (Id × A)) → TCM (Unique xs)
checkUnique []              = pure []
checkUnique ((id , x) ∷ xs) = _∷_ <$> id notIn xs <*> checkUnique xs


open Valid renaming (Stm to TypedStm; Stms to TypedStms)


checkFun : (Σ : SymbolTab) (t : Type) (ts : List Type) → TopDef → TCM (Def Σ ts t)
checkFun Σ t ts (fnDef t' x as (block b)) = do
    refl ← t =?= t'
    let (ids , ts') = unzipWith (λ {(argument t id) → id , t}) as
    eqLists ts ts'
    let params = zip ids ts
    unique  ← checkUnique params
    _ , ss' ← checkStms (reverse params ∷ []) b
    returns ← CH.checkReturn ss'
    pparam  ← checkAll (_=/= void) ts
    pure (record { idents    = ids
                 ; body      = toStms ss'
                 ; voidparam = pparam
                 ; unique    = unique
                 ; return    = returnProof returns })
  where import CheckExp Σ as CH
        open CH.CheckStatements t
        open import Translate Σ using (toStms)

        import TypeCheckerProofs as TCP 
        open TCP.ReturnsProof  Σ using (returnProof)

checkFuns : (Σ' Σ  : SymbolTab) → (def : List TopDef) → TCM (FunList Σ' Σ)
checkFuns Σ' [] [] = pure []
checkFuns Σ' [] (x ∷ def) = error "More functions than in SyTab"
checkFuns Σ' (x ∷ Σ) []   = error "More entries in symtab than defs"
checkFuns Σ' ((id , (ts , t)) ∷ Σ) (def ∷ defs) = do def'  ← checkFun  Σ' t ts def
                                                     defs' ← checkFuns Σ' Σ    defs
                                                     pure (def' ∷ defs')

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
                 -- ; hasMain    = p
                 ; hasDefs    = defs'
                 ; uniqueDefs = unique })
