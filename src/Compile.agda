{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product using (_×_; _,_; ∃; map₂) renaming (proj₁ to fst; proj₂ to snd)
open import Data.List using (List; _∷_; []; map) renaming (_++_ to _+++_; _ʳ++_ to _++r_)
open import Data.List.Relation.Unary.All using (All); open All

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)

open import Data.String using (String; fromList; unwords; unlines; intersperse; _++_; length)
open import Agda.Builtin.Int using (pos) renaming (primShowInteger to showℤ)
open import Data.Float using () renaming (show to showℝ)
import Data.Bool as Bool
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Function using (_$_; _∘_; case_of_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Effect.Monad
open import Effect.Monad.State
open import Effect.Monad.State.Transformer.Base using (mkStateT)
open RawMonadState {{...}}
open RawMonad {{...}}


open import Code
open import Javalette.AST using (ident; RelOp) renaming (Ident to Id; Type to OldType)
open import TypedSyntax Id hiding (T; Ts; toZero) renaming (* to mul; toSet to oldToSet; SymbolTab to OldSymbolTab) 

module Compile where


llvmType  : OldType → Type
llvmTypes : List OldType → List Type
llvmType OldType.int  = i32
llvmType OldType.doub = float
llvmType OldType.bool = i1
llvmType OldType.void = void
llvmType (OldType.array t) = (struct (i32 ∷ llvmType t * ∷ [])) *
llvmType (OldType.fun t ts) = fun (llvmType t) (llvmTypes ts)

llvmTypes [] = []
llvmTypes (x ∷ xs) = llvmType x ∷ llvmTypes xs

toSetProof : (t : OldType) → oldToSet t ≡ toSet (llvmType t)
toSetProof OldType.int  = refl
toSetProof OldType.doub = refl
toSetProof OldType.bool = refl
toSetProof OldType.void = refl
toSetProof (OldType.array t) = refl
toSetProof (OldType.fun t ts) = refl

BlockList : Block → Set
BlockList Δ = TList (λ (id , t) → Operand (llvmType t *)) Δ

CtxList : Ctx → Set
CtxList Γ = TList BlockList  Γ 

SymTab : OldSymbolTab → Set
SymTab Σ = TList (λ (id , (ts , t)) → Operand (fun (llvmType t) (llvmTypes ts))) Σ

record GlobalState : Set where
  constructor gS
  field
    globalC : ℕ
    strings : List (Id × String)

open GlobalState

record CMState (Γ : Ctx) : Set where
  constructor cMS
  field 
    globalS : GlobalState 
    varC tmpC labelC : ℕ
    ctxList : CtxList Γ
    block   : Code

open CMState

initState : GlobalState → CMState ([] ∷ [])
initState glob = cMS glob 0 0 0 ([] ∷ []) []

addBlock : CMState Γ → CMState ([] ∷ Γ)
addBlock (cMS g v t l c b) = cMS g v t l ([] ∷ c) b

removeBlock : CMState (Δ ∷ Γ) → CMState Γ
removeBlock (cMS g v t l (_ ∷ c) b) = cMS g v t l (c) b

addVar : Operand (llvmType t *) → CMState (Δ  ∷ Γ) → CMState (((id , t) ∷ Δ) ∷ Γ)
addVar x (cMS g v t l (δ  ∷ γ) b) = cMS g v t l ((x ∷ δ) ∷ γ) b 

removeVar : ∀ {id t} → CMState (((id , t) ∷ Δ) ∷ Γ) → CMState (Δ  ∷ Γ)
removeVar (cMS g v t l ((_ ∷ δ) ∷ γ) b) = cMS g v t l (δ  ∷ γ) b

CM : (Γ : Ctx) → Set → Set
CM Γ = State (CMState Γ)

instance
  CMMonadState : ∀ {Γ} → RawMonadState (CMState Γ) (CM Γ)
  CMMonadState {Γ} = monadState

  CMMonad : ∀ {Γ} → RawMonad (CM Γ)
  CMMonad = monad

runCM : CM Γ A → CMState Γ → (CMState Γ × A)
runCM m s = runState m s

toZero : {T : OldType} → Num T → toSet (llvmType T)
toZero NumInt    = pos 0
toZero NumDouble = 0.0

lookupPtr' : BlockList Δ → (id , t) ∈ Δ → Operand (llvmType t *)
lookupPtr' (x ∷ b) (here refl) = x
lookupPtr' (_ ∷ b) (there x)   = lookupPtr' b x

lookupPtr : CtxList Γ → (id , t) ∈' Γ → Operand (llvmType t *)
lookupPtr (x ∷ xs) (here p)  = lookupPtr' x p
lookupPtr (x ∷ xs) (there s) = lookupPtr xs s

getPtr : (id , t) ∈' Γ → CM Γ (Operand (llvmType t *))
getPtr p = do ctx ← ctxList <$> get
              pure (lookupPtr ctx p)

-- not sure if functions are Ptr
lookupFun : SymTab Σ → (id , ts , t) ∈ Σ → Operand (fun (llvmType t) (llvmTypes ts))
lookupFun (x ∷ _)  (here refl) = x
lookupFun (_ ∷ xs) (there p)   = lookupFun xs p

emit : Instruction T → CM Γ ⊤
emit x = modify (λ s → record s {block = x ∷ block s })

emitTmp : Instruction T → CM Γ (Operand T)
emitTmp {void} x = do modify λ s → record s {block = x ∷ block s}
                      pure (local (ident "This_void_tmp_should_never_be_used"))
emitTmp {T} x = do tmp ← tmpC <$> get
                   let operand = local (ident $ "t" ++ showℕ tmp)
                   modify λ s → record s { block = operand := x ∷ block s
                                         ; tmpC = suc (tmpC s)}
                   pure operand


withNewVar : (id : Id) → Operand (llvmType t)  → CM (((id , t) ∷ Δ) ∷ Γ) A → CM (Δ ∷ Γ) A
withNewVar {t = t} _ x m = do v ← varC <$> get
                              let p = local $ ident ("v" ++ showℕ v)
                              modify λ s → record s { block = store x p ∷ p := alloc (llvmType t) ∷ block s
                                                            ; varC  = suc (varC s)}
                              s ← get
                              let (s' , a) = runState m (addVar p s)
                              put (removeVar s')
                              pure a

inNewBlock : CM ([] ∷ Γ) A → CM Γ A
inNewBlock m = do x ← get
                  let (x' , a) = runState m (addBlock x)
                  put (removeBlock x')
                  pure a

newLabel : CM Γ Label
newLabel = do l ← labelC <$> get 
              modify λ s → record s {labelC = suc (labelC s)}
              pure $ ident ("L" ++ showℕ l)

putLabel : Label → CM Γ ⊤
putLabel l = modify λ s → record s {block = label l ∷ block s}

-- Used for lazy evaluation of ||, &&.
-- Should be removed during simplification
curentLabel : CM Γ Label
curentLabel = do l ← newLabel
                 emit (jmp l)
                 putLabel l
                 pure l

llvmSym : OldSymbolTab → SymbolTab
llvmSym [] = []
llvmSym ((id , ts , t) ∷ xs) = (id , llvmTypes ts , llvmType t) ∷ llvmSym xs

llvmSymHom : (Σ' Σ : OldSymbolTab) → llvmSym (Σ' +++ Σ) ≡ (llvmSym Σ' +++ llvmSym Σ)
llvmSymHom [] Σ = refl
llvmSymHom (x ∷ Σ') Σ rewrite llvmSymHom Σ' Σ = refl


fromNum : Num t → FirstClass (llvmType t)
fromNum NumInt    = lint 31
fromNum NumDouble = float

fromOrd : Ord t → FirstClass (llvmType t)
fromOrd OrdInt    = lint 31
fromOrd OrdDouble = float

fromEq : Eq t → FirstClass (llvmType t)
fromEq EqInt    = lint 31
fromEq EqBool   = lint 0
fromEq EqDouble = float

sizeOfType : ∀ {t} → Basic t → toSet i32
sizeOfType BasicInt  = pos 4
sizeOfType BasicDoub = pos 4
sizeOfType BasicBool = pos 1

-- Compilation using a given SymTab σ
module _ (σ : SymTab Σ) where
  open Typed 
  open Valid 

  compileExp : (e : Exp Σ Γ t) → CM Γ (Operand (llvmType t))
  compileExp (EValue {t} x) rewrite toSetProof t = pure (const x)
  compileExp (EId id x)        = emitTmp =<< load <$> getPtr x
  compileExp (EArith p x op y) = emitTmp =<< arith (fromNum p) op  <$> compileExp x <*> compileExp y
  compileExp (EMod     x    y) = emitTmp =<< srem                  <$> compileExp x <*> compileExp y
  compileExp (EOrd   p x op y) = emitTmp =<< cmp   (fromOrd p) op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { <  → RelOp.lTH ; <= → RelOp.lE
                             ; >  → RelOp.gTH ; >= → RelOp.gE }
  compileExp (EEq    p x op y) = emitTmp =<< cmp   (fromEq  p) op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { == → RelOp.eQU ; != → RelOp.nE }

  compileExp (ELogic x op y) = do mid ← newLabel
                                  end ← newLabel

                                  x' ← compileExp x
                                  postx ← curentLabel
                                  case op of λ { && → emit (branch x' mid end)
                                               ; || → emit (branch x' end mid)}

                                  putLabel mid
                                  y' ← compileExp y
                                  posty ← curentLabel
                                  emit (jmp end)

                                  putLabel end
                                  emitTmp (phi ((x' , postx) ∷ (y' , posty) ∷ []))

  compileExp (ENeg p e) = emitTmp =<< arith (fromNum p) ArithOp.- (const (toZero p)) <$> compileExp e
  compileExp (ENot e)   = emitTmp =<< cmp i1 RelOp.eQU (const Bool.false) <$> compileExp e
  compileExp (EIdx arr i) = do i' ← emitTmp =<< getArray <$> compileExp arr <*> compileExp i
                               emitTmp (load i')
  compileExp (ENew (nType {t} x n)) = do n' ← compileExp n
                                         arr ← emitTmp (alloc (struct (i32 ∷ llvmType t * ∷ [])))
                                         arr' ← emitTmp (getStruct arr (there (here refl))) -- index 1
                                         t* ← emitTmp (call (global (ident "calloc")) (n' ∷ const {i32} (sizeOfType x) ∷ [])) -- should define calloc properly
                                         emit (store t* arr')
                                         pure arr
  compileExp (ENew (nArray x n)) = {!!}
  compileExp (ELength x)  = do x' ← compileExp x
                               len ← emitTmp (getStruct x' (here refl)) -- index 0
                               emitTmp (load len)
  compileExp (EPrintStr x) = do gS c strs ← globalS <$> get
                                let id = ident ("str" ++ showℕ c)
                                let gs = gS (suc c) ((id , fromList x ++ "\00") ∷ strs)
                                modify λ s → record s {globalS = gs}
                                operand ← emitTmp (getStr (suc (length (fromList x))) id)
                                emitTmp (call (global (ident "printString")) (operand ∷ []))
  compileExp (EAPP id es p) = emitTmp =<< call (lookupFun σ p) <$> mapCompileExp es
    where mapCompileExp : TList (Exp Σ Γ) ts → CM Γ (TList Operand (llvmTypes ts))
          mapCompileExp [] = pure []
          mapCompileExp (x ∷ xs) = _∷_ <$> compileExp x <*> mapCompileExp xs



  -- compileStms returns true if it encountered a return
  -- This is used to return early
  compileStms  : (ss : Stms  Σ t Γ) → CM Γ Bool
  compileStms SEmpty = pure false
  compileStms (SExp x SCons ss) = do compileExp x
                                     compileStms ss
  compileStms (SDecl t id x p SCons ss) = do x' ← compileExp x
                                             withNewVar id x' $ compileStms ss
  compileStms (SAss id e x SCons ss)    = do emit =<< store <$> compileExp e <*> getPtr x
                                             compileStms ss
  compileStms (SAssIdx arr i x  SCons ss) = do x' ← compileExp x
                                               i' ← emitTmp =<< getArray <$> compileExp arr <*> compileExp i
                                               emit (store x' i')
                                               compileStms ss
  compileStms (SFor id arr s SCons ss) = do arr' ← compileExp arr
                                            lenPtr ← emitTmp (getStruct arr' (here refl)) -- index 0
                                            len ← emitTmp (load lenPtr)

                                            iPtr ← emitTmp (alloc i32)
                                            preCond ← newLabel
                                            for     ← newLabel
                                            end     ← newLabel

                                            putLabel preCond
                                            i'   ← emitTmp (load iPtr)
                                            iter ← emitTmp (cmp i32 RelOp.lTH i' len)
                                            emit (branch iter for end) -- while i < len
                                            putLabel for
                                            val ← emitTmp ∘ load =<< emitTmp (getArray arr' i')
                                            sRet ← inNewBlock $ withNewVar id val (compileStms s)
                                            unless sRet do i'' ← emitTmp (arith i32 + i' (const (pos 1)))
                                                           emit (store i'' iPtr)
                                                           emit (jmp preCond)
                                            putLabel end
                                            compileStms ss
  compileStms (SWhile x s  SCons ss) = do preCond ← newLabel
                                          loop    ← newLabel
                                          end     ← newLabel

                                          emit (jmp preCond)
                                          putLabel preCond
                                          x' ← compileExp x
                                          emit (branch x' loop end)

                                          putLabel loop
                                          inNewBlock (compileStms s >> emit (jmp preCond))
                                          putLabel end
                                          compileStms ss
  compileStms (SBlock s SCons ss) = do b ← inNewBlock $ compileStms s
                                       if b then pure true
                                            else compileStms ss
  compileStms (SIfElse x t f SCons ss) = do trueL  ← newLabel
                                            falseL ← newLabel
                                            end    ← newLabel

                                            x' ← compileExp x
                                            emit (branch x' trueL falseL)
                                            putLabel trueL
                                            tRet  ← inNewBlock $ compileStms t
                                            unless tRet $ emit (jmp end)

                                            putLabel falseL
                                            fRet ← inNewBlock $ compileStms f
                                            unless fRet $ emit (jmp end)

                                            if tRet ∧ fRet then pure true
                                                            else do putLabel end
                                                                    compileStms ss
  compileStms (SReturn vRet SCons _)    = do emit vret
                                             pure true
  compileStms (SReturn (Ret x) SCons _) = do x' ← compileExp x
                                             emit (ret x')
                                             pure true


  compileFun : GlobalState → Def Σ ts t → (FunDef (llvmSym Σ) (llvmTypes ts) (llvmType t) × GlobalState)
  compileFun glob def = let s , f = runCM compileBody (initState glob)
                        in f , globalS s
    where open Def def
          withInitBlock : Unique Δ → CM ((Δ ++r Δ') ∷ []) A → CM (Δ' ∷ []) A
          withInitBlock [] m = m
          withInitBlock (_∷_ {id} p xs) m = withNewVar id (local id) (withInitBlock xs m)

          compileBody : CM ([] ∷ []) (FunDef _ _ _)
          compileBody = do putLabel (ident "entry")
                           withInitBlock unique do
                                 compileStms body
                                 body ← block <$> get
                                 pure (record { idents = idents
                                              ; body = body
                                              })

  compileFuns : {Σ' : OldSymbolTab} → FunList Σ Σ' → GlobalState → (FunList' (llvmSym Σ) (llvmSym Σ') × GlobalState)
  compileFuns []           g = [] , g
  compileFuns (def ∷ defs) g = let defs' , g'  = compileFuns defs g
                                   def'  , g'' = compileFun g' def
                               in  def' ∷ defs' , g''


compileProgram : Program → llvmProgram
compileProgram p =
  let defs , globState = compileFuns (mkSymTab uniqueDefs) hasDefs (gS 0 [])
                   in record
                     { BuiltIn = llvmSym BuiltIn
                     ; Defs    = llvmSym Defs
                     ; Strings = strings globState
                     ; hasDefs = help defs
                     }
  where open Program p
        mkSymTab : Unique Σ → SymTab Σ
        mkSymTab [] = []
        mkSymTab (_∷_ {id} _ xs) = (global id) ∷ mkSymTab xs

        help : FunList' (llvmSym (BuiltIn +++ Defs)) (llvmSym Defs) → FunList' (llvmSym BuiltIn +++ llvmSym Defs) (llvmSym Defs)
        help x rewrite llvmSymHom BuiltIn Defs = x


-- printing llvm code
module _ where

  pType :      Type → String
  pTypeList : List Type → String
  pType (lint n)  = "i" ++ showℕ (suc n)
  pType float = "double"
  pType void  = "void"
  pType (t *) = pType t ++ "*"
  pType (struct ts) = "{" ++ pTypeList ts ++ "}"
  pType (fun t ts) = pType t ++ " (" ++ pTypeList ts ++ ")"

  pTypeList [] = ""
  pTypeList (x ∷ []) = pType x
  pTypeList (y ∷ x ∷ xs) = pType y ++ ", " ++ pTypeList (x ∷ xs)


  pOperand : Operand T → String
  pOperand {T} (const x) with T
  ... | float = showℝ x
  ... | t *   = "null"  -- is null the only ptr constant?
  ... | (lint n) with n
  ... | suc _ = showℤ x 
  ... | zero with x 
  ... | Bool.false = "false"
  ... | Bool.true  = "true"
  pOperand {_} (local  (ident x)) = "%" ++ x
  pOperand {_} (global (ident x)) = "@" ++ x

  pPairOperand : (x y : Operand T) → String
  pPairOperand {T} x y = pType T ++ " " ++ pOperand x ++ " , " ++ pOperand y

  pTypeOper : Operand T → String
  pTypeOper {T} x = pType T ++ " " ++ pOperand x

  pLabel : Label → String
  pLabel (ident x) = "label %" ++ x

  -- Helper functions for pInst
  private
    pArith : FirstClass T → ArithOp → String
    pArith (lint n) = λ { + →  "add"; - →  "sub"; mul →  "mul"; / → "sdiv"}
    pArith float    = λ { + → "fadd"; - → "fsub"; mul → "fmul"; / → "fdiv"}

    open RelOp
    pCmp : FirstClass T → RelOp → String
    pCmp (lint _)  = ("icmp " ++_) ∘ λ { lTH → "slt"; lE → "sle"; gTH → "sgt"; gE → "sge"; eQU →  "eq"; nE →  "ne"}
    pCmp float = ("fcmp " ++_) ∘ λ { lTH → "ult"; lE → "ule"; gTH → "ugt"; gE → "uge"; eQU → "ueq"; nE → "une"}

    pCall : All Operand Ts → String
    pCall (_∷_ {t} y (x ∷ xs)) = pType t ++ " " ++ pOperand y ++ ", " ++ pCall (x ∷ xs)
    pCall (_∷_ {t} x [])       = pType t ++ " " ++ pOperand x
    pCall [] = ""

    pPhi : List (Operand T × Id) → List String
    pPhi = map λ {(x , ident l) → "[ " ++ pOperand x ++ ", %" ++ l ++ " ]"}

    pTypeDeptr : ∀ {t} → Operand (t *) → String
    pTypeDeptr {t} x = pType t


  pInst : Instruction T → String
  pInst {T} inst with inst
  ... | arith p op x y = unwords $ pArith p op ∷ pPairOperand x y ∷ []
  ... | cmp   p op x y = unwords $ pCmp   p op ∷ pPairOperand x y ∷ []
  ... | srem       x y = unwords $ "srem"      ∷ pPairOperand x y ∷ []
  ... | alloc t        = unwords $ "alloca" ∷ pType t     ∷ []
  ... | load x         = unwords $ "load"   ∷ pType T     ∷ "," ∷ pTypeOper x ∷ []
  ... | store o p      = unwords $ "store"  ∷ pTypeOper o ∷ "," ∷ pTypeOper p ∷ []
  ... | call (global (ident "printString")) (x ∷ []) = "call void @printString( i8* " ++ pOperand x ++ ")"
  ... | call x xs = unwords $ "call"   ∷ (pTypeOper x ++ "(" ) ∷ pCall xs ∷ ")" ∷ []
  ... | getStr n (ident x) = unwords $ "getelementptr [" ∷ showℕ n ∷ "x i8], [" ∷ showℕ n ∷ "x i8]*" ∷ ("@" ++ x) ∷ ", i32 0, i32 0" ∷ []
  ... | getStruct {t} s i = unwords $ "getelementptr " ∷ pTypeDeptr s ∷ "," ∷ pTypeOper s ∷ ", i32 0, i32 " ∷ showℕ (toℕ i) ∷ []
          where toℕ : ∀ {t ts} → t ∈ ts → ℕ
                toℕ (here px) = 0
                toℕ (there x) = suc (toℕ x)
  ... | getArray arr i = unwords $ "getelementptr " ∷ pTypeDeptr arr ∷ "," ∷ pTypeOper arr ∷ ", i32 0, i32 1," ∷ pTypeOper i ∷ []
  ... | phi x  = unwords $ "phi" ∷ pType T ∷ intersperse ", " (pPhi x) ∷ []
  ... | vret   = unwords $ "ret" ∷ "void" ∷ []
  ... | ret x  = unwords $ "ret" ∷ pTypeOper x ∷ []
  ... | jmp x  = unwords $ "br"  ∷ pLabel x ∷ []
  ... | branch x t f =  unwords $ "br" ∷ "i1" ∷ pOperand x ∷ "," ∷ pLabel t ∷ "," ∷ pLabel f ∷ []
  ... | label (ident x) = "error: lables should have been handled in pCode"

  -- Should maybe reverse the order of code when compiling
  pCode : Code → String
  pCode [] = ""
  pCode (label (ident l) ∷ xs) = pCode xs ++ l ++ ": \n"
  pCode (x ∷ xs)      = pCode xs ++ "  " ++                        pInst x ++ "\n"
  pCode (o := x ∷ xs) = pCode xs ++ "  " ++ pOperand o ++ " = " ++ pInst x ++ "\n"

  pFun : {Σ : SymbolTab} → Id → FunDef Σ Ts T → String
  pFun {T = T} (ident id) def =
       let header = unwords $ "define" ∷ pType T ∷ ("@" ++ id) ∷ pParams ∷ "{" ∷ []
       in intersperse "\n" $ header ∷ pCode body ∷ "}" ∷ []
    where open FunDef def
          pParams = "(" ++ intersperse ", " (map (λ {(ident i , t) → pType t ++ " %" ++ i}) params) ++ ")"

  pProgram : llvmProgram → String
  pProgram p = intersperse "\n\n" $ unlines pBuiltIn ∷ unlines pStrings ∷ pDefs hasDefs
    where open llvmProgram p
          pStrings : List String
          pStrings = map (λ {(ident i , s) →
                         "@" ++ i ++ " = internal constant [ " ++ showℕ (length s) ++ " x i8 ] c\"" ++ s ++ "\""}) Strings
          pBuiltIn : List String
          pBuiltIn = map (λ
                       { (ident "printString" , _) → "declare void @printString(i8*)" -- since we use a "hack" for printString
                       ; (ident i , ts , t) →
                              "declare " ++ pType t ++ " @" ++ i ++ "(" ++ intersperse ", " (map pType ts) ++ ")" }) BuiltIn

          pDefs : ∀ {Σ' Σ} → FunList' Σ' Σ → List String
          pDefs [] = []
          pDefs (_∷_ {i , _} x xs) = pFun i x ∷ pDefs xs
