
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.List    using (List; _∷_; []; map) renaming (_++_ to _+++_; _ʳ++_ to _++r_)
open import Data.String  using (String; fromList; _++_; length)

open import Agda.Builtin.Int using (pos)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat  using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)

open import Function using (_$_; _∘_; case_of_)

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Effect.Monad
open import Effect.Monad.State
open import Effect.Monad.State.Transformer.Base using (mkStateT)
open RawMonadState {{...}}
open RawMonad {{...}}


open import Code hiding (TypeTab)
open import Javalette.AST using (ident; RelOp) renaming (Ident to Id; Type to OldType)
open import TypedSyntax hiding (T; Ts) renaming (* to mul; toSet to oldToSet; SymbolTab to OldSymbolTab)

module Compile where

open Typed
open Valid


llvmType  : OldType → Type
llvmTypes : List OldType → List Type
llvmType OldType.int  = i32
llvmType OldType.doub = float
llvmType OldType.bool = i1
llvmType OldType.void = void
llvmType (OldType.structT x) = named x *
llvmType (OldType.array t)  = struct (i32 ∷ array 0 (llvmType t) ∷ []) *
llvmType (OldType.fun t ts) = fun (llvmType t) (llvmTypes ts)

null : ∀ {t} → Operand (t *)
null = const 0

llvmTypes [] = []
llvmTypes (x ∷ xs) = llvmType x ∷ llvmTypes xs

toSetProof : (t : OldType) → oldToSet t ≡ toSet (llvmType t)
toSetProof OldType.int  = refl
toSetProof OldType.doub = refl
toSetProof OldType.bool = refl
toSetProof OldType.void = refl
toSetProof (OldType.structT x) = refl
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


-- Compiler monad
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
lookupFun : ∀ {Σ} → SymTab Σ → (id , ts , t) ∈ Σ → Operand (fun (llvmType t) (llvmTypes ts))
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

-- Might want to do somthing more safe than bitcast
lookupNamed : ∀ {n c fs} {χ : TypeTab} → Operand (named n *) → (n , c , fs) ∈ χ → CM Γ (Operand (struct (map (llvmType ∘ proj₂) fs) *))
lookupNamed x x₁ = emitTmp (bitCast x _)


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
fromEq (EqStruct {n}) = ptrFC (named n)


calloc : (n : Operand i32) → Operand i32 → Instruction (i8 *)
calloc n t = call (global (ident "calloc")) (n ∷ t ∷ [])

callocArray : (t : Type) → (n : Operand i32) → CM Γ (Operand (struct (i32 ∷ array 0 t ∷ []) *))
callocArray t n = do sucN ← emitTmp (arith i32 ArithOp.+ n (const (pos 1)))
                     size' ← emitTmp (getElemPtr {struct (i32 ∷ array 0 t ∷ [])} (const 0) 0
                                                                (struct (there (here refl)) ∷ array sucN ∷ []))
                     size ← emitTmp (ptrToInt size')

                     p ← emitTmp (calloc (const (pos 1)) size)
                     pArr ← emitTmp (bitCast p ((struct (i32 ∷ array 0 t ∷ [])) *))

                     len  ← emitTmp (getElemPtr pArr 0 ((struct (here refl)) ∷ []))
                     emit (store n len)
                     pure pArr


forArray : ∀ {t} → Operand (struct (i32 ∷ array 0 t ∷ []) *) → (Operand (t *) → CM Γ Bool) → CM Γ Bool
forArray arr f = do lenPtr ← emitTmp (getElemPtr arr 0 (struct (here refl) ∷ [])) -- index 0
                    len ← emitTmp (load lenPtr)

                    iPtr ← emitTmp (alloc i32)
                    emit (store (const (pos 0)) iPtr)

                    preCond ← newLabel
                    for     ← newLabel
                    end     ← newLabel

                    emit (jmp preCond)
                    putLabel preCond
                    i'   ← emitTmp (load iPtr)
                    cond ← emitTmp (cmp i32 RelOp.lTH i' len)
                    emit (branch cond for end) -- while i < len
                    putLabel for
                    valPtr ← emitTmp (getElemPtr arr 0 (struct (there (here refl)) ∷ array i' ∷ [])) -- index 1

                    sRet ← f valPtr
                    unless sRet do i'' ← emitTmp (arith i32 + i' (const (pos 1)))
                                   emit (store i'' iPtr)
                                   emit (jmp preCond)
                    putLabel end
                    pure sRet


-- Compilation using a given SymTab σ
module _ (σ : SymTab Σ) (χ : TypeTab) where

  compileExp : (e : Exp Σ χ Γ t) → CM Γ (Operand (llvmType t))
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
                                  res ← emitTmp (alloc i1)

                                  x' ← compileExp x
                                  emit (store x' res)
                                  case op of λ { && → emit (branch x' mid end)
                                               ; || → emit (branch x' end mid)}

                                  putLabel mid
                                  y' ← compileExp y
                                  emit (store y' res)
                                  emit (jmp end)

                                  putLabel end
                                  emitTmp (load res)

  compileExp (ENeg p e) = emitTmp =<< arith (fromNum p) ArithOp.- (const (toZero p)) <$> compileExp e
  compileExp (ENot e)   = emitTmp =<< cmp i1            RelOp.eQU (const false)      <$> compileExp e
  compileExp (EIdx arr i) = do arrPtr ← compileExp arr
                               i' ← compileExp i
                               iPtr ← emitTmp (getElemPtr arrPtr 0 (struct (there (here refl)) ∷ array i' ∷ [])) -- index 1
                               emitTmp (load iPtr)
  compileExp (EArray new) = callocNew new
    where callocNew : WFNew Σ χ Γ t → CM Γ (Operand (llvmType t))
          callocNew (nType  t len)     = callocArray (llvmType t) =<< compileExp len
          callocNew (nArray {t} n len) = do pArr ← callocArray (llvmType t) =<< compileExp len
                                            forArray pArr λ t* → do
                                                  new ← callocNew n
                                                  emit (store new t*)
                                                  pure false
                                            pure pArr
  compileExp (EStruct {n}) = do size' ← emitTmp (getElemPtr {named n} null 1 [])
                                size ← emitTmp (ptrToInt size')
                                p ← emitTmp (calloc (const (pos 1)) size)
                                emitTmp (bitCast p (named n *))

  compileExp ENull      = pure null
  compileExp (EDeRef x p p') = do x' ← compileExp x
                                  s ← lookupNamed x' p
                                  ptr ← emitTmp (getElemPtr s 0 ((struct (reShapeP' p')) ∷ []))
                                  emitTmp (load ptr)
      where reShapeP' : ∀ {t n} {fs : List (Id × OldType)} → (n , t) ∈ fs → llvmType t ∈ map (llvmType ∘ proj₂) fs
            reShapeP' (here refl) = here refl
            reShapeP' (there x) = there (reShapeP' x)
  compileExp (ELength x)  = do arr ← compileExp x
                               len ← emitTmp (getElemPtr arr 0 ((struct (here refl)) ∷ [])) -- index 0
                               emitTmp (load len)
  compileExp (EPrintStr x) = do gS c strs ← globalS <$> get
                                let str = fromList x ++ "\00"
                                let id = ident ("str" ++ showℕ c)
                                let globalOper = global {array (length str) i8 *} id
                                modify λ s → record s {globalS = gS (suc c) ((id , str) ∷ strs)}

                                operand ← emitTmp (getElemPtr globalOper 0 (array (const (pos 0)) ∷ []))
                                emitTmp (call (global (ident "printString")) (operand ∷ []))
  compileExp (EAPP id es p) = emitTmp =<< call (lookupFun σ p) <$> mapCompileExp es
    where mapCompileExp : TList (Exp Σ χ Γ) ts → CM Γ (TList Operand (llvmTypes ts))
          mapCompileExp [] = pure []
          mapCompileExp (x ∷ xs) = _∷_ <$> compileExp x <*> mapCompileExp xs



  -- compileStms returns true if it encountered a return
  -- This is used to return early
  compileStms  : (ss : Stms  Σ χ t Γ) → CM Γ Bool
  compileStms SEmpty = pure false
  compileStms (SExp x SCons ss) = do compileExp x
                                     compileStms ss
  compileStms (SDecl t id x p SCons ss) = do x' ← compileExp x
                                             withNewVar id x' $ compileStms ss
  compileStms (SAss id e x SCons ss)    = do emit =<< store <$> compileExp e <*> getPtr x
                                             compileStms ss
  compileStms (SAssIdx arr i x  SCons ss) = do arr' ← compileExp arr
                                               i' ← compileExp i
                                               x' ← compileExp x
                                               i'' ← emitTmp (getElemPtr arr' 0 ((struct (there (here refl))) ∷ (array i' ∷ []))) -- index 1
                                               emit (store x' i'')
                                               compileStms ss
  compileStms (SAssPtr e p p' x SCons ss) = do e' ← compileExp e
                                               x' ← compileExp x
                                               s ← lookupNamed e' p
                                               ptr ← emitTmp (getElemPtr s 0 ((struct (reShapeP' p')) ∷ []))
                                               emit (store x' ptr)
                                               compileStms ss
      where reShapeP' : ∀ {t n} {fs : List (Id × OldType)} → (n , t) ∈ fs → llvmType t ∈ map (llvmType ∘ proj₂) fs
            reShapeP' (here refl) = here refl
            reShapeP' (there x) = there (reShapeP' x)
  compileStms (SFor id arr s SCons ss) = do arr' ← compileExp arr
                                            forArray arr' λ v* → do
                                                  v ← emitTmp (load v*)
                                                  inNewBlock $ withNewVar id v (compileStms s)
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


  compileFun : GlobalState → Def Σ χ ts t → (FunDef (llvmSym Σ) (llvmTypes ts) (llvmType t) × GlobalState)
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

  compileFuns : {Σ' : OldSymbolTab} → FunList χ Σ Σ' → GlobalState → (FunList' (llvmSym Σ) (llvmSym Σ') × GlobalState)
  compileFuns []           g = [] , g
  compileFuns (def ∷ defs) g = let defs' , g'  = compileFuns defs g
                                   def'  , g'' = compileFun g' def
                               in  def' ∷ defs' , g''


compileProgram : Program → llvmProgram
compileProgram p =
  let defs , globState = compileFuns (mkSymTab uniqueDefs) χ hasDefs (gS 0 [])
                   in record
                     { BuiltIn = llvmSym BuiltIn
                     ; Defs    = llvmSym Defs
                     ; Strings = strings globState
                     ; hasDefs = help defs
                     ; χ = map (λ {(n , c , fs) → n , map (llvmType ∘ proj₂) fs}) χ
                     }
  where open Program p
        mkSymTab : Unique Σ → SymTab Σ
        mkSymTab [] = []
        mkSymTab (_∷_ {id} _ xs) = (global id) ∷ mkSymTab xs

        help : FunList' (llvmSym (BuiltIn +++ Defs)) (llvmSym Defs) → FunList' (llvmSym BuiltIn +++ llvmSym Defs) (llvmSym Defs)
        help x rewrite llvmSymHom BuiltIn Defs = x
