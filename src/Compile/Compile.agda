
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong)
open import Data.List.Relation.Unary.All using (All; lookup); open All
open import Data.List.Relation.Unary.All.Properties using (++⁺) renaming (gmap⁺ to allMap)
open import Data.List.Relation.Unary.Any using (Any); open Any
open import Data.List.Relation.Unary.Any.Properties using () renaming (gmap to anyMap)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star) renaming (ε to []; _◅_ to _∷_)

open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.List    using (List; _∷_; []; map) renaming (_++_ to _+++_; _ʳ++_ to _++r_)
open import Data.List.Properties using (map-++)
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

module Compile.Compile where


null : ∀ {t} → Operand (t *)
null = const 0

llvmType  : OldType → Type
llvmTypes : List OldType → List Type
llvmType OldType.int  = i32
llvmType OldType.doub = float
llvmType OldType.bool = i1
llvmType OldType.void = void
llvmType (OldType.structT x) = named x *
llvmType (OldType.array t)  = struct (i32 ∷ [ 0 × llvmType t ] ∷ []) *
llvmType (OldType.fun t ts) = fun (llvmType t) (llvmTypes ts)

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
BlockList = All (λ t → Operand (llvmType t *))

CtxList : Ctx → Set
CtxList = All BlockList

SymTab : OldSymbolTab → Set
SymTab = All (λ _ → Id)

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

addVar : Operand (llvmType t *) → CMState (Δ  ∷ Γ) → CMState ((t ∷ Δ) ∷ Γ)
addVar x (cMS g v t l (δ  ∷ γ) b) = cMS g v t l ((x ∷ δ) ∷ γ) b

removeVar : ∀ {t} → CMState ((t ∷ Δ) ∷ Γ) → CMState (Δ  ∷ Γ)
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

lookupPtr : CtxList Γ → t ∈' Γ → Operand (llvmType t *)
lookupPtr (x ∷ xs) (here p)  = lookup x p
lookupPtr (x ∷ xs) (there s) = lookupPtr xs s

getPtr : t ∈' Γ → CM Γ (Operand (llvmType t *))
getPtr p = do ctx ← ctxList <$> get
              pure (lookupPtr ctx p)

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


withNewVar : Operand (llvmType t)  → CM ((t ∷ Δ) ∷ Γ) A → CM (Δ ∷ Γ) A
withNewVar {t = t} x m = do v ← varC <$> get
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
llvmSym = map (λ (ts , t) → (llvmTypes ts , llvmType t))


fromNum : Num t → FirstClass (llvmType t)
fromNum NumInt    = i32
fromNum NumDouble = float

fromOrd : Ord t → FirstClass (llvmType t)
fromOrd OrdInt    = i32
fromOrd OrdDouble = float

fromEq : Eq t → FirstClass (llvmType t)
fromEq EqInt    = i32
fromEq EqBool   = i1
fromEq EqDouble = float
fromEq (EqStruct {n}) = ptrFC (named n)


calloc : (n : Operand i32) → Operand i32 → Instruction (i8 *)
calloc n t = call (global (ident "calloc")) (n ∷ t ∷ [])

callocArray : (t : Type) → (n : Operand i32) → CM Γ (Operand (struct (i32 ∷ [ 0 × t ] ∷ []) *))
callocArray t n = do sucN ← emitTmp (arith i32 ArithOp.+ n (const (pos 1)))
                     size' ← emitTmp (getElemPtr {struct (i32 ∷ [ 0 × t ] ∷ [])} null 0
                                                                (struct (there (here refl)) ∷ array sucN ∷ []))
                     size ← emitTmp (ptrToInt size')

                     i8*  ← emitTmp (calloc (const (pos 1)) size)
                     arr* ← emitTmp (bitCast i8* (struct (i32 ∷ [ 0 × t ] ∷ []) *))

                     len  ← emitTmp (getElemPtr arr* 0 (struct (here refl) ∷ []))
                     emit (store n len)
                     pure arr*


forArray : ∀ {t} → Operand (struct (i32 ∷ [ 0 × t ] ∷ []) *) → (Operand (t *) → CM Γ Bool) → CM Γ Bool
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

  open Typed Σ χ
  open Valid Σ χ

  compileExp : (e : Exp Γ t) → CM Γ (Operand (llvmType t))
  compileExp (EValue {t} x) rewrite toSetProof t = pure (const x)
  compileExp (EId x)           = emitTmp =<< load <$> getPtr x

  compileExp (EOp (OpNum p op) x y) = emitTmp =<< arith (fromNum p) op  <$> compileExp x <*> compileExp y
  compileExp (EOp OpMod     x    y) = emitTmp =<< srem                  <$> compileExp x <*> compileExp y
  compileExp (EOp (OpOrd p op) x y) = emitTmp =<< cmp   (fromOrd p) op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { <  → RelOp.lTH ; <= → RelOp.lE
                             ; >  → RelOp.gTH ; >= → RelOp.gE }
  compileExp (EOp (OpEq p op) x y) = emitTmp =<< cmp   (fromEq  p) op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { == → RelOp.eQU ; != → RelOp.nE }

  compileExp (EOp (OpLogic op) x y) = do mid ← newLabel
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

  compileExp (EIdx arr i) = do arrPtr ← compileExp arr
                               i' ← compileExp i
                               iPtr ← emitTmp (getElemPtr arrPtr 0 (struct (there (here refl)) ∷ array i' ∷ [])) -- index 1
                               emitTmp (load iPtr)
  compileExp (EArray new) = callocNew =<< compileWFNew new
    where compileWFNew : WFNew (Exp Γ OldType.int) OldType.array t → CM Γ (WFNew (Operand i32) (λ t → struct (i32 ∷ [ 0 × t ] ∷ []) *) (llvmType t))
          compileWFNew (nType  x)    = nType  <$> compileExp x
          compileWFNew (nArray x xs) = nArray <$> compileExp x <*> compileWFNew xs

          callocNew : ∀ {t} → WFNew (Operand i32) (λ t → struct (i32 ∷ [ 0 × t ] ∷ []) *) t → CM Γ (Operand t)
          callocNew (nType  len)   = callocArray _ len
          callocNew (nArray len n) = do pArr ← callocArray _ len
                                        forArray pArr λ t* → do
                                              new ← callocNew n
                                              emit (store new t*)
                                              pure false
                                        pure pArr
  compileExp (EStruct {n}) = do size' ← emitTmp (getElemPtr {named n} null 1 [])
                                size ← emitTmp (ptrToInt size')
                                p ← emitTmp (calloc (const (pos 1)) size)
                                emitTmp (bitCast p (named n *))

  compileExp (EDeRef x p p') = do x' ← compileExp x
                                  s ← lookupNamed x' p
                                  ptr ← emitTmp (getElemPtr s 0 (struct (anyMap (λ {refl → refl}) p') ∷ []))
                                  emitTmp (load ptr)
  compileExp (ELength x)  = do arr ← compileExp x
                               len ← emitTmp (getElemPtr arr 0 ((struct (here refl)) ∷ [])) -- index 0
                               emitTmp (load len)
  compileExp (EPrintStr x) = do gS c strs ← globalS <$> get
                                let str = fromList x ++ "\00"
                                let id = ident ("str" ++ showℕ c)
                                let globalOper = global {[ length str × i8 ] *} id
                                modify λ s → record s {globalS = gS (suc c) ((id , str) ∷ strs)}

                                operand ← emitTmp (getElemPtr globalOper 0 (array (const (pos 0)) ∷ []))
                                emitTmp (call (global (ident "printString")) (operand ∷ []))
  compileExp (EAPP p es) = emitTmp =<< call (global (lookup σ p)) <$> mapCompileExp es
    where mapCompileExp : All (Exp Γ) ts → CM Γ (All Operand (llvmTypes ts))
          mapCompileExp []       = pure []
          mapCompileExp (x ∷ xs) = _∷_ <$> compileExp x <*> mapCompileExp xs



  -- compileStms returns true if it encountered a return
  -- This is used to return early
  compileStms  : (ss : Stms  t Γ) → CM Γ Bool
  compileStms [] = pure false
  compileStms (SExp x ∷ ss) = do compileExp x
                                 compileStms ss
  compileStms (SDecl t x ∷ ss) = do x' ← compileExp x
                                    withNewVar x' $ compileStms ss
  compileStms (SAss p e  ∷ ss) = do emit =<< store <$> compileExp e <*> getPtr p
                                    compileStms ss
  compileStms (SAssIdx arr i x  ∷ ss) = do arr' ← compileExp arr
                                           i' ← compileExp i
                                           x' ← compileExp x
                                           i'' ← emitTmp (getElemPtr arr' 0 ((struct (there (here refl))) ∷ (array i' ∷ []))) -- index 1
                                           emit (store x' i'')
                                           compileStms ss
  compileStms (SAssPtr e p p' x ∷ ss) = do e' ← compileExp e
                                           x' ← compileExp x
                                           s ← lookupNamed e' p
                                           ptr ← emitTmp (getElemPtr s 0 ((struct (anyMap (λ {refl → refl}) p')) ∷ []))
                                           emit (store x' ptr)
                                           compileStms ss
  compileStms (SFor arr s ∷ ss) = do arr' ← compileExp arr
                                     forArray arr' λ v* → do
                                           v ← emitTmp (load v*)
                                           inNewBlock $ withNewVar v (compileStms s)
                                     compileStms ss
  compileStms (SWhile x s  ∷ ss) = do preCond ← newLabel
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
  compileStms (SBlock s ∷ ss) = do b ← inNewBlock $ compileStms s
                                   if b then pure true
                                        else compileStms ss
  compileStms (SIfElse x t f ∷ ss) = do trueL  ← newLabel
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
  compileStms (SReturn vRet ∷ _)    = do emit vret
                                         pure true
  compileStms (SReturn (Ret x) ∷ _) = do x' ← compileExp x
                                         emit (ret x')
                                         pure true


  compileFun : GlobalState → Def Σ χ ts t → (FunDef (llvmSym Σ) (llvmTypes ts) (llvmType t) × GlobalState)
  compileFun glob def = let s , f = runCM compileBody (initState glob)
                        in f , globalS s
    where open Def def
          withInitBlock : Named Δ → CM (Δ ∷ []) A → CM ([] ∷ []) A
          withInitBlock [] m = m
          withInitBlock (i ∷ is) m = withInitBlock is (withNewVar (local i) m)

          llvmParams : ∀ {ts} → Named ts → Named (llvmTypes ts)
          llvmParams []         = []
          llvmParams (px ∷ pxs) = px ∷ llvmParams pxs

          compileBody : CM ([] ∷ []) (FunDef _ _ _)
          compileBody = do putLabel (ident "entry")
                           withInitBlock params do
                                 compileStms body
                                 body ← block <$> get
                                 pure (record { funId = funId
                                              ; params = llvmParams params
                                              ; body = body
                                              })

  compileFuns : {Σ' : OldSymbolTab} → FunList χ Σ Σ' → GlobalState → (FunList' (llvmSym Σ) (llvmSym Σ') × GlobalState)
  compileFuns []           g = [] , g
  compileFuns (def ∷ defs) g = let defs' , g'  = compileFuns defs g
                                   def'  , g'' = compileFun g' def
                               in  def' ∷ defs' , g''


compileProgram : Program → llvmProgram
compileProgram p =
  let defs , globState = compileFuns NamedFuns χ hasDefs (gS 0 [])
                   in record
                     { NamedBuiltIn = allMap (λ x → x) NamedBuiltIn
                     ; Strings = strings globState
                     ; hasDefs = help defs
                     ; χ = map (λ {(n , c , fs) → n , map (llvmType ∘ proj₂) fs}) χ
                     }
  where open Program p

        help : FunList' (llvmSym (BuiltIn +++ Defs)) (llvmSym Defs) → FunList' (llvmSym BuiltIn +++ llvmSym Defs) (llvmSym Defs)
        help x rewrite map-++ (λ (ts , t) → (llvmTypes ts , llvmType t)) BuiltIn Defs = x
