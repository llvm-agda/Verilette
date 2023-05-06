open import Data.Product using (_×_; _,_; ∃; map₂) renaming (proj₁ to fst; proj₂ to snd)
open import Data.List using (List; _∷_ ; []; _++_; length)
open import Data.List.Relation.Unary.All using (All; map); open All

open import Data.String using (String; fromList) renaming (_++_ to _++s_)
open import Agda.Builtin.Int using (negsuc) 
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using (show)
open import Function using (_$_; _∘_; case_of_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Effect.Monad.Indexed
open import Effect.Monad.State.Indexed
open RawIMonadState {{...}} renaming (_⊛_ to _<*>_)
open import Effect.Monad.Identity as Ident using (Identity; mkIdentity)

open import Code
open import Javalette.AST using (Type; ident; RelOp) renaming (Ident to Id); open Type
open import TypedSyntax Id hiding (+)

module CompileIndexed where

private
  variable
    n : ℕ
    v  : List Type 
    v' : List Type 
    w  : List Type 

BlockList : Block → Set
BlockList Δ = TList (λ (id , t) → Ptr t) Δ

CtxList : Ctx → Set
CtxList Γ = TList BlockList  Γ 

SymTab : SymbolTab → Set
SymTab Σ = TList (λ (id , (ts , t)) → Ptr (fun t ts)) Σ

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
    block   : Block'

open CMState

initState : GlobalState → CMState ([] ∷ [])
initState glob = cMS glob 0 0 0 ([] ∷ []) []


CM : (Γ Γ' : Ctx) → Set → Set
CM = IStateT CMState Identity

instance
  CMMonad : RawIMonadState CMState CM
  CMMonad = StateTIMonadState CMState Ident.monad

runCM : CM Γ Γ' A → CMState Γ → (A × CMState Γ')
runCM m s = Ident.runIdentity (m s)


negOne : Num T → toSet T
negOne NumInt    = negsuc 0 -- -1
negOne NumDouble = -1.0

lookupPtr' : BlockList Δ → (id , t) ∈ Δ → Ptr t
lookupPtr' (x ∷ b) (here refl) = x
lookupPtr' (_ ∷ b) (there x)   = lookupPtr' b x

lookupPtr : CtxList Γ → (id , t) ∈' Γ → Ptr t
lookupPtr (x ∷ xs) (here p)  = lookupPtr' x p
lookupPtr (x ∷ xs) (there s) = lookupPtr xs s

getPtr : (id , T) ∈' Γ → CM Γ Γ (Ptr T)
getPtr p = do ctx ← ctxList <$> get
              pure (lookupPtr ctx p)

-- not sure if functions are Ptr
lookupFun : SymTab Σ → (id , Ts , T) ∈ Σ → Ptr (fun T Ts)
lookupFun (x ∷ _)  (here refl) = x
lookupFun (_ ∷ xs) (there p)   = lookupFun xs p


emit : Instruction T → CM Γ Γ ⊤
emit x = modify (λ s → record s {block = x ∷ block s })

emitTmp : Instruction T → CM Γ Γ (Operand T)
emitTmp x = do tmp ← tmpC <$> get 
               let operand = local (ident $ "t" ++s show tmp)
               modify λ s → record s { block = operand := x ∷ block s
                                     ; tmpC = suc (tmpC s)}
               pure operand

allocate : (T : Type) → CM Γ Γ (Ptr T)
allocate t = do v ← varC <$> get
                let p = ident $ "v" ++s show v
                modify λ s → record s { block = local p := alloc t ∷ block s
                                      ; varC = suc (varC s)}
                pure (ptr p)

addVar : (T : Type) → (id ∉ Δ) → CM (Δ ∷ Γ) (((id , T) ∷ Δ) ∷ Γ) (Ptr T)
addVar t p = do p ← allocate t
                modify (addVar' p)
                pure p
  where addVar' : Ptr T → CMState (Δ ∷ Γ) → CMState (((id , T) ∷ Δ) ∷ Γ)
        addVar' x (cMS g v t l (     δ  ∷ γ) block₁) =
                   cMS g v t l ((x ∷ δ) ∷ γ) block₁ 


inNewBlock : CM ([] ∷ Γ) (Γ' ) A → CM Γ Γ A
inNewBlock m (cMS g v t l ctx b) =
  let (mkIdentity (x , cMS g' v' t' l' _   b')) = m (cMS g v t l ([] ∷ ctx) b)
  in   mkIdentity (x , cMS g' v' t' l' ctx b')

newLabel : CM Γ Γ Label
newLabel = do l ← labelC <$> get 
              modify λ s → record s {labelC = suc (labelC s)}
              pure $ ident ("L" ++s show l)

putLabel : Label → CM Γ Γ ⊤
putLabel l = modify λ s → record s {block = label l ∷ block s}

-- Used for lazy evaluation of ||, &&.
-- Should be removed during simplification
curentLabel : CM Γ Γ Label
curentLabel = do l ← newLabel
                 emit (jmp l)
                 putLabel l
                 pure l


module _ (σ : SymTab Σ) where
  open Typed 
  open Valid 

  compileExp : (e : Exp Σ Γ T) → CM Γ Γ (Operand T) 
  compileExp (EValue x) = pure (const x)
  compileExp (EId id x) = emitTmp =<< load <$> getPtr x
  compileExp (EArith p x op y) = emitTmp =<< arith p op  <$> compileExp x <*> compileExp y
  compileExp (EMod     x    y) = emitTmp =<< srem        <$> compileExp x <*> compileExp y
  compileExp (EOrd   p x op y) = emitTmp =<< cmp     op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { <  → RelOp.lTH ; <= → RelOp.lE
                             ; >  → RelOp.gTH ; >= → RelOp.gE }
  compileExp (EEq    p x op y) = emitTmp =<< cmp     op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { == → RelOp.eQU ; != → RelOp.nE }

  compileExp (ELogic x op y) = do cur ← curentLabel
                                  mid ← newLabel
                                  end ← newLabel

                                  x' ← compileExp x
                                  case op of λ { && → emit (branch x' mid end)
                                               ; || → emit (branch x' end mid)}

                                  putLabel mid
                                  y' ← compileExp y
                                  emit (jmp end)

                                  putLabel end
                                  emitTmp (phi ((x' , cur) ∷ (y' , mid) ∷ []))

  compileExp (ENeg p e) = do e' ← compileExp e
                             emitTmp (arith p ArithOp.* e' (const (negOne p)))
  compileExp (ENot e) = {!!}
  compileExp (EStr x) = do c ← globalC ∘ globalS <$> get
                           let id = ident ("str" ++s show c)
                           gS c strs ← globalS <$> get
                           modify λ s → record s {globalS = gS (suc c) ((id , fromList x) ∷ strs)}
                           pure (global id)
  compileExp (EAPP id es p) = emitTmp =<< call (lookupFun σ p) <$> mapCompileExp es
    where mapCompileExp : TList (Exp Σ Γ) Ts → CM Γ Γ (TList Operand Ts)
          mapCompileExp [] = pure []
          mapCompileExp (x ∷ xs) = _∷_ <$> compileExp x <*> mapCompileExp xs

  compileStm  : (s  : Stm  T Σ Γ) → CM Γ (nextCtx T Σ s)  ⊤
  compileStms : (ss : Stms T Σ Γ) → CM Γ (lastCtx T Σ ss) ⊤
  compileStm (SExp x) = ignore (compileExp x)
  compileStm (SDecl t id x p) = emit =<< store     (const x)    <$> addVar t p
  compileStm (SAss id e x)    = emit =<< store <$> compileExp e <*> getPtr x
  compileStm (SWhile x ss) = do preCond ← newLabel
                                loop    ← newLabel
                                end     ← newLabel

                                putLabel preCond
                                x' ← compileExp x
                                emit (branch x' loop end)

                                putLabel loop
                                inNewBlock $ compileStms ss
                                emit (jmp preCond) 
                                putLabel end 
  compileStm (SBlock x) = inNewBlock (compileStms x)
  compileStm (SIfElse x t f) = do true  ← newLabel
                                  false ← newLabel
                                  end   ← newLabel

                                  x' ← compileExp x
                                  emit (branch x' true false)
                                  putLabel true ; inNewBlock $ compileStms t; emit (jmp end)
                                  putLabel false; inNewBlock $ compileStms f; emit (jmp end)
                                  putLabel end
  compileStm (SReturn vRet)    = emit (ret vRet)
  compileStm (SReturn (Ret x)) = do x' ← compileExp x
                                    emit (ret (Ret x'))

  compileStms SEmpty       = pure tt
  compileStms (s SCons ss) = compileStm  s >> compileStms ss


  compileFun : GlobalState → Def Σ Ts T → (FunDef Σ Ts T × GlobalState)
  compileFun glob def = map₂ globalS (runCM compileBody (initState glob))
    where open Def def
          initBlock : Unique Δ → CM ([] ∷ []) (Δ ∷ []) ⊤
          initBlock  []       = pure tt
          initBlock (_∷_ {id} x p) = do initBlock p
                                        v ← addVar _ x
                                        emit $ store (local id) v

          compileBody : CM ([] ∷ []) (lastCtx _ _ body) (FunDef _ _ _)
          compileBody = do putLabel (ident "entry")
                           initBlock unique
                           compileStms body
                           body ← block <$> get
                           pure (record { idents = idents
                                        ; body = body
                                        ; voidparam = voidparam
                                        ; uniqueParams = unique })

  compileFuns : {Σ' : SymbolTab} → FunList Σ Σ' → GlobalState → (FunList' Σ Σ' × GlobalState)
  compileFuns []           g = [] , g
  compileFuns (def ∷ defs) g = let defs' , g'  = compileFuns defs g
                                   def'  , g'' = compileFun g' def
                               in  def' ∷ defs' , g''


compileProgram : Program → llvmProgram
compileProgram p = let defs , globState = compileFuns (mkSymTab uniqueDefs) hasDefs (gS 0 [])
                   in record
                     { BuiltIn = BuiltIn
                     ; Defs = Defs
                     ; strings = strings globState
                     ; hasDefs = defs
                     ; uniqueDefs = uniqueDefs
                     }
  where open Program p
        mkSymTab : Unique Σ → SymTab Σ
        mkSymTab [] = []
        mkSymTab (_∷_ {id} _ xs) = (ptr id) ∷ mkSymTab xs
