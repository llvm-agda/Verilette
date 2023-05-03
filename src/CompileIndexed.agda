open import Data.Product using (_×_; _,_; ∃) renaming (proj₁ to fst; proj₂ to snd)
open import Data.List using (List; _∷_ ; []; _++_; length)
open import Data.List.Relation.Unary.All using (All; map); open All

open import Data.String using (String; fromList) renaming (_++_ to _++s_)
open import Agda.Builtin.Int using (negsuc) 
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using (show)
open import Function using (_$_; case_of_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_; cong)
open import Data.List.Relation.Unary.All using (All); open All
open import Data.List.Relation.Unary.Any using (Any); open Any

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Effect.Monad.Indexed
open import Effect.Monad.State.Indexed
open import Effect.Monad.Identity using (Identity; mkIdentity) renaming (monad to IdMonad)

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

record CMState (Σ : SymbolTab) (Γ : Ctx) : Set where
  constructor cMS
  field 
    varC tmpC labelC globalC : ℕ
    symTab  : SymTab Σ
    ctxList : CtxList Γ
    strings : List (Id × String)
    block   : Block'

open CMState

CM : SymbolTab → (Γ Γ' : Ctx) → Set → Set
CM Σ = IStateT (CMState Σ) Identity

open RawIMonadState {{...}} renaming (_⊛_ to _<*>_)

instance
  CMMonad : {Σ : SymbolTab} → RawIMonadState (CMState Σ) (CM Σ)
  CMMonad {Σ} = StateTIMonadState (CMState Σ) IdMonad

negOne : Num T → toSet T
negOne NumInt    = negsuc 0 -- -1
negOne NumDouble = -1.0

lookupPtr' : BlockList Δ → (id , t) ∈ Δ → Ptr t
lookupPtr' (x ∷ b) (here refl) = x
lookupPtr' (_ ∷ b) (there x)   = lookupPtr' b x

lookupPtr : CtxList Γ → (id , t) ∈' Γ → Ptr t
lookupPtr (x ∷ xs) (here p)  = lookupPtr' x p
lookupPtr (x ∷ xs) (there s) = lookupPtr xs s

getPtr : (id , T) ∈' Γ → CM Σ Γ Γ (Ptr T)
getPtr p = do ctx ← ctxList <$> get
              pure (lookupPtr ctx p)


-- not sure if functions are Ptr
lookupFun : SymTab Σ → (id , Ts , T) ∈ Σ → Ptr (fun T Ts)
lookupFun (x ∷ _)  (here refl) = x
lookupFun (_ ∷ xs) (there p)   = lookupFun xs p



emit : Instruction T → CM Σ Γ Γ ⊤
emit x = modify (λ s → record s {block = x ∷ block s })

emitTmp : Instruction T → CM Σ Γ Γ (Operand T)
emitTmp x = do tmp ← tmpC <$> get 
               let operand = local (ident $ "t" ++s show tmp)
               modify λ s → record s {tmpC = suc (tmpC s)
                                     ;block = operand := x ∷ block s}
               pure operand

allocate : (T : Type) → CM Σ Γ Γ (Ptr T)
allocate t = do v ← varC <$> get
                let p = ident $ "v" ++s show v
                modify λ s → record s { block = local p := alloc t ∷ block s
                                      ; varC = suc (varC s)}
                pure (ptr p)

addVar : (T : Type) → (id : Id) → Ptr T → CM Σ (Δ ∷ Γ) (((id , T) ∷ Δ) ∷ Γ) ⊤
addVar T id x (cMS v t l g σ (δ ∷ γ) strings block₁) =
  let s = cMS v t l g σ ((x ∷ δ) ∷ γ) strings block₁ in
  mkIdentity (tt , s)

inNewBlock : CM Σ ([] ∷ Γ) (Γ' ) A → CM Σ Γ Γ A
inNewBlock m (cMS v t l g σ ctx s b) =
  let (mkIdentity (x , cMS v' t' l' g' σ' _ s' b')) = m (cMS v t l g σ ([] ∷ ctx) s b)
  in  mkIdentity (x , (cMS v' t' l' g' σ' ctx s' b'))

newLabel : CM Σ Γ Γ Label
newLabel = do l ← labelC <$> get 
              modify λ s → record s {labelC = suc (labelC s)}
              pure $ ident ("L" ++s show l)

putLabel : Label → CM Σ Γ Γ ⊤
putLabel l = modify λ s → record s {block = label l ∷ block s}

module _ where
  open Typed 

  compileExp : (e : Exp Σ Γ T) → CM Σ Γ Γ (Operand T) 
  compileExp (EValue x) = pure (const x)
  compileExp (EId id x) = emitTmp =<< load <$> getPtr x
  compileExp (EArith p x op y) = emitTmp =<< arith p op  <$> compileExp x <*> compileExp y
  compileExp (EMod     x    y) = emitTmp =<< srem        <$> compileExp x <*> compileExp y
  compileExp (EOrd   p x op y) = emitTmp =<< cmp     op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { <  → RelOp.lTH ; <= → RelOp.lE
                             ; >  → RelOp.gTH ; >= → RelOp.gE }
  compileExp (EEq    p x op y) = emitTmp =<< cmp     op' <$> compileExp x <*> compileExp y
    where op' = case op of λ { == → RelOp.eQU ; != → RelOp.nE }
  compileExp (ELogic x op y) = do mid ← newLabel
                                  end ← newLabel
                                  x' ← compileExp x
                                  res ← allocate bool
                                  emit (store x' res)
                                  case op of λ { && → emit (branch x' mid end)
                                               ; || → emit (branch x' end mid)}

                                  putLabel mid
                                  y' ← compileExp y
                                  emit (store y' res)
                                  emit (jmp end)

                                  putLabel end
                                  emitTmp (load res)
  compileExp (ENeg p e) = do e' ← compileExp e
                             emitTmp (arith p ArithOp.+ e' (const (negOne p)))
  compileExp (ENot e) = {!!}
  compileExp (EStr x) = do c ← globalC <$> get
                           let id = ident ("str" ++s show c)
                           modify λ s → record s { globalC = suc (globalC s)
                                                 ; strings = (id , fromList x) ∷ strings s}
                           pure (global id)
  compileExp (EAPP id es p) = do sym ← symTab <$> get
                                 emitTmp =<< call (lookupFun sym p) <$> mapCompileExp es
    where mapCompileExp : TList (Exp Σ Γ) Ts → CM Σ Γ Γ (TList Operand Ts)
          mapCompileExp [] = pure []
          mapCompileExp (x ∷ xs) = _∷_ <$> compileExp x <*> mapCompileExp xs


module _ (T : Type) where
  open Valid T 

  compileStm  : (s  : Stm  Σ Γ) → CM Σ Γ (nextCtx Σ s)  ⊤
  compileStms : (ss : Stms Σ Γ) → CM Σ Γ (lastCtx Σ ss) ⊤
  compileStm (SExp x) = do compileExp x
                           pure tt
  compileStm (SDecl t id x x₁) = do v ← allocate t
                                    emit (store (const x) v)
                                    addVar t id v
  compileStm (SAss id e x) = do p ← getPtr x
                                e' ← compileExp e
                                emit (store e' p) 
  compileStm (SWhile x ss) = do preCond ← newLabel
                                loop ← newLabel
                                end ← newLabel

                                putLabel preCond
                                x' ← compileExp x
                                emit (branch x' loop end)

                                putLabel loop
                                inNewBlock $ compileStms ss
                                emit (jmp preCond) 
                                putLabel end 
  compileStm (SBlock x) = inNewBlock (compileStms x)
  compileStm (SIfElse x t f) = do true ← newLabel
                                  false ← newLabel
                                  end ← newLabel

                                  x' ← compileExp x
                                  emit (branch x' true false)
                                  putLabel true
                                  inNewBlock $ compileStms t
                                  emit (jmp end)
                                  putLabel false
                                  inNewBlock $ compileStms f
                                  emit (jmp end)
                                  putLabel end
  compileStm (SReturn vRet)    = emit (ret vRet)
  compileStm (SReturn (Ret x)) = do x' ← compileExp x
                                    emit (ret (Ret x'))

  compileStms SEmpty       = pure tt
  compileStms (s SCons ss) = do compileStm  s
                                compileStms ss


compileFun : (globalC : ℕ) → Def Σ Ts T → FunDef Σ Ts T
compileFun c record { idents = idents
                    ; body = body
                    ; voidparam = voidparam
                    ; unique = unique
                    ; return = return } = {!!}

