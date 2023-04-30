open import Data.Product using (_×_; _,_; ∃) renaming (proj₁ to fst; proj₂ to snd)
open import Data.List using (List; _∷_ ; [] ; zip ; map)
open import Data.List.Relation.Unary.All using (All); open All

open import Data.String using (String; _++_)
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
open import Javalette.AST using (Type; ident) renaming (Ident to Id); open Type
open import TypedSyntax Id hiding (+; <) -- Using ℕ as Id

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
    varC tmpC labelC : ℕ
    symTab : SymTab Σ
    ctxList : CtxList Γ
    block : Block'

open CMState

CM : SymbolTab → (Γ Γ' : Ctx) → Set → Set
CM Σ = IStateT (CMState Σ) Identity

open RawIMonadState {{...}}

instance
  CMMonad : {Σ : SymbolTab} → RawIMonadState (CMState Σ) (CM Σ)
  CMMonad {Σ} = StateTIMonadState (CMState Σ) IdMonad

negOne : Num T → toSet T
negOne NumInt    = negsuc 0 -- -1
negOne NumDouble = -1.0

lookupPtr' : BlockList Δ → (id , t) ∈ Δ → Ptr t
lookupPtr' (x :+ b) (here refl) = x
lookupPtr' (_ :+ b) (there x)   = lookupPtr' b x

lookupPtr : CtxList Γ → (id , t) ∈' Γ → Ptr t
lookupPtr (x :+ xs) (here p)  = lookupPtr' x p
lookupPtr (x :+ xs) (there s) = lookupPtr xs s

getPtr : (id , T) ∈' Γ → CM Σ Γ Γ (Ptr T)
getPtr p = do ctx ← ctxList <$> get
              pure (lookupPtr ctx p)


-- not sure if functions are Ptr
lookupFun : SymTab Σ → (id , Ts , T) ∈ Σ → Ptr (fun T Ts)
lookupFun (x :+ _)  (here refl) = x
lookupFun (_ :+ xs) (there p)   = lookupFun xs p



emit : Instruction T → CM Σ Γ Γ ⊤
emit x = do modify (λ s → record s {block = x ∷ block s })
            pure tt

emitTmp : Instruction T → CM Σ Γ Γ (Operand T)
emitTmp x = do tmp ← tmpC <$> get 
               let operand = var (ident $ "t" ++ show tmp)
               modify λ s → record s {tmpC = suc (tmpC s)
                                     ;block = operand := x ∷ block s}
               pure operand

allocate : (T : Type) → CM Σ Γ Γ (Ptr T)
allocate t = do v ← varC <$> get
                let p = ident $ "v" ++ show v
                modify λ s → record s { block = var p := alloc t ∷ block s
                                      ; varC = suc (varC s)}
                pure (ptr p)

addVar : (T : Type) → (id : Id) → Ptr T → CM Σ (Δ ∷ Γ) (((id , T) ∷ Δ) ∷ Γ) ⊤
addVar T id x (cMS varC₁ tmpC₁ labelC₁ σ (δ :+ γ) block₁) =
  let s = cMS varC₁ tmpC₁ labelC₁ σ ((x :+ δ) :+ γ) block₁ in
  mkIdentity (tt , s)

inNewBlock : CM Σ ([] ∷ Γ) (Γ' ) A → CM Σ Γ Γ A
inNewBlock = {!!}

newLabel : CM Σ Γ Γ Label
newLabel = do l ← labelC <$> get 
              modify λ s → record s {labelC = suc (labelC s)}
              pure $ ident ("L" ++ show l)

putLabel : Label → CM Σ Γ Γ ⊤
putLabel l = do modify λ s → record s {block = label l ∷ block s}
                pure tt

module _ where
  open Typed 

  compileExp : (e : Exp Σ Γ T) → CM Σ Γ Γ (Operand T) 
  compileExp (EValue x) = pure (const x)
  compileExp (EId id x) = do p ← getPtr x
                             emitTmp (load p)
  compileExp (EAPP id es p) = do {!!}
  compileExp (EArith p x op y) = do x' ← compileExp x
                                    y' ← compileExp y
                                    emitTmp (arith p op x' y')
  compileExp (EMod e e₁) = {!!}
  compileExp (EOrd x e x₁ e₁) = {!!}
  compileExp (EEq x e x₁ e₁) = {!!}
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
  compileExp (ENeg x e) = {!!}
  compileExp (ENot e) = {!!}
  compileExp (EStr x) = {!!}

  
module _ (T : Type) (σ : SymTab Σ) where
  open Valid T Σ 

  compileStm  : (s  : Stm  Γ) → CM Σ Γ (nextCtx s)  ⊤
  compileStms : (ss : Stms Γ) → CM Σ Γ (lastCtx ss) ⊤
  compileStm (SExp x) = do compileExp x
                           pure tt
  compileStm (SDecl t id x x₁) = do v ← allocate t
                                    emit (store (const x) v)
                                    addVar t id v
                                    pure tt
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
  compileStm (SBlock x) = {!!}
  compileStm (SIfElse x x₁ x₂) = {!!}
  compileStm (SReturn x) = {!!}

  compileStms SEmpty = pure tt
  compileStms (s SCons ss) = do compileStm  s
                                compileStms ss
