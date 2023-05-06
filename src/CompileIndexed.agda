open import Data.Product using (_×_; _,_; ∃; map₂) renaming (proj₁ to fst; proj₂ to snd)
open import Data.List using (List; _∷_ ; []; map)
open import Data.List.Relation.Unary.All using (All); open All

open import Data.String using (String; fromList; unwords; unlines; intersperse; _++_; length)
open import Agda.Builtin.Int using (negsuc) renaming (primShowInteger to showℤ)
open import Data.Float using () renaming (show to showℝ)
import Data.Bool as Bool
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
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
open import TypedSyntax Id

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
    block   : Code

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
emitTmp {void} x = do modify λ s → record s {block = x ∷ block s}
                      pure (local (ident "This_void_tmp_should_never_be_used"))
emitTmp {T} x = do tmp ← tmpC <$> get
                   let operand = local (ident $ "t" ++ showℕ tmp)
                   modify λ s → record s { block = operand := x ∷ block s
                                         ; tmpC = suc (tmpC s)}
                   pure operand

allocate : (T : Type) → CM Γ Γ (Ptr T)
allocate t = do v ← varC <$> get
                let p = ident $ "v" ++ showℕ v
                modify λ s → record s { block = local p := alloc t ∷ block s
                                      ; varC = suc (varC s)}
                pure (local p)

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
              pure $ ident ("L" ++ showℕ l)

putLabel : Label → CM Γ Γ ⊤
putLabel l = modify λ s → record s {block = label l ∷ block s}

-- Used for lazy evaluation of ||, &&.
-- Should be removed during simplification
curentLabel : CM Γ Γ Label
curentLabel = do l ← newLabel
                 emit (jmp l)
                 putLabel l
                 pure l


-- Compilation using a given SymTab σ
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

  compileExp (ENeg p e) = do e' ← compileExp e
                             emitTmp (arith p ArithOp.* e' (const (negOne p)))
  compileExp (ENot e) = emitTmp =<< cmp RelOp.eQU (const Bool.false) <$> compileExp e
  compileExp (EStr x) = do gS c strs ← globalS <$> get
                           let id = ident ("str" ++ showℕ c)
                           let gs = gS (suc c) ((id , fromList x) ∷ strs)
                           modify λ s → record s {globalS = gs}
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

                                emit (jmp preCond)
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
                     ; Strings = strings globState
                     ; hasDefs = defs
                     ; uniqueDefs = uniqueDefs
                     }
  where open Program p
        mkSymTab : Unique Σ → SymTab Σ
        mkSymTab [] = []
        mkSymTab (_∷_ {id} _ xs) = (global id) ∷ mkSymTab xs



-- printing llvm code
module _ where

  pType : Type → String
  pType int  = "i32"
  pType doub = "double"
  pType bool = "i1"
  pType void = "void"
  pType (fun t ts) = pType t ++ " (" ++ pList ts ++ ")"
    where pList : List Type → String
          pList [] = ""
          pList (x ∷ []) = pType x
          pList (y ∷ x ∷ xs) = pType y ++ ", " ++ pList (x ∷ xs)

  pOperand : Operand T → String
  pOperand {T} (const x) with T
  ... | int  = showℤ x
  ... | doub = showℝ x
  ... | bool with x
  ... | Bool.false = "false"
  ... | Bool.true  = "true"
  pOperand {_} (local  (ident x)) = "%" ++ x
  pOperand {_} (global (ident x)) = "@" ++ x

  pPairOperand : (x y : Operand T) → String
  pPairOperand x y = pOperand x ++ " , " ++ pOperand y

  pPtr' : Ptr T → String
  pPtr' (local  (ident x)) = "%" ++ x
  pPtr' (global (ident x)) = "@" ++ x

  pPtr : Ptr T → String
  pPtr {T} x = pType T ++ "* " ++ pPtr' x 

  pLabel : Label → String
  pLabel (ident x) = "label %" ++ x

  -- Helper functions for pInst
  private
    pArith : Num T → ArithOp → String
    pArith NumInt    = λ { + →  "add"; - →  "sub"; * →  "mul"; / → "sdiv"}
    pArith NumDouble = λ { + → "fadd"; - → "fsub"; * → "fmul"; / → "fdiv"}

    open RelOp
    pCmp : Type → RelOp → String
    pCmp int  = ("icmp " ++_) ∘ λ { lTH → "slt"; lE → "sle"; gTH → "sgt"; gE → "sge"; eQU →  "eq"; nE →  "ne"}
    pCmp bool = ("icmp " ++_) ∘ λ { lTH → "slt"; lE → "sle"; gTH → "sgt"; gE → "sge"; eQU →  "eq"; nE →  "ne"}
    pCmp doub = ("fcmp " ++_) ∘ λ { lTH → "ult"; lE → "ule"; gTH → "ugt"; gE → "uge"; eQU → "ueq"; nE → "une"}
    pCmp void      = λ _ → "error: can not compare void"
    pCmp (fun _ _) = λ _ → "error: can not compare function"

    pCall : All Operand Ts → String
    pCall (_∷_ {t} y (x ∷ xs)) = pType t ++ " " ++ pOperand y ++ ", " ++ pCall (x ∷ xs)
    pCall (_∷_ {t} x [])       = pType t ++ " " ++ pOperand x
    pCall [] = ""

    pPhi : List (Operand T × Id) → List String
    pPhi = map λ {(x , ident l) → "[ " ++ pOperand x ++ ", %" ++ l ++ " ]"}


  pInst : Instruction T → String
  pInst {T} x with pT ← pType T | x
  ... | arith p op x y = unwords $ pArith p op ∷ pT      ∷ pPairOperand x y ∷ []
  ... | cmp {t} op x y = unwords $ pCmp t op   ∷ pType t ∷ pPairOperand x y ∷ []
  ... | srem x y       = unwords $ "srem"      ∷ pT      ∷ pPairOperand x y ∷ []
  ... | alloc t   = unwords $ "alloca" ∷ pT ∷ []
  ... | load x    = unwords $ "load"   ∷ pT ∷ "," ∷ pPtr x ∷ []
  ... | store o p = unwords $ "store"  ∷ pT ∷ pOperand o ∷ "," ∷ pPtr p ∷ []
  ... | call (global (ident "printString")) (x ∷ []) = "call void @printString( i8* " ++ pOperand x ++ ")"
  ... | call x xs = unwords $ "call"   ∷ pT ∷ ( pPtr' x ++ "(" ) ∷ pCall xs ∷ ")" ∷ []
  ... | phi x     = unwords $ "phi"    ∷ pT ∷ intersperse ", " (pPhi x) ∷ []
  ... | jmp x = unwords $ "br" ∷ pLabel x ∷ []
  ... | branch x t f =  unwords $ "br" ∷ "i1" ∷ pOperand x ∷ "," ∷ pLabel t ∷ "," ∷ pLabel f ∷ []
  ... | ret vRet    = unwords $ "ret"  ∷ "void" ∷ []
  ... | ret (Ret x) = unwords $ "ret"  ∷ pT ∷ pOperand x ∷ []
  ... | label (ident x) = "error: lables should have been handled in pCode" -- x ++ ":"

  -- Should maybe reverse the order of code when compiling
  pCode : Code → String
  pCode [] = ""
  pCode (label (ident l) ∷ xs) = pCode xs ++ l ++ ": \n"
  pCode (x ∷ xs)      = pCode xs ++ "  " ++                        pInst x ++ "\n"
  pCode (o := x ∷ xs) = pCode xs ++ "  " ++ pOperand o ++ " = " ++ pInst x ++ "\n"

  pFun : Id → FunDef Σ Ts T → String
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
