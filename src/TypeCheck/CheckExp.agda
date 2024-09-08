open import Agda.Builtin.Equality using (refl; _≡_)
open import Relation.Binary.PropositionalEquality using (_≢_; ≡-≟-identity; sym)
open import Data.String using (_≟_) renaming (_++_ to _++s_)

open import Function using (_$_; _∘_)

open import Data.Product using (_×_; _,_; ∃; proj₂)
open import Data.List using (List; _∷_; []; zip; _++_; reverse; [_]; foldr) renaming (_ʳ++_ to _++r_; _∷ʳ_ to _∷r_)
open import Data.List.Relation.Unary.All using (All; reduce); open All
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise); open Pointwise

open import Agda.Builtin.Bool using (true; false)


open import TypeCheck.Monad
open import TypeCheck.Util
open import Javalette.AST

open import TypedSyntax as TS using (TypeTab;
                                     _∈'_; _∈_; _∉_;
                                     Num; Eq; Ord; Return; toSet; NonVoid;
                                     T; Ts)
open import WellTyped


module TypeCheck.CheckExp (Σ : SymbolTab) (χ : TypeTab) where

open Expression Σ χ


module CheckExp (Γ : Ctx) where

  pattern _:::_ e t = t , e

  -- If an expression typechecks it is well typed (in our type semantics) -- Soundness
  checkExp : (t : Type) → (e : Expr) → TCM (Γ ⊢ e ∶ t)

  infer     : (e  :      Expr) → TCM (∃ (Γ ⊢ e ∶_))
  inferList : (es : List Expr) → TCM (∃ (Pointwise (Γ ⊢_∶_) es) )
  inferList [] = pure ([] ::: [])
  inferList (e ∷ es) = do e'  ::: t  ← infer e
                          es' ::: ts ← inferList es
                          pure ((e' ∷ es') ::: (t ∷ ts))

  inferPair : (x y : Expr) → TCM (∃ (λ t → (Γ ⊢ x ∶ t) × (Γ ⊢ y ∶ t) ))
  inferPair x y = do x' ::: t1 ← infer x
                     y' ::: t2 ← infer y
                     refl ← t1 =?= t2
                     pure ((x' , y') ::: t1)

  infer (eVar x)  = do t , p ← lookupCtx x Γ
                       pure (eVar x p ::: t)
  infer (eLitInt x ) = pure (eLitInt  x ::: int)
  infer (eLitDoub x) = pure (eLitDoub x ::: doub)
  infer (eLitTrue  ) = pure (eLitTrue   ::: bool)
  infer (eLitFalse ) = pure (eLitFalse  ::: bool)
  infer (eString x)  = error "Encountered string outside of printString"
  infer (eNull (eVar x)) = do t , p ← lookupTCM x χ
                              pure (eNull p ::: structT x)
  infer (eNull _) = error "Error; eNull should take a struct type as argument"
  infer (eIndex e i) = do i' ← checkExp int i
                          e' ::: array t ← infer e
                            where e' ::: _ → error "Tried to index non array expression"
                          pure (eIndex e' i' ::: t)
  infer (eNew t []) with t
  ... | structT c = do inList n fs p ← lookupConstructor c χ
                       pure (eStruct p ::: structT n)
  ... | t = error "Tried to make a new array without size"
  infer (eNew t (n ∷ ns)) = do b ← ifBasic χ t
                               ns' ← inferNew (n ∷ ns)
                               pure (eArray b ns' ::: _)
        where inferNew : (nss : List ArrDecl) → TCM (All (Γ ⊢_∶ int ∘ deLen) nss)
              inferNew []                 = pure []
              inferNew (arraySize e ∷ es) = _∷_ <$> checkExp int e <*> inferNew es

  infer (eAttrib e (ident "length")) = do e' ::: array t  ← infer e
                                             where e' ::: _ → error "Only arrays have length attribute"
                                          pure (eLength e' ::: int)
  infer (eAttrib e (ident x₁)) = error $ "Found non-legal attribute: " ++s x₁
  infer (eDeRef e x) = do e' ::: structT n ← infer e
                             where e' ::: _ → error "Tried to deref non-struct"
                          (c , fs) , p ← lookupTCM n χ
                          t , p' ← lookupTCM x fs
                          pure (eDeRef e' p p' ::: t)
  infer (neg e) = do e' ::: t ← infer e
                     p ← ifNum t
                     pure (neg p e' ::: t)
  infer (not e) = do e' ← checkExp bool e
                     pure (not e' ::: bool)
  infer (eMul x op y) with inferPair x y
  ...   | inj₁ s = error s
  ...   | inj₂ ((x' , y') ::: t) with op
  ...     | times = ifNum   t >>= λ  p    → pure (eMul p x' y' ::: t)
  ...     | div   = ifNum   t >>= λ  p    → pure (eDiv p x' y' ::: t)
  ...     | mod   = int =?= t >>= λ {refl → pure (eMod   x' y' ::: t)}
  infer (eAdd x op y) = do (x' , y') ::: t ← inferPair x y
                           p ← ifNum t
                           pure (eAdd p op x' y' ::: t)

  infer (eRel x op y) with inferPair x y
  ... | inj₁ s = error s
  ... | inj₂ ((x' , y') ::: t) with op
  ...      | lTH = ifOrd t >>= λ p → pure (eOrd lTH p x' y' ::: bool)
  ...      | lE  = ifOrd t >>= λ p → pure (eOrd lE  p x' y' ::: bool)
  ...      | gTH = ifOrd t >>= λ p → pure (eOrd gTH p x' y' ::: bool)
  ...      | gE  = ifOrd t >>= λ p → pure (eOrd gE  p x' y' ::: bool)
  ...      | eQU = ifEq  t >>= λ p → pure (eEq  eQU p x' y' ::: bool)
  ...      | nE  = ifEq  t >>= λ p → pure (eEq  nE  p x' y' ::: bool)
  infer (eAnd x y) = do (x' , y') ::: bool ← inferPair x y
                            where _ ::: t → error "non-bool expression found in and"
                        pure (eAnd x' y' ::: bool)
  infer (eOr x y)  = do (x' , y') ::: bool ← inferPair x y
                            where _ ::: t → error "non-bool expression found in or"
                        pure (eOr  x' y' ::: bool)
  infer (eApp (ident "printString") (eString s ∷ [])) = pure (ePrintString s ::: void)
  infer (eApp x es) = do (ts , t) , p ← lookupTCM x Σ
                         es' ::: ts' ← inferList es
                         refl ← eqLists ts ts'
                         pure (eApp x p es' ::: t)

  checkExp t e = do e' ::: t' ← infer e
                    refl ← t =?= t'
                    pure e'


module CheckStatements (T : Type) where
  open Statements Σ χ T
  open Declarations Σ χ

  open CheckExp

  check     : (Γ : Ctx) → (s  :      Stmt) → TCM (∃ (Γ ⊢ s ⇒_))

  checkStms : (Γ : Ctx) → (ss : List Stmt) → TCM (∃ (Γ ⊢ ss ⇒⇒_))
  checkStms Γ [] = pure (_ , [])
  checkStms Γ (s ∷ ss) = do _ , s'  ← check _ s
                            _ , ss' ← checkStms _ ss
                            pure (_ , s' ∷ ss')

  check Γ empty = pure (_ , empty)
  check Γ (bStmt (block ss)) = do _ , ss' ← checkStms ([] ∷ Γ) ss
                                  pure (_ , bStmt ss')

  check Γ (ass (eVar x) e) = do t , p ← lookupCtx x Γ
                                e' ← checkExp Γ t e
                                pure (_ , ass x p e')
  check Γ (ass (eIndex arr i) x) = do i'     ← checkExp Γ int i
                                      t , x' ← infer Γ x
                                      arr'   ← checkExp Γ (array t) arr
                                      pure (_ , assIdx arr' i' x')
  check Γ (ass (eDeRef e f) x) = do e' ::: structT t ← infer Γ e
                                       where e' ::: _ → error "Can not defer field from non-struct type"
                                    (c , fs) , p ← lookupTCM t χ
                                    t' , p' ← lookupTCM f fs
                                    x' ← checkExp Γ t' x
                                    pure (_ , assPtr e' p p' x')
  check Γ (ass _ e) = error "Could not assign to expression"
  check Γ (incr x) = do int , p ← lookupCtx x Γ
                          where _ → error "Can not increment non-int type"
                        pure (_ , incr x p)
  check Γ (decr x) = do int , p ← lookupCtx x Γ
                          where _ → error "Can not decrement non-int type"
                        pure (_ , decr x p)
  check Γ (ret e) = do e' ← checkExp Γ T e
                       pure (_ , ret e')
  check Γ vRet = do refl ← T =?= void
                    pure (_ , vRet refl)
  check Γ (cond e t) = do e' ← checkExp Γ bool e
                          _ , t' ← check ([] ∷ Γ) t
                          pure (_ , cond e' t')
  check Γ (condElse e t f) = do e' ← checkExp Γ bool e
                                _ , t' ← check ([] ∷ Γ) t
                                _ , f' ← check ([] ∷ Γ) f
                                pure (_ , condElse e' t' f')
  check Γ (while e s) = do e' ← checkExp Γ bool e
                           _ , s' ← check ([] ∷ Γ) s
                           pure (_ , while e' s')
  check Γ (for t id e s) = do e' ← checkExp Γ (array t) e
                              _ , s' ← check ([ id , t ] ∷ Γ) s
                              pure (_ , (for id e' s'))
  check Γ (sExp e) = do e' ← checkExp Γ void e
                        pure (_ , sExp e')
  check Γ (decl t is) with Γ
  ... | []    = error "Can not declare variable in empty Ctx"
  ... | Δ ∷ Γ = do p ← ifNonVoid χ t
                   Δ' , is' ← checkIs Δ is
                   pure (_ , decl p is')
    where checkIs : ∀ Δ → (is : List Item) → TCM (∃ (Star' (DeclP t) (Δ ∷ Γ) is))
          checkIs Δ [] = pure (_ , [])
          checkIs Δ (noInit id ∷ is) = do p  ← id notIn Δ
                                          Δ' , ps ← checkIs ((id , t) ∷ Δ) is
                                          pure (_ , noInit p ∷ ps)
          checkIs Δ (init id e ∷ is) = do p , e'  ← zipM (id notIn Δ) (checkExp (Δ ∷ Γ) t e)
                                          Δ' , ps ← checkIs ((id , t) ∷ Δ) is
                                          pure (_ , init p e' ∷ ps)


module _ where

  open Statements Σ χ
  open WellTyped.Return

  checkReturn  : ∀ {ss t} → (ss' : _⊢_⇒⇒_ t Γ ss Γ') → TCM (Returns  ss')
  checkReturn' : ∀ {s  t} → (s'  : _⊢_⇒_  t Γ s  Γ') → TCM (Returns' s')
  checkReturn (s ∷ ss) = here <$> checkReturn' s <|> there <$> checkReturn ss
  checkReturn {Γ = Δ ∷ []} {t = void} [] = pure vEnd
  checkReturn                         [] = error "CheckReturn failed; found no return"

  checkReturn' (condElse x s1 s2) = condElse <$> checkReturn' s1 <*> checkReturn' s2
  checkReturn' (bStmt x)   = bStmt <$> checkReturn x
  checkReturn' (ret _)     = pure ret
  checkReturn' (vRet refl) = pure vRet
  checkReturn' s = error "CheckReturn' failed; found non-returning stmt"
