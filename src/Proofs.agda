
module Proofs where

open import Data.List.Relation.Unary.All using (All); open All
open import Data.List using ([]; _∷_)

open import Javalette.AST using (Type); open Type
open import TypedSyntax 


--------------------------------------------------------------------------------
-- Statements

module StmProofs (Σ : SymbolTab) (T : Type) where
  open Valid Σ

  -- Proof that condition holds for all statements in a sequence
  data Allways {Γ} (P : ∀ {Γ'} → Stm T Γ' → Set) : Stms T Γ → Set where
    SEmpty  : Allways P SEmpty
    _SCons_ : ∀ {s ss} → P s → Allways P ss → Allways P (s SCons ss)


  uniqueNextCtx : (s : Stm T Γ) → All Unique Γ → All Unique (nextCtx s)
  uniqueNextCtx (SDecl _ _ _ p') (px ∷ p) = (uniqueSuc p' px) ∷ p
  uniqueNextCtx (SExp _)        p = p
  uniqueNextCtx (SAss _ _ _)    p = p
  uniqueNextCtx (SWhile _ _)    p = p
  uniqueNextCtx (SBlock _)      p = p
  uniqueNextCtx (SIfElse _ _ _) p = p
  uniqueNextCtx (SReturn _)     p = p
  uniqueNextCtx  VReturn        p = p

    
  UniqueCtx : ∀ {Γ} → (ss : Stm T Γ) → Set 
  UniqueCtx {Γ} ss = All Unique Γ

  allwaysUniqueCtx : (ss : Stms T Γ) → All Unique Γ → Allways UniqueCtx ss
  allwaysUniqueCtx SEmpty x       = SEmpty
  allwaysUniqueCtx (s SCons ss) x = x SCons (allwaysUniqueCtx ss (uniqueNextCtx s x))

  allwaysUniqueCtx' : ∀ {Δ} → (ss : Stms T (Δ ∷ [])) → Unique Δ → Allways UniqueCtx ss
  allwaysUniqueCtx' ss x = allwaysUniqueCtx ss (x ∷ [])



--------------------------------------------------------------------------------
-- Funs

module FunProofs (Σ : SymbolTab) (T : Type) where
  open StmProofs Σ T
  open Def 

  allwaysUniqueΓFun : (F : Def Σ ts T) → Allways UniqueCtx (body F)
  allwaysUniqueΓFun F = allwaysUniqueCtx' (body F) (unique F)
