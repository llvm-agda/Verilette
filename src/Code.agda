open import Javalette.AST using (Type; String) renaming (Ident to Id)
open import Data.List using (List; _∷_ ; [] ; zip ; _++_)
open import TypedSyntax

Label = Id
Labels = List Label

data Instruction : Set where
module Body (T : Type) where

  data TermInstruction (ℓ : Labels) : Set where
    ret    : TermInstruction ℓ
    branch : (l : Label) → (l ∈ ℓ) → TermInstruction ℓ

  record BasicBlock (ℓ : Labels) : Set where
    field
      termInstruction : TermInstruction ℓ

-- record Def (Σ : SymbolTab) (ts : List Type) (T : Type) : Set  where
--   field
--     idents : List Id

--   params = zip idents ts

--   field
--     body      : Stms Σ T (params ∷ [])
--     voidparam : All (_≢ void) ts
--     unique    : Unique params
--     return    : returnStms body



-- record Program : Set where
--   field
--     BuiltIn : SymbolTab
--     Defs    : SymbolTab
--   Σ' = BuiltIn ++ Defs

--   field
--     hasMain    : (Id.ident "main" , ([] , int)) ∈ Σ'
--     hasDefs    : FunList Σ' Defs
--     uniqueDefs : Unique Σ'
