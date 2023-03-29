
module TypeCheckerMonad where

open import Agda.Primitive using (lzero)
open import Data.String using (String; _≟_; _++_ )

open import Effect.Monad

open import Data.Sum.Effectful.Left renaming (monad to monadSum)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)


-- | Type checker monad
TCM : Set → Set
TCM = String ⊎_

open RawMonad {{...}} public hiding (zip)
instance
  monadTCM : {A : Set} → RawMonad (A ⊎_)
  monadTCM {a} = monadSum a lzero

error : {A : Set} → String → TCM A
error = inj₁
