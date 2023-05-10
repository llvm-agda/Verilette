
module TypeCheckerMonad where

open import Agda.Primitive using (lzero)
open import Data.String using (String; _≟_; _++_ )

open import Effect.Monad
open import Effect.Choice

open import Data.Sum.Effectful.Left renaming (monad to monadSum; choice to choiceSum)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)


-- | Type checker monad
TCM : Set → Set
TCM = String ⊎_

open RawMonad  {{...}} public renaming (zip to zipM)
open RawChoice {{...}} public

instance
  monadTCM : {A : Set} → RawMonad (A ⊎_)
  monadTCM {a} = monadSum a lzero

  alternativeTCM : RawChoice TCM
  alternativeTCM = choiceSum _ lzero

error : {A : Set} → String → TCM A
error = inj₁
