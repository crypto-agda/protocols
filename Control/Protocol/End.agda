{-# OPTIONS --without-K #-}
open import Type
open import Level.NP
open import Data.One using (𝟙)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; refl)
open import Function.Extensionality
open import HoTT
open Equivalences

module Control.Protocol.End where

record End_ ℓ : ★_ ℓ where
  constructor end

End : ∀ {ℓ} → ★_ ℓ
End = End_ _

End-equiv : End ≃ 𝟙
End-equiv = equiv {₀} _ _ (λ _ → refl) (λ _ → refl)

End-uniq : {{_ : UA}} → End ≡ 𝟙
End-uniq = ua End-equiv
