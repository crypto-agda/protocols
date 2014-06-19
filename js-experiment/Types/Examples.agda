open import runningtest
open import Types String String


module Types.Examples (d : String) where

  S≈S : String ≃? String
  S≈S = record { serialize = λ x → x ; parse = succeed ; linv = λ x → succeed refl ; rinv = λ _ → refl }

  cater-Proto : Proto
  cater-Proto = recv λ _ →
                recv λ _ →
                send λ _ →
                end

  Δ : Env
  Δ = ε , d ↦ cater-Proto

  prf : ∀ {s₀ s₁} → Δ ⊢ᶜ (cater-client d s₀ s₁)
  prf = output here here (output here here (input here (λ m p → end)))
