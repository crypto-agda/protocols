open import runningtest
open import Types String


module Types.Examples (d : String) where

  ≃-refl : ∀ {X} → X ≃? X
  ≃-refl = record { serialize = λ x → x ; parse = succeed ; linv = λ x → succeed refl ; rinv = λ _ → refl }

  adder-Proto : Proto
  adder-Proto = recv λ _ →
                recv λ _ →
                send λ _ →
                end

  Δ : Env
  Δ = [ d ↦ adder-Proto ]

  prf : ∀ {s₀ s₁} → Δ ⊢ adder-client d s₀ s₁
  prf = output here (output here (input here (λ s m p → end)))

  -- -}
  -- -}
  -- -}
