open import runningtest
open import prelude
open import proto
open import proc
open import Types


module Types.Examples (d : URI) where

  ≃-refl : ∀ {X} → X ≃? X
  ≃-refl = record { serialize = λ x → x ; parse = succeed ; linv = λ x → succeed refl ; rinv = λ _ → refl }

  module adder where
    adder-Proto : Proto
    adder-Proto = recv λ _ →
                  recv λ _ →
                  send λ _ →
                  end

    Δ : Env
    Δ = [ d ↦ adder-Proto ]

    prf : ∀ {s₀ s₁} → Δ ⊢ adder-client d s₀ s₁
    prf = output here (output here (input here (λ s m p → end)))


  module str-sorter₁ where

    sorter-Proto : Proto
    sorter-Proto = recv λ _ →
                   send λ _ →
                   end

                   {-
    prf : [ d ↦ dual sorter-Proto ] ⊢ str-sorter₁ d
    prf = {!!}

  -- -}
  -- -}
  -- -}
