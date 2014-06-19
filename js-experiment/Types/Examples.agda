open import runningtest
open import prelude
open import proto
open import proc
open import Types


module Types.Examples where

  ≃-refl : ∀ {X} → X ≃? X
  ≃-refl = record { serialize = λ x → x ; parse = succeed ; linv = λ x → succeed refl ; rinv = λ _ → refl }

  module adder where
    adder-Proto : Proto
    adder-Proto = recv λ _ →
                  recv λ _ →
                  send λ _ →
                  end

    prf : ∀ {d s₀ s₁} → [ d ↦ adder-Proto ] ⊢ adder-client d s₀ s₁
    prf = output here (output here (input here (λ s m p → end)))


  module str-sorter₁ where

    sorter-Proto : Proto
    sorter-Proto = send λ _ →
                   recv λ _ →
                   end

    str-sorter₀-P : ∀ {d} → [ d ↦ sorter-Proto ] ⊢ str-sorter₀ d
    str-sorter₀-P = input here (λ s m x → output here end)

    str-merger-P : ∀ {d h₀ h₁} → (ε , d ↦ sorter-Proto , h₀ ↦ dual sorter-Proto , h₁ ↦ dual sorter-Proto)
                               ⊢ str-merger d h₀ h₁
    str-merger-P
      = input (there {!!} (there {!!} here)) λ s m p →
        output (there {!!} here)
       (output here
       (input (there {!!} here) λ ss₀ m₀ p₀ →
        input here λ ss₁ m₁ p₁ →
        output (there {!!} (there {!!} here))
        end))

    str-sorter₁-P : ∀ {d} → [ d ↦ sorter-Proto ] ⊢ str-sorter₁ d
    str-sorter₁-P
      = start sorter-Proto str-sorter₀-P λ h₀ →
        start sorter-Proto str-sorter₀-P λ h₁ →
        str-merger-P

  -- -}
  -- -}
  -- -}
