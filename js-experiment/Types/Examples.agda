open import runningtest
open import libjs
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

    prf : ∀ {d s₀ s₁} → [ d ↦ dual adder-Proto ] ⊢ adder-client d s₀ s₁
    prf = output here refl (output here refl (input here (λ s m p → end)))


  module str-sorter₁ where

    sorter-Proto : Proto
    sorter-Proto = send λ _ →
                   recv λ _ →
                   end

    str-sorter₀-P : ∀ {d} → [ d ↦ dual sorter-Proto ] ⊢ str-sorter₀ d
    str-sorter₀-P = input here (λ s m x → output here refl end)

    str-merger-P : ∀ {d h₀ h₁} → (ε , d ↦ dual sorter-Proto , h₀ ↦ sorter-Proto , h₁ ↦ sorter-Proto)
                               ⊢ str-merger d h₀ h₁
    str-merger-P
      = input (there (there here)) λ s m p →
        output (there here) refl
       (output here refl
       (input (there here) λ ss₀ m₀ p₀ →
        input here λ ss₁ m₁ p₁ →
        output (there (there here)) refl
        end))

    str-sorter₁-P : ∀ {d} → [ d ↦ dual sorter-Proto ] ⊢ str-sorter₁ d
    str-sorter₁-P
      = start sorter-Proto str-sorter₀-P λ h₀ →
        start sorter-Proto str-sorter₀-P λ h₁ →
        str-merger-P

  module str-sorter-cool where


    foo : String ≃? JSValue
    foo = record { serialize = fromString ; parse = {!!} ; linv = {!!} ; rinv = {!!} }
    postulate
      bar : ∀ {s} → Σ String (λ s' → s' ≡ sort s) ≃? JSValue

    sorter-Proto : Proto
    sorter-Proto = recv λ (s : String) →
                   send λ (_ : Σ String λ s' → s' ≡ sort s) →
                   end

    str-sorter₀-P : ∀ {d} → [ d ↦ sorter-Proto ] ⊢ str-sorter₀ d
    str-sorter₀-P = input here (λ s m x → output here {!!} end)
  -- -}
  -- -}
  -- -}
