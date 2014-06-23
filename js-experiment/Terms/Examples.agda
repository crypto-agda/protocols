open import prelude
open import proto
open import libjs
open import Terms
open import Types
open import runningtest using (merge-sort-string)

module Terms.Examples where

  record Σ' (A : Set)(B : A → Set) : Set where
    constructor _,_
    field
      fst' : A
      .snd' : B fst'
  open Σ' public

  S≃?JSValue : String ≃? JSValue
  S≃?JSValue = record { serialize = fromString ; parse = {!!} ; linv = {!!} ; rinv = {!!} }

  postulate
    Σ≃?JSValue : ∀ {A}{{_ : A ≃? JSValue }}(P : A → Set) → Σ' A P ≃? JSValue

  postulate
    merge-sort-spec : ∀ s s' → merge-sort-string (sort s) (sort s') ≡ sort (s ++ s')
    half-spec : ∀ s → (take-half s ++ drop-half s) ≡ s


  module str-sorter where

    blah : {s : String} → (Σ' String λ s' → s' ≡ sort s) ≃? JSValue
    blah {s} = Σ≃?JSValue (λ s' → s' ≡ sort s)

    ap₂ : ∀ {A B C}(f : A → B → C){x x' y y'} → x ≡ x' → y ≡ y'
        → f x y ≡ f x' y'
    ap₂ f refl refl = refl

    infixr 6 _∙_
    _∙_ : ∀ {A}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
    refl ∙ p = p

    sorter-Proto : Proto
    sorter-Proto = recv λ (s : String) →
                   send λ (_ : Σ' String λ s' → s' ≡ sort s) →
                   end

    str-sorter₀ : ∀ {d} → ⊢ [ d ↦ sorter-Proto ]
    str-sorter₀ = input here λ m →
                  output here (sort m , refl)
                  end

    str-merger : ∀ {d h₀ h₁}
      → ⊢ (ε , d ↦ sorter-Proto , h₀ ↦ dual sorter-Proto , h₁ ↦ dual sorter-Proto)
    str-merger =
         input (there (there here)) λ s →
         output (there here) (take-half s)
        (output here (drop-half s)
        (input (there here) λ ss₀ →
         input here λ ss₁ →
         output (there (there here)) (merge-sort-string (fst' ss₀) (fst' ss₁)
                                               , (ap₂ merge-sort-string (snd' ss₀) (snd' ss₁)
                                                 ∙ merge-sort-spec (take-half s) (drop-half s)
                                                 ∙ ap sort (half-spec s)))
         end))

    str-sorter₁ : ∀ {d} → ⊢ [ d ↦ sorter-Proto ]
    str-sorter₁ = start (dual sorter-Proto) str-sorter₀ (λ h₀ →
                  start (dual sorter-Proto) str-sorter₀ (λ h₁ →
                  str-merger))
