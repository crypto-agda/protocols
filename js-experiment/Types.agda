open import runningtest

module Types
  (D : Set₀)(M : Set₀){{M≃S : M ≃? String}} where

data 𝟘 : Set where

_≢_ : {A : Set}(x y : A) → Set₀
x ≢ y = x ≡ y → 𝟘

data Env : Set₁ where
  ε : Env
  _,_↦_ : Env → D → Proto → Env

data _↦_∈_ (d : D)(P : Proto) : (Δ : Env) → Set₁ where
  here : ∀ {Δ} → d ↦ P ∈ (Δ , d ↦ P)
  there : ∀ {d' P' Δ} → d ≢ d' → d ↦ P ∈ Δ → d ↦ P ∈ (Δ , d' ↦ P')
-- d ↦ P ∈ Δ = {!!} -- P ≡₁ Δ d

data [_≔_]_≡_ (d : D)(P : Proto) : Env → Env → Set₁ where
  here : ∀ {Δ P'} → [ d ≔ P ] (Δ , d ↦ P') ≡ (Δ , d ↦ P)
  there : ∀ {Δ Δ' d' P'} → d ≢ d' → [ d ≔ P ] Δ ≡ Δ'
          → [ d ≔ P ] (Δ , d' ↦ P') ≡ (Δ' , d' ↦ P')

-- will not compute to completion
data _⊢ᶜ_ (Δ : Env) : Proc D M → Set₁ where

  end :  -- we could check that everything in Δ maps to end
      --------------
         Δ ⊢ᶜ end

  output : ∀ {d m p P Δ'}
        → d ↦ recv P ∈ Δ → [ d ≔ P m ] Δ ≡ Δ' → Δ' ⊢ᶜ p
        → ------------------
          Δ ⊢ᶜ output d m p

  input : ∀ {d p P}
        → d ↦ send P ∈ Δ → (∀ m {Δ'} → [ d ≔ P m ] Δ ≡ Δ' → Δ' ⊢ᶜ p m)
        → --------------------
           Δ ⊢ᶜ input d p

