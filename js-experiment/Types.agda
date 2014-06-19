open import runningtest

module Types
  (D : Set₀) where -- (M : Set₀){{M≃S : M ≃? String}} where

SERIAL = String

SER : Set → Set
SER M = M ≃? SERIAL

open _≃?_ {{...}}
data 𝟘 : Set where

_≢_ : {A : Set}(x y : A) → Set₀
x ≢ y = x ≡ y → 𝟘

data Env : Set₁ where
  ε : Env
  _,_↦_ : Env → D → Proto → Env

[_↦_] : D → Proto → Env
[ d ↦ P ] = ε , d ↦ P

data Com : Set where send recv : Com

com : {M : Set}{{_ : M ≃? SERIAL}} → Com → (M → Proto) → Proto
com send P = send P
com recv P = recv P

data _↦_is_∈_ (d : D){M : Set}{{_ : M ≃? SERIAL}}(c : Com)(P : M → Proto) : Env → Set₁ where
  here : ∀ {Δ} → d ↦ c is P ∈ (Δ , d ↦ com c P)
  there : ∀ {Δ d' P'} → d ≢ d' → d ↦ c is P ∈ Δ
                      → d ↦ c is P ∈ (Δ , d' ↦ P')

module _ {d c M}{{_ : M ≃? SERIAL}} {P} where
  _[_≔_] : (Δ : Env) → d ↦ c is P ∈ Δ → M → Env
  ._ [ here {Δ} ≔ m ] = Δ , d ↦ P m
  ._ [ there {d' = d'}{P'} x₁ var ≔ m ] = _ [ var ≔ m ] , d' ↦ P'

AllEnv : (P : D → Proto → Set) → Env → Set
AllEnv P ε = 𝟙
AllEnv P (Δ , d ↦ p) = AllEnv P Δ × P d p

Ended : Proto → Set
Ended end = 𝟙
Ended (send P) = 𝟘
Ended (recv P) = 𝟘

module _ {M : Set}{{_ : SER M}} where
  _parsesTo_ : SERIAL → M → Set
  s parsesTo m = succeed m ≡ parse s

data _⊢_ (Δ : Env) : Proc D SERIAL → Set₁ where

  end : {_ : AllEnv (λ _ p → Ended p) Δ}
     → --------------
         Δ ⊢ end

  output : ∀ {d M m p}{{_ : SER M}}{P : M → Proto}
        → (l : d ↦ recv is P ∈ Δ) → Δ [ l ≔ m ] ⊢ p
        → ------------------
          Δ ⊢ output d (serialize m) p

  input : ∀ {d p M}{{_ : SER M}}{P}
        → (l : d ↦ send is P ∈ Δ) → (∀ s m → s parsesTo m → Δ [ l ≔ m ] ⊢ p s)
        → --------------------
           Δ ⊢ input d p


-- -}
-- -}
-- -}
-- -}
-- -}
