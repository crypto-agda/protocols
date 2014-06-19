open import libjs
open import proc
open import proto
open import prelude

module Types where

SERIAL = JSValue

SER : Set → Set
SER M = M ≃? SERIAL

data 𝟘 : Set where

_≢_ : {A : Set}(x y : A) → Set₀
x ≢ y = x ≡ y → 𝟘

data Env : Set₁ where
  ε : Env
  _,_↦_ : Env → URI → Proto → Env

[_↦_] : URI → Proto → Env
[ d ↦ P ] = ε , d ↦ P

data Com : Set where send recv : Com

com : {M : Set}{{_ : M ≃? SERIAL}} → Com → (M → Proto) → Proto
com send P = send P
com recv P = recv P

data _↦_is_∈_ (d : URI){M : Set}{{_ : M ≃? SERIAL}}(c : Com)(P : M → Proto) : Env → Set₁ where
  here : ∀ {Δ} → d ↦ c is P ∈ (Δ , d ↦ com c P)
  there : ∀ {Δ d' P'} → d ≢ d' → d ↦ c is P ∈ Δ
                      → d ↦ c is P ∈ (Δ , d' ↦ P')

module _ {d c M}{{_ : M ≃? SERIAL}} {P} where
  _[_≔_] : (Δ : Env) → d ↦ c is P ∈ Δ → M → Env
  ._ [ here {Δ} ≔ m ] = Δ , d ↦ P m
  ._ [ there {d' = d'}{P'} x₁ var ≔ m ] = _ [ var ≔ m ] , d' ↦ P'

AllEnv : (P : URI → Proto → Set) → Env → Set
AllEnv P ε = 𝟙
AllEnv P (Δ , d ↦ p) = AllEnv P Δ × P d p

Ended : Proto → Set
Ended end = 𝟙
Ended (send P) = 𝟘
Ended (recv P) = 𝟘

module _ {M : Set}{{_ : SER M}} where
  _parsesTo_ : SERIAL → M → Set
  s parsesTo m = succeed m ≡ parse s

data _⊢_ (Δ : Env) : JSProc → Set₁ where

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

           {-
  start : ∀ {s p} P
        → [ clientURI ↦ P ] ⊢ {!!}
        → -------------------
          Δ ⊢ start s p
          -}

toProcWT : ∀ {d} P → (p : ⟦ P ⟧) → [ d ↦ dual P ] ⊢ toProc d P p
toProcWT end p = end
toProcWT (send P) (m , p) = output here (toProcWT (P m) p)
toProcWT (recv P) p = input here λ { s m prf → subst (λ X → _ ⊢ [succeed: _ ,fail: _ ] X)
                                                     prf (toProcWT (P m) (p m)) }


-- -}
-- -}
-- -}
-- -}
-- -}
