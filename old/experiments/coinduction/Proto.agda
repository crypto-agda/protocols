{-# OPTIONS --copatterns #-}
module coinduction.Proto where

open import prelude
open import uri

data Com : Set where IN OUT : Com

data PProto (X : Set₁) : Set₁ where
  end : PProto X
  com : (c : Com){M : Set}(P : M → X) → PProto X


Proto' : Set₁

record Proto : Set₁ where
  coinductive
  field
    obs : Proto'
open Proto public

Proto' = PProto Proto

pattern send P = com OUT P
pattern recv P = com IN P

dualC : Com → Com
dual' : Proto' → Proto'
dual : Proto → Proto

dualC IN = OUT
dualC OUT = IN

dual' end = end
dual' (com c P) = com (dualC c) λ m → dual (P m)

obs (dual P) = dual' (obs P)


Ended : Proto' → Set
Ended end = 𝟙
Ended _ = 𝟘

infixl 5 _,_↦_
data Env : Set₁ where
  ε : Env
  _,_↦_ : (Δ : Env)(d : URI)(P : Proto') → Env


module _ (P : URI → Proto' → Set) where
  AllEnv : Env → Set
  AllEnv ε = 𝟙
  AllEnv (Δ , d ↦ p) = AllEnv Δ × P d p

EndedEnv : Env → Set
EndedEnv = AllEnv λ _ P → Ended P

data _↦_∈_ (d : URI)(P : Proto') : Env → Set₁ where
  here : ∀ {Δ} → d ↦ P ∈ (Δ , d ↦ P)
  there : ∀ {Δ d' P'} → d ↦ P ∈ Δ
                      → d ↦ P ∈ (Δ , d' ↦ P')

module _ {d P} where
  _[_≔_↦_] : ∀ Δ → d ↦ P ∈ Δ → URI → Proto' → Env
  ._ [ here {Δ} ≔ c ↦ Q ] = Δ , c ↦ Q
  ._ [ there {d' = d'}{P'} l ≔ c ↦ Q ] = _ [ l ≔ c ↦ Q ] , d' ↦ P'

module _ {d c M P} where
  _[_≔_] : (Δ : Env) → d ↦ com c {M} P ∈ Δ → M → Env
  Δ [ l ≔ m ] = Δ [ l ≔ d ↦ obs (P m) ]

data Zip : Env → Env → Env → Set₁ where
  ε : Zip ε ε ε
  _,_↦₀_ : ∀ {Δ₀ Δ₁ Δ}(Z : Zip Δ Δ₀ Δ₁) d P → Zip (Δ , d ↦ P) (Δ₀ , d ↦ P)   (Δ₁ , d ↦ end)
  _,_↦₁_ : ∀ {Δ₀ Δ₁ Δ}(Z : Zip Δ Δ₀ Δ₁) d P → Zip (Δ , d ↦ P) (Δ₀ , d ↦ end) (Δ₁ , d ↦ P)

[_is_⋎_] : Env → Env → Env → Set₁
[_is_⋎_] = Zip

Zip-comm : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → [ Δ is Δ₁ ⋎ Δ₀ ]
Zip-comm ε = ε
Zip-comm (Z , d ↦₀ P) = Zip-comm Z , d ↦₁ P
Zip-comm (Z , d ↦₁ P) = Zip-comm Z , d ↦₀ P

module _ {d io M}{P : M → Proto} where
    Zip-com∈₀ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ com io P ∈ Δ₀ → d ↦ com io P ∈ Δ
    Zip-com∈₀ (Z , ._ ↦₀ ._) here = here
    Zip-com∈₀ (Z , c ↦₀ Q)  (there l) = there (Zip-com∈₀ Z l)
    Zip-com∈₀ (Z , c ↦₁ Q)  (there l) = there (Zip-com∈₀ Z l)

    Zip-com∈₁ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ com io P ∈ Δ₁ → d ↦ com io P ∈ Δ
    Zip-com∈₁ Z = Zip-com∈₀ (Zip-comm Z)

    Zip-≔₀ : ∀ {Δ Δ₀ Δ₁}
              (l : d ↦ com io P ∈ Δ₀) {m : M}
              (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
              [ Δ [ Zip-com∈₀ Δₛ l ≔ m ] is Δ₀ [ l ≔ m ] ⋎ Δ₁ ]
    Zip-≔₀ here (Δₛ , ._ ↦₀ ._) = Δₛ , d ↦₀ _
    Zip-≔₀ (there l) (Δₛ , c ↦₀ Q) = Zip-≔₀ l Δₛ , c ↦₀ Q
    Zip-≔₀ (there l) (Δₛ , c ↦₁ Q) = Zip-≔₀ l Δₛ , c ↦₁ Q

    Zip-≔₁ : ∀ {Δ Δ₀ Δ₁}
               (l : d ↦ com io P ∈ Δ₁) {m : M} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
             [ Δ [ Zip-com∈₁ Δₛ l ≔ m ] is Δ₀ ⋎ Δ₁ [ l ≔ m ] ]
    Zip-≔₁ l Δₛ = Zip-comm (Zip-≔₀ l (Zip-comm Δₛ))
