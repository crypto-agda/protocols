open import libjs
-- open import proc
open import proto
open import prelude
open import uri

module Types where

infixl 5 _,_↦_
data Env : Set₁ where
  ε : Env
  _,_↦_ : (Δ : Env)(d : URI)(P : Proto) → Env

data Zip : Env → Env → Env → Set₁ where
  ε : Zip ε ε ε
  _,_↦₀_ : ∀ {Δ₀ Δ₁ Δ}(Z : Zip Δ Δ₀ Δ₁) d P → Zip (Δ , d ↦ P) (Δ₀ , d ↦ P)   (Δ₁ , d ↦ end)
  _,_↦₁_ : ∀ {Δ₀ Δ₁ Δ}(Z : Zip Δ Δ₀ Δ₁) d P → Zip (Δ , d ↦ P) (Δ₀ , d ↦ end) (Δ₁ , d ↦ P)

[_is_⋎_] : Env → Env → Env → Set₁
[_is_⋎_] = Zip

[_↦_] : URI → Proto → Env
[ d ↦ P ] = ε , d ↦ P

infixr 4 _,,_
_,,_ : Env → Env → Env
Δ ,, ε = Δ
Δ ,, (Δ' , d ↦ P) = (Δ ,, Δ') , d ↦ P


data _↦_∈_ (d : URI)(P : Proto) : Env → Set₁ where
  here : ∀ {Δ} → d ↦ P ∈ (Δ , d ↦ P)
  there : ∀ {Δ d' P'} → d ↦ P ∈ Δ
                      → d ↦ P ∈ (Δ , d' ↦ P')

module _ {d P} where
  _[_≔_↦_] : ∀ Δ → d ↦ P ∈ Δ → URI → Proto → Env
  ._ [ here {Δ} ≔ c ↦ Q ] = Δ , c ↦ Q
  ._ [ there {d' = d'}{P'} l ≔ c ↦ Q ] = _ [ l ≔ c ↦ Q ] , d' ↦ P'

module _ {d c M}{{_ : M ≃? SERIAL}} {P} where
  _[_≔_] : (Δ : Env) → d ↦ com c {M} P ∈ Δ → M → Env
  Δ [ l ≔ m ] = Δ [ l ≔ d ↦ P m ]

AllEnv : (P : URI → Proto → Set) → Env → Set
AllEnv P ε = 𝟙
AllEnv P (Δ , d ↦ p) = AllEnv P Δ × P d p

Ended : Proto → Set
Ended end = 𝟙
Ended _   = 𝟘

EndedEnv : Env → Set
EndedEnv = AllEnv λ _ → Ended

ZipAll : ∀ {P Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → AllEnv P Δ₀ → AllEnv P Δ₁ → AllEnv P Δ
ZipAll ε A₀ A₁ = <>
ZipAll (Z , d ↦₀ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₀
ZipAll (Z , d ↦₁ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₁

ZipEnded : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → EndedEnv Δ₀ → EndedEnv Δ₁ → EndedEnv Δ
ZipEnded = ZipAll

Ended-≡end : ∀ {P} → Ended P → P ≡ end
Ended-≡end {end} e = refl
Ended-≡end {send P} ()
Ended-≡end {recv P} ()

Zip-comm : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → [ Δ is Δ₁ ⋎ Δ₀ ]
Zip-comm ε = ε
Zip-comm (Z , d ↦₀ P) = Zip-comm Z , d ↦₁ P
Zip-comm (Z , d ↦₁ P) = Zip-comm Z , d ↦₀ P

Zip-identity : ∀ {Δ₀ Δ₁ Δ} {{Δ₀E : EndedEnv Δ₀}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₁ ≡ Δ
Zip-identity ε = refl
Zip-identity {{E , e}} (Z , d ↦₀ P) = ap₂ (λ Δ P → Δ , d ↦ P) (Zip-identity Z) (! (Ended-≡end e))
Zip-identity {{E , e}} (Z , d ↦₁ P) = ap (λ Δ → Δ , d ↦ P) (Zip-identity Z)

Zip-identity' : ∀ {Δ₀ Δ₁ Δ} {{Δ₁E : EndedEnv Δ₁}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₀ ≡ Δ
Zip-identity' Z = Zip-identity (Zip-comm Z)

module _ {d io M}{{_ : SER M}} {P : M → Proto} where
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

module _ {M : Set}{{_ : SER M}} where
  _parsesTo_ : SERIAL → M → Set
  s parsesTo m = succeed m ≡ parse s


-- -}
-- -}
-- -}
-- -}
-- -}
