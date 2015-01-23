open import Data.Product
open import Data.Zero
open import Data.One
open import Data.Sum
open import Data.List
open import Data.Nat

open import Relation.Binary.PropositionalEquality.NP
open import partensor.Shallow.Session

module partensor.Shallow.Proto where

postulate
  URI : Set

infixl 5 _,_↦_
data Env : Set₁ where
  ε : Env
  _,_↦_ : (Δ : Env)(d : URI)(P : Session) → Env

data Proto : Set₁ where
  · : Proto
  _,[_] : Proto → Env → Proto


data Zip : Env → Env → Env → Set₁ where
  ε : Zip ε ε ε
  _,_↦₀_ : ∀ {Δ₀ Δ₁ Δ}(Z : Zip Δ Δ₀ Δ₁) d P → Zip (Δ , d ↦ P) (Δ₀ , d ↦ P)   (Δ₁ , d ↦ end)
  _,_↦₁_ : ∀ {Δ₀ Δ₁ Δ}(Z : Zip Δ Δ₀ Δ₁) d P → Zip (Δ , d ↦ P) (Δ₀ , d ↦ end) (Δ₁ , d ↦ P)

data ZipP : ℕ → Proto → Proto → Proto → Set₁ where
  · : ∀ {n} → ZipP n · · ·
  _,[_]₀ : ∀ {n}{Δ₀ Δ₁ Δ}(Z : ZipP n Δ Δ₀ Δ₁) η → ZipP n (Δ ,[ η ]) (Δ₀ ,[ η ]) (Δ₁ ,[ ε ])
  _,[_]₁ : ∀ {n}{Δ₀ Δ₁ Δ}(Z : ZipP n Δ Δ₀ Δ₁) η → ZipP n (Δ ,[ η ]) (Δ₀ ,[ ε ]) (Δ₁ ,[ η ])
  _,[_]ₘ : ∀ {n}{Δ₀ Δ₁ Δ}{η₀ η₁ η}(Z : ZipP n Δ Δ₀ Δ₁)(Zη : Zip η η₀ η₁) → ZipP (suc n) (Δ ,[ η ]) (Δ₀ ,[ η₀ ]) (Δ₁ ,[ η₁ ])

[_is_⋎_] : Env → Env → Env → Set₁
[_is_⋎_] = Zip

[_↦_] : URI → Session → Env
[ d ↦ P ] = ε , d ↦ P

infixr 4 _,,_
_,,_ : Env → Env → Env
Δ ,, ε = Δ
Δ ,, (Δ' , d ↦ P) = (Δ ,, Δ') , d ↦ P

data [_]∈_ (η : Env) : Proto → Set₁ where
  here  : ∀ {I} → [ η ]∈ I ,[ η ]
  there : ∀ {I σ} → [ η ]∈ I → [ η ]∈ I ,[ σ ]

_[_≔*_] : ∀{η}(P : Proto) → [ η ]∈ P → List Env → Proto
(Δ ,[ _ ]) [ here ≔* xs ] = foldr (λ σ Δ' → Δ' ,[ σ ]) Δ xs
(Δ ,[ η ]) [ there l ≔* xs ] = Δ [ l ≔* xs ] ,[ η ]


data _↦_∈_ (d : URI)(P : Session) : Env → Set₁ where
  here  : ∀ {Δ} → d ↦ P ∈ (Δ , d ↦ P)
  there : ∀ {Δ d' P'} → d ↦ P ∈ Δ
                      → d ↦ P ∈ (Δ , d' ↦ P')

[_↦_]∈_ : (d : URI)(S : Session) → Proto → Set₁
[ d ↦ S ]∈ P = [ (ε , d ↦ S) ]∈ P

_[_+=_]η : ∀{d S}(η : Env)(l : d ↦ S ∈ η) → Env → Env
(η , d ↦ S) [ here += η' ]η = η ,, η'
(η , d ↦ S) [ there l += xs ]η = η [ l += xs ]η , d ↦ S

module _ {d P} where
  _[_≔_↦_] : ∀ Δ → d ↦ P ∈ Δ → URI → Session → Env
  ._ [ here {Δ} ≔ c ↦ Q ] = Δ , c ↦ Q
  ._ [ there {d' = d'}{P'} l ≔ c ↦ Q ] = _ [ l ≔ c ↦ Q ] , d' ↦ P'

module _ {d c M} {P} where
  _[_≔_] : (Δ : Env) → d ↦ act (com c {M} P) ∈ Δ → M → Env
  Δ [ l ≔ m ] = Δ [ l ≔ d ↦ P m ]

AllEnv : (P : URI → Session → Set) → Env → Set
AllEnv P ε = 𝟙
AllEnv P (Δ , d ↦ p) = AllEnv P Δ × P d p

Ended : Session → Set
Ended end = 𝟙
Ended _   = 𝟘

EndedEnv : Env → Set
EndedEnv = AllEnv λ _ → Ended

ZipAll : ∀ {P Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → AllEnv P Δ₀ → AllEnv P Δ₁ → AllEnv P Δ
ZipAll ε A₀ A₁ = 0₁
ZipAll (Z , d ↦₀ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₀
ZipAll (Z , d ↦₁ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₁

ZipEnded : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → EndedEnv Δ₀ → EndedEnv Δ₁ → EndedEnv Δ
ZipEnded = ZipAll

Ended-≡end : ∀ {P} → Ended P → P ≡ end
Ended-≡end {act x} ()
Ended-≡end {⅋ P P₁} ()
Ended-≡end {⊗ P P₁} ()
Ended-≡end {end} p = refl

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

module _ {d io M} {P : M → Session} where
    Zip-com∈₀ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ act (com io P) ∈ Δ₀ → d ↦ act (com io P) ∈ Δ
    Zip-com∈₀ (Z , ._ ↦₀ ._) here = here
    Zip-com∈₀ (Z , c ↦₀ Q)  (there l) = there (Zip-com∈₀ Z l)
    Zip-com∈₀ (Z , c ↦₁ Q)  (there l) = there (Zip-com∈₀ Z l)

    Zip-com∈₁ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ act (com io P) ∈ Δ₁ → d ↦ act (com io P) ∈ Δ
    Zip-com∈₁ Z = Zip-com∈₀ (Zip-comm Z)

    Zip-≔₀ : ∀ {Δ Δ₀ Δ₁}
              (l : d ↦ act (com io P) ∈ Δ₀) {m : M}
              (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
              [ Δ [ Zip-com∈₀ Δₛ l ≔ m ] is Δ₀ [ l ≔ m ] ⋎ Δ₁ ]
    Zip-≔₀ here (Δₛ , ._ ↦₀ ._) = Δₛ , d ↦₀ _
    Zip-≔₀ (there l) (Δₛ , c ↦₀ Q) = Zip-≔₀ l Δₛ , c ↦₀ Q
    Zip-≔₀ (there l) (Δₛ , c ↦₁ Q) = Zip-≔₀ l Δₛ , c ↦₁ Q

    Zip-≔₁ : ∀ {Δ Δ₀ Δ₁}
               (l : d ↦ act (com io P) ∈ Δ₁) {m : M} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
             [ Δ [ Zip-com∈₁ Δₛ l ≔ m ] is Δ₀ ⋎ Δ₁ [ l ≔ m ] ]
    Zip-≔₁ l Δₛ = Zip-comm (Zip-≔₀ l (Zip-comm Δₛ))
