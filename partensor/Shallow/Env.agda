open import Data.One
open import Data.Product
{-
open import Data.Zero
open import Data.Sum
open import Data.Nat

-}
open import Relation.Binary.PropositionalEquality.NP
open import partensor.Shallow.Dom as Dom
open import partensor.Shallow.Session as Session hiding (Ended)

module partensor.Shallow.Env where

open import partensor.Shallow.Map as Map public

Env : Dom → Set₁
Env = Map Session

module _ {δ d S}(Δ : Env δ) where
  _/_ : d ↦ S ∈ Δ → Env δ
  _/_ l = Δ [ l ]≔ end

module _ {δ d c M S}(Δ : Env δ) where
  _[_≔_] : d ↦ act (com c {M} S) ∈ Δ → M → Env δ
  _[_≔_] l m = Δ [ l ]≔ S m

infixr 4 _♦Env_
_♦Env_ : ∀ {D₀ D₁} → Env D₀ → Env D₁ → Env (D₀ ♦Dom D₁)
_♦Env_ = _♦Map_

open With-end {_} {Session} end public

Ended : ∀ {δ} (Δ : Env δ) → Set
Ended = Map.All (λ _ → Session.Ended)

{-
_[_+=_]η : ∀{d S δ δ'}(η : Env δ)(l : d ↦ S ∈ η) → Env δ' → Env {!!}
(η , d ↦ S) [ here    += η' ]η = {!η ♦Env η'!}
(η , d ↦ S) [ there l += η' ]η = η [ l += η' ]η , d ↦ S
-}

{-
postulate
  URI : Set

infixl 5 _,_↦_
data Env : Set₁ where
  ε : Env
  _,_↦_ : (Δ : Env)(d : URI)(S : Session) → Env

data _↦_∈_ (d : URI)(P : Session) : Env → Set₁ where
  here  : ∀ {Δ} → d ↦ P ∈ (Δ , d ↦ P)
  there : ∀ {Δ d' P'} → d ↦ P ∈ Δ
                      → d ↦ P ∈ (Δ , d' ↦ P')

module _ {d P} where
  _[_≔_↦_] : ∀ Δ → d ↦ P ∈ Δ → URI → Session → Env
  ._ [ here {Δ} ≔ c ↦ Q ] = Δ , c ↦ Q
  ._ [ there {d' = d'}{P'} l ≔ c ↦ Q ] = _ [ l ≔ c ↦ Q ] , d' ↦ P'

module _ {d c M} {P} where
  _[_≔_] : (Δ : Env) → d ↦ act (com c {M} P) ∈ Δ → M → Env
  Δ [ l ≔ m ] = Δ [ l ≔ d ↦ P m ]

All : (Pred : URI → Session → Set) → Env → Set
All Pred ε = 𝟙
All Pred (Δ , d ↦ p) = All Pred Δ × Pred d p

ZipAll : ∀ {S Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → All S Δ₀ → All S Δ₁ → All S Δ
ZipAll ε A₀ A₁ = 0₁
ZipAll (Z , d ↦₀ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₀
ZipAll (Z , d ↦₁ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₁

Ended : Env → Set
Ended = All λ _ → Session.Ended

ZipEnded : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → Ended Δ₀ → Ended Δ₁ → Ended Δ
ZipEnded = ZipAll

Zip-comm : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → [ Δ is Δ₁ ⋎ Δ₀ ]
Zip-comm ε = ε
Zip-comm (Z , d ↦₀ P) = Zip-comm Z , d ↦₁ P
Zip-comm (Z , d ↦₁ P) = Zip-comm Z , d ↦₀ P

Zip-identity : ∀ {Δ₀ Δ₁ Δ} {{Δ₀E : Ended Δ₀}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₁ ≡ Δ
Zip-identity ε = refl
Zip-identity {{E , e}} (Z , d ↦₀ P) = ap₂ (λ Δ P → Δ , d ↦ P) (Zip-identity Z) (! (Ended-≡end e))
Zip-identity {{E , e}} (Z , d ↦₁ P) = ap (λ Δ → Δ , d ↦ P) (Zip-identity Z)

Zip-identity' : ∀ {Δ₀ Δ₁ Δ} {{Δ₁E : Ended Δ₁}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₀ ≡ Δ
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

infixr 4 _,,_
_,,_ : Env → Env → Env
Δ ,, ε = Δ
Δ ,, (Δ' , d ↦ P) = (Δ ,, Δ') , d ↦ P
-- -}
