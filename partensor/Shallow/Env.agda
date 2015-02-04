open import Data.One
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP
open import partensor.Shallow.Dom as Dom
open import partensor.Shallow.Session as Session hiding (Ended)

module partensor.Shallow.Env where

open import partensor.Shallow.Map as Map public

Env : Dom → Set₁
Env = Map MSession

module _ {δ c}(E : Env δ) where
  infixl 4 _/'_ _/D_
  _/D_ :  c ∈D δ → Env δ
  _/D_ l = E [ l ]≔' end

  _/'_ : ∀ {S} → c ↦ S ∈ E → Env δ
  _/'_ l = _/D_ (_↦_∈_.lA l)

infixr 4 _♦Env_
_♦Env_ : ∀ {D₀ D₁} → Env D₀ → Env D₁ → Env (D₀ ♦Dom D₁)
_♦Env_ = _♦Map_

open With-end {_} {MSession} end public

Ended : ∀ {δ}(E : Env δ) → Set
Ended = Map.All (λ _ → Session.Ended)

Ended-/* : ∀ {δ}(E : Env δ) → Ended (E /*)
Ended-/* ε = _
Ended-/* (E , c ↦ v) = Ended-/* E , _

Ended-∈D : ∀ {δE c}{E : Env δE} (l : c ∈D δE) → Ended E → Session.Ended (lookup E l)
Ended-∈D {E = _ , _ ↦ _} here      EE = snd EE
Ended-∈D {E = _ , _ ↦ _} (there l) EE = Ended-∈D l (fst EE)

Ended-↦∈ : ∀ {δE c S}{E : Env δE} (l : c ↦ S ∈ E) (EE : Ended E) → Session.Ended S
Ended-↦∈ ⟨ l R⟩ = Ended-∈D l

{-
ZipAll : ∀ {S Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → All S Δ₀ → All S Δ₁ → All S Δ
ZipAll ε A₀ A₁ = 0₁
ZipAll (Z , d ↦₀ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₀
ZipAll (Z , d ↦₁ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₁

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
-- -}
-- -}
-- -}
-- -}
-- -}
