module partensor.Shallow.Dom where

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

postulate
  URI : Set

data Dom : Set where
  ε : Dom
  _,_↦* : (δ : Dom) (c : URI) → Dom

module Dom' where
    data _∈_ (c : URI) : Dom → Set where
      here : ∀ {δ} → c ∈ (δ , c ↦*)
      there : ∀ {δ d} (p : c ∈ δ) → c ∈ (δ , d ↦*)
open Dom' using (here; there) public

data DiffDom' : ∀ {c d δ} → c Dom'.∈ δ → d Dom'.∈ δ → Set where
  h/t : ∀ {c d δ}(l : c Dom'.∈ δ) → DiffDom' (here {d}{δ}) (there l)
  t/h : ∀ {c d δ}(l : c Dom'.∈ δ) → DiffDom' (there l) (here {d}{δ})
  t/t : ∀ {c d j δ}{l : c Dom'.∈ δ}{l' : d Dom'.∈ δ} → DiffDom' l l'
    → DiffDom' {δ = δ , j ↦*} (there l) (there l')

sameDom? : ∀ {c d δ}(l : c Dom'.∈ δ)(l' : d Dom'.∈ δ)
  → DiffDom' l l' ⊎ (∃ λ (d=c : d ≡ c) → l ≡ subst _ d=c l')
sameDom? here here = inj₂ (refl , refl)
sameDom? here (there l') = inj₁ (h/t l')
sameDom? (there l) here = inj₁ (t/h l)
sameDom? (there l) (there l') with sameDom? l l'
sameDom? (there l) (there l') | inj₁ x = inj₁ (t/t x)
sameDom? (there l) (there .l) | inj₂ (refl , refl) = inj₂ (refl , refl)

infixr 4 _♦Dom_
_♦Dom_ : Dom → Dom → Dom
δ ♦Dom ε = δ
δ ♦Dom (δ' , d ↦*) = (δ ♦Dom δ') , d ↦*

∈♦₀ : ∀ {c E F} → c Dom'.∈ E → c Dom'.∈ (E ♦Dom F)
∈♦₀ {F = ε} l = l
∈♦₀ {F = F , c₁ ↦*} l = there (∈♦₀ {F = F} l)
