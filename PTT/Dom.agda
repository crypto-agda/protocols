module PTT.Dom where

open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product
open import Relation.Binary.PropositionalEquality

postulate
  URI : Set

data Dom : Set where
  ε : Dom
  _,_↦* : (δ : Dom) (c : URI) → Dom

data _∈D_ (c : URI) : Dom → Set where
  here  : ∀ {δ} → c ∈D (δ , c ↦*)
  there : ∀ {δ d} (p : c ∈D δ) → c ∈D (δ , d ↦*)

pattern hereD = _∈D_.here
pattern thereD p = _∈D_.there p

data DiffDom : ∀ {c d δ} → c ∈D δ → d ∈D δ → Set where
  h/t : ∀ {c d δ}(l : c ∈D δ) → DiffDom (here {d}{δ}) (there l)
  t/h : ∀ {c d δ}(l : c ∈D δ) → DiffDom (there l) (here {d}{δ})
  t/t : ∀ {c d j δ}{l : c ∈D δ}{l' : d ∈D δ} → DiffDom l l'
    → DiffDom {δ = δ , j ↦*} (there l) (there l')

sameDom? : ∀ {c d δ}(l : c ∈D δ)(l' : d ∈D δ)
  → DiffDom l l' ⊎ (∃ λ (d=c : d ≡ c) → l ≡ subst _ d=c l')
sameDom? here here = inr (refl , refl)
sameDom? here (there l') = inl (h/t l')
sameDom? (there l) here = inl (t/h l)
sameDom? (there l) (there l') with sameDom? l l'
sameDom? (there l) (there l') | inl x = inl (t/t x)
sameDom? (there l) (there .l) | inr (refl , refl) = inr (refl , refl)

infixr 4 _♦Dom_
_♦Dom_ : Dom → Dom → Dom
δ ♦Dom ε = δ
δ ♦Dom (δ' , d ↦*) = (δ ♦Dom δ') , d ↦*

∈♦₀ : ∀ {c E F} → c ∈D E → c ∈D (E ♦Dom F)
∈♦₀ {F = ε} l = l
∈♦₀ {F = F , c₁ ↦*} l = there (∈♦₀ {F = F} l)
