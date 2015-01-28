module partensor.Shallow.Dom where

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

infixr 4 _♦Dom_
_♦Dom_ : Dom → Dom → Dom
δ ♦Dom ε = δ
δ ♦Dom (δ' , d ↦*) = (δ ♦Dom δ') , d ↦*
