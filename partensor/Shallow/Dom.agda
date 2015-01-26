module partensor.Shallow.Dom where

postulate
  URI : Set

data Dom : Set where
  ε : Dom
  _,_ : (δ : Dom) (c : URI) → Dom

infixr 4 _♦Dom_
_♦Dom_ : Dom → Dom → Dom
δ ♦Dom ε = δ
δ ♦Dom (δ' , d) = (δ ♦Dom δ') , d
