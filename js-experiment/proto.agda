module _ where

open import prelude
open import libjs

data Proto : Set₁ where
  end : Proto
  send recv : {M : Set} {{M≃S : M ≃? JSValue}} (P : M → Proto) → Proto

dual : Proto → Proto
dual end      = end
dual (send P) = recv λ m → dual (P m)
dual (recv P) = send λ m → dual (P m)

log : Proto → Proto
log end      = end
log (send P) = send λ m → log (P m)
log (recv P) = send λ m → log (P m)

⟦_⟧ : Proto → Set
⟦ end ⟧ = 𝟙
⟦ send P ⟧ = Σ _ λ m → ⟦ P m ⟧
⟦ recv P ⟧ = (m : _) → ⟦ P m ⟧

⟦_⟧D : Proto → Set → Set
⟦ end ⟧D D = 𝟙
⟦ send P ⟧D D = D × Σ _ λ m → ⟦ P m ⟧D D
⟦ recv P ⟧D D = D × ((m : _) → ⟦ P m ⟧D D)

{-
_⅋_ : Proto → Proto → Proto
end    ⅋ Q      = Q
recv P ⅋ Q      = recv λ m → P m ⅋ Q
P      ⅋ end    = P
P      ⅋ recv Q = recv λ m → P ⅋ Q m
send P ⅋ send Q = send {{{!!}}} [inl: (λ m → P m ⅋ send Q)
                                ,inr: (λ n → send P ⅋ Q n) ]
-}

                             {-
_⊗_ : Proto → Proto → Proto
end    ⊗ Q      = Q
send P ⊗ Q      = send λ m → P m ⊗ Q
P      ⊗ end    = P
P      ⊗ send Q = send λ m → P ⊗ Q m
recv P ⊗ recv Q = recv [inl: (λ m → P m ⊗ recv Q)
                       ,inr: (λ n → recv P ⊗ Q n) ]
-}

telecom : (P : Proto) (p : ⟦ P ⟧) (q : ⟦ dual P ⟧) → ⟦ log P ⟧
telecom end p q = _
telecom (send P) (m , p) q = m , telecom (P m) p (q m)
telecom (recv P) p (m , q) = m , telecom (P m) (p m) q
