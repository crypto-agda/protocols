

  {-
mutual
  ⅋-comm : ∀ P Q → ⟦ P ⅋ Q ⟧ → ⟦ Q ⅋ P ⟧
  ⅋-comm P Q p = ⅋-comm-view (view-⅋ P Q p)

  ⅋-comm-view : ∀ {P Q} {pq : ⟦ P ⅋ Q ⟧} → View-⅋ P Q pq → ⟦ Q ⅋ P ⟧
  ⅋-comm-view (sendL' P Q m p) = ⅋-sendR (send Q) m (⅋-comm (P m) (send Q) p)
  ⅋-comm-view (sendR' P Q n p) = inl n , ⅋-comm (send P) (Q n) p
  ⅋-comm-view (recvL' P Q pq)  = ⅋-recvR Q P λ m → ⅋-comm (P m) Q (pq m)
  ⅋-comm-view (recvR' P Q pq)  = λ n → ⅋-comm (send P) (Q n) (pq n)
  ⅋-comm-view (endL Q pq)      = ⅋-rend! Q pq
  ⅋-comm-view (send P m pq)    = m , pq
-}
{-
-- see dist-⅋-&
dist-⅋-fst : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ P ⅋ Q ⟧
dist-⅋-fst (recv P) Q R p = λ m → dist-⅋-fst (P m) Q R (p m)
dist-⅋-fst (send P) Q R p = p `L
dist-⅋-fst end      Q R p = p `L

-- see dist-⅋-&
dist-⅋-snd : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ P ⅋ R ⟧
dist-⅋-snd (recv P) Q R p = λ m → dist-⅋-snd (P m) Q R (p m)
dist-⅋-snd (send P) Q R p = p `R
dist-⅋-snd end      Q R p = p `R

-- see dist-⅋-&
dist-⅋-× : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ P ⅋ Q ⟧ × ⟦ P ⅋ R ⟧
dist-⅋-× P Q R p = dist-⅋-fst P Q R p , dist-⅋-snd P Q R p

-- see dist-⅋-&
dist-⅋-& : ∀ P Q R → ⟦ P ⅋ (Q & R) ⟧ → ⟦ (P ⅋ Q) & (P ⅋ R) ⟧
dist-⅋-& P Q R p = ×→& (dist-⅋-× P Q R p)

-- see dist-⅋-&
factor-,-⅋ : ∀ P Q R → ⟦ P ⅋ Q ⟧ → ⟦ P ⅋ R ⟧ → ⟦ P ⅋ (Q & R) ⟧
factor-,-⅋ end      Q R pq pr = ×→& (pq , pr)
factor-,-⅋ (recv P) Q R pq pr = λ m → factor-,-⅋ (P m) Q R (pq m) (pr m)
factor-,-⅋ (send P) Q R pq pr = [L: pq R: pr ]

-- see dist-⅋-&
factor-×-⅋ : ∀ P Q R → ⟦ P ⅋ Q ⟧ × ⟦ P ⅋ R ⟧ → ⟦ P ⅋ (Q & R) ⟧
factor-×-⅋ P Q R (p , q) = factor-,-⅋ P Q R p q

-- see dist-⅋-&
factor-&-⅋ : ∀ P Q R → ⟦ (P ⅋ Q) & (P ⅋ R) ⟧ → ⟦ P ⅋ (Q & R) ⟧
factor-&-⅋ P Q R p = factor-×-⅋ P Q R (&→× p)

-- see dist-⅋-&
module _ {{_ : FunExt}} where
  dist-⅋-fst-factor-&-, : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧)(pr : ⟦ P ⅋ R ⟧)
                          → dist-⅋-fst P Q R (factor-,-⅋ P Q R pq pr) ≡ pq
  dist-⅋-fst-factor-&-, (recv P) Q R pq pr = λ= λ m → dist-⅋-fst-factor-&-, (P m) Q R (pq m) (pr m)
  dist-⅋-fst-factor-&-, (send P) Q R pq pr = refl
  dist-⅋-fst-factor-&-, end      Q R pq pr = refl

  dist-⅋-snd-factor-&-, : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧)(pr : ⟦ P ⅋ R ⟧)
                          → dist-⅋-snd P Q R (factor-,-⅋ P Q R pq pr) ≡ pr
  dist-⅋-snd-factor-&-, (recv P) Q R pq pr = λ= λ m → dist-⅋-snd-factor-&-, (P m) Q R (pq m) (pr m)
  dist-⅋-snd-factor-&-, (send P) Q R pq pr = refl
  dist-⅋-snd-factor-&-, end      Q R pq pr = refl

  factor-×-⅋-linv-dist-⅋-× : ∀ P Q R → (factor-×-⅋ P Q R) LeftInverseOf (dist-⅋-× P Q R)
  factor-×-⅋-linv-dist-⅋-× (recv P) Q R p = λ= λ m → factor-×-⅋-linv-dist-⅋-× (P m) Q R (p m)
  factor-×-⅋-linv-dist-⅋-× (send P) Q R p = λ= λ { `L → refl ; `R → refl }
  factor-×-⅋-linv-dist-⅋-× end      Q R p = λ= λ { `L → refl ; `R → refl }

  module _ P Q R where
      factor-×-⅋-rinv-dist-⅋-× : (factor-×-⅋ P Q R) RightInverseOf (dist-⅋-× P Q R)
      factor-×-⅋-rinv-dist-⅋-× (x , y) = pair×= (dist-⅋-fst-factor-&-, P Q R x y) (dist-⅋-snd-factor-&-, P Q R x y)

      dist-⅋-×-≃ : ⟦ P ⅋ (Q & R) ⟧ ≃ (⟦ P ⅋ Q ⟧ × ⟦ P ⅋ R ⟧)
      dist-⅋-×-≃ = dist-⅋-× P Q R
                  , record { linv = factor-×-⅋ P Q R; is-linv = factor-×-⅋-linv-dist-⅋-× P Q R
                          ; rinv = factor-×-⅋ P Q R; is-rinv = factor-×-⅋-rinv-dist-⅋-× }

      dist-⅋-&-≃ : ⟦ P ⅋ (Q & R) ⟧ ≃ ⟦ (P ⅋ Q) & (P ⅋ R) ⟧
      dist-⅋-&-≃ = dist-⅋-×-≃ ≃-∙ ≃-! &≃×
-}
module _ {{_ : FunExt}}{{_ : UA}} where
  send⅋-⊎ : ∀ {M}(P : M → ★) Q →
            Σ ★₀ λ N →
            Σ (N → Proto₀) λ R →
            Σ (⟦ send R ⟧ ≡ ⟦ Q ⟧) λ e →
            ⟦ send P ⅋ Q ⟧ ≡ (Σ M λ m → ⟦ P m    ⅋ Q ⟧)
                            ⊎ (Σ N λ n → ⟦ send P ⅋ R n ⟧)
  send⅋-⊎ P Q = ?

  ⅋-cong : ∀ P Q R → ⟦ Q ⟧ ≡ ⟦ R ⟧ → ⟦ P ⅋ Q ⟧ ≡ ⟦ P ⅋ R ⟧
  ⅋-cong end      Q R QR = QR
  ⅋-cong (recv P) Q R QR = Π=′ _ (λ m → ⅋-cong (P m) Q R QR)
  ⅋-cong (send P) end R QR = {!!}
  ⅋-cong (send P) (recv Q) R QR = {!!}
  ⅋-cong (send P) (send Q) R QR = {!!}
  {-
  ⅋-cong (send P) end      end      QR = refl
  ⅋-cong (send P) end      (recv R) QR = {!!}
  ⅋-cong (send P) end      (send R) QR = {!!}
  ⅋-cong (send P) (recv Q) end      QR = {!!}
  ⅋-cong (send P) (recv Q) (recv R) QR = Π≃ {!!} λ m → {!!}
  ⅋-cong (send P) (recv Q) (send R) QR = {!!}
  ⅋-cong (send P) (send Q) end      QR = {!!}
  ⅋-cong (send P) (send Q) (recv R) QR = {!!}
  ⅋-cong (send P) (send Q) (send R) QR = {!!}
  -}
-}
