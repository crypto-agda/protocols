{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Data.Product.NP renaming (proj₁ to fst; proj₂ to snd) using (∃;Σ;_×_;_,_;first;second)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_]) hiding ([_,_]′)
open import Data.One using (𝟙)
open import Data.LR
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; subst; ap; coe; coe!)
open import Function.Extensionality
open import HoTT
open Equivalences

open import Control.Protocol
open import Control.Protocol.Additive
open import Control.Protocol.Sequence

module Control.Protocol.Multiplicative where

_⅋_ : Proto → Proto → Proto
end    ⅋ Q      = Q
recv P ⅋ Q      = recv λ m → P m ⅋ Q
P      ⅋ end    = P
P      ⅋ recv Q = recv λ m → P ⅋ Q m
send P ⅋ send Q = send [inl: (λ m → P m ⅋ send Q)
                       ,inr: (λ n → send P ⅋ Q n) ]

_⊗_ : Proto → Proto → Proto
end    ⊗ Q      = Q
send P ⊗ Q      = send λ m → P m ⊗ Q
P      ⊗ end    = P
P      ⊗ send Q = send λ m → P ⊗ Q m
recv P ⊗ recv Q = recv [inl: (λ m → P m ⊗ recv Q)
                       ,inr: (λ n → recv P ⊗ Q n) ]

module _ {{_ : FunExt}}{{_ : UA}} where
  -- absorption
  ⊤-⅋ : ∀ P → ⟦ P⊤ ⅋ P ⟧
  ⊤-⅋ P = λ()

_⊸_ : (P Q : Proto) → Proto
P ⊸ Q = dual P ⅋ Q

_o-o_ : (P Q : Proto) → Proto
P o-o Q = (P ⊸ Q) ⊗ (Q ⊸ P)

module _ {{_ : FunExt}} where
  ⊗-endR : ∀ P → P ⊗ end ≡ P
  ⊗-endR end      = refl
  ⊗-endR (recv _) = refl
  ⊗-endR (send P) = send=′ λ m → ⊗-endR (P m)

  ⅋-endR : ∀ P → P ⅋ end ≡ P
  ⅋-endR end      = refl
  ⅋-endR (send _) = refl
  ⅋-endR (recv P) = recv=′ λ m → ⅋-endR (P m)

module _ {{_ : FunExt}}{{_ : UA}} where
  ⊗-sendR : ∀ P{M}(Q : M → Proto) → ⟦ P ⊗ send Q ⟧ ≡ (Σ M λ m → ⟦ P ⊗ Q m ⟧)
  ⊗-sendR end      Q = refl
  ⊗-sendR (recv P) Q = refl
  ⊗-sendR (send P) Q = (Σ=′ _ λ m → ⊗-sendR (P m) Q) ∙ ΣΣ-comm

  ⊗-comm : ∀ P Q → ⟦ P ⊗ Q ⟧ ≡ ⟦ Q ⊗ P ⟧
  ⊗-comm end      Q        = ! ap ⟦_⟧ (⊗-endR Q)
  ⊗-comm (send P) Q        = (Σ=′ _ λ m → ⊗-comm (P m) Q) ∙ ! ⊗-sendR Q P
  ⊗-comm (recv P) end      = refl
  ⊗-comm (recv P) (send Q) = Σ=′ _ λ m → ⊗-comm (recv P) (Q m)
  ⊗-comm (recv P) (recv Q) = Π≃ ⊎-comm-equiv [inl: (λ m → ⊗-comm (P m) (recv Q))
                                              ,inr: (λ m → ⊗-comm (recv P) (Q m)) ]

  ⊗-assoc : ∀ P Q R → P ⊗ (Q ⊗ R) ≡ (P ⊗ Q) ⊗ R
  ⊗-assoc end      Q        R        = refl
  ⊗-assoc (send P) Q        R        = send=′ λ m → ⊗-assoc (P m) Q R
  ⊗-assoc (recv P) end      R        = refl
  ⊗-assoc (recv P) (send Q) R        = send=′ λ m → ⊗-assoc (recv P) (Q m) R
  ⊗-assoc (recv P) (recv Q) end      = refl
  ⊗-assoc (recv P) (recv Q) (send R) = send=′ λ m → ⊗-assoc (recv P) (recv Q) (R m)
  ⊗-assoc (recv P) (recv Q) (recv R) = recv≃ ⊎-assoc-equiv
                                            λ { (inl m)       → ⊗-assoc (P m) (recv Q) (recv R)
                                              ; (inr (inl m)) → ⊗-assoc (recv P) (Q m) (recv R)
                                              ; (inr (inr m)) → ⊗-assoc (recv P) (recv Q) (R m) }

  ⅋-recvR : ∀ P{M}(Q : M → Proto) → ⟦ P ⅋ recv Q ⟧ ≡ (Π M λ m → ⟦ P ⅋ Q m ⟧)
  ⅋-recvR end      Q = refl
  ⅋-recvR (send P) Q = refl
  ⅋-recvR (recv P) Q = (Π=′ _ λ m → ⅋-recvR (P m) Q) ∙ ΠΠ-comm

  ⅋-comm : ∀ P Q → ⟦ P ⅋ Q ⟧ ≡ ⟦ Q ⅋ P ⟧
  ⅋-comm end      Q        = ! ap ⟦_⟧ (⅋-endR Q)
  ⅋-comm (recv P) Q        = (Π=′ _ λ m → ⅋-comm (P m) Q) ∙ ! ⅋-recvR Q P
  ⅋-comm (send P) end      = refl
  ⅋-comm (send P) (recv Q) = Π=′ _ λ m → ⅋-comm (send P) (Q m)
  ⅋-comm (send P) (send Q) = Σ≃ ⊎-comm-equiv [inl: (λ m → ⅋-comm (P m) (send Q))
                                              ,inr: (λ m → ⅋-comm (send P) (Q m)) ]

  ⅋-assoc : ∀ P Q R → P ⅋ (Q ⅋ R) ≡ (P ⅋ Q) ⅋ R
  ⅋-assoc end      Q        R        = refl
  ⅋-assoc (recv P) Q        R        = recv=′ λ m → ⅋-assoc (P m) Q R
  ⅋-assoc (send P) end      R        = refl
  ⅋-assoc (send P) (recv Q) R        = recv=′ λ m → ⅋-assoc (send P) (Q m) R
  ⅋-assoc (send P) (send Q) end      = refl
  ⅋-assoc (send P) (send Q) (recv R) = recv=′ λ m → ⅋-assoc (send P) (send Q) (R m)
  ⅋-assoc (send P) (send Q) (send R) = send≃ ⊎-assoc-equiv
                                            λ { (inl m)       → ⅋-assoc (P m) (send Q) (send R)
                                              ; (inr (inl m)) → ⅋-assoc (send P) (Q m) (send R)
                                              ; (inr (inr m)) → ⅋-assoc (send P) (send Q) (R m) }

module _ {P Q R}{{_ : FunExt}} where
  dist-⊗-⊕′ : (Q ⊕ R) ⊗ P ≡ (Q ⊗ P) ⊕ (R ⊗ P)
  dist-⊗-⊕′ = send=′ [L: refl R: refl ]

  dist-⅋-&′ : (Q & R) ⅋ P ≡ (Q ⅋ P) & (R ⅋ P)
  dist-⅋-&′ = recv=′ [L: refl R: refl ]

  module _ {{_ : UA}} where
      dist-⊗-⊕ : ⟦ P ⊗ (Q ⊕ R) ⟧ ≡ ⟦ (P ⊗ Q) ⊕ (P ⊗ R) ⟧
      dist-⊗-⊕ = ⊗-comm P (Q ⊕ R)
                ∙ ap ⟦_⟧ dist-⊗-⊕′
                ∙ ⊕≡⊎
                ∙ ⊎= (⊗-comm Q P) (⊗-comm R P)
                ∙ ! ⊕≡⊎

      dist-⅋-& : ⟦ P ⅋ (Q & R) ⟧ ≡ ⟦ (P ⅋ Q) & (P ⅋ R) ⟧
      dist-⅋-& = ⅋-comm P (Q & R)
                ∙ ap ⟦_⟧ dist-⅋-&′
                ∙ &≡×
                ∙ ×= (⅋-comm Q P) (⅋-comm R P)
                ∙ ! &≡×

  -- sends can be pulled out of tensor
  source->>=-⊗ : ∀ P Q R → (source-of P >>= Q) ⊗ R ≡ source-of P >>= λ log → (Q log ⊗ R)
  source->>=-⊗ end       Q R = refl
  source->>=-⊗ (com _ P) Q R = send=′ λ m → source->>=-⊗ (P m) (Q ∘ _,_ m) R

  -- consequence[Q = const end]: ∀ P R → source-of P ⊗ R ≡ source-of P >> R

  -- recvs can be pulled out of par
  sink->>=-⅋ : ∀ P Q R → (sink-of P >>= Q) ⅋ R ≡ sink-of P >>= λ log → (Q log ⅋ R)
  sink->>=-⅋ end       Q R = refl
  sink->>=-⅋ (com _ P) Q R = recv=′ λ m → sink->>=-⅋ (P m) (Q ∘ _,_ m) R

  -- source-⅋ : source-of P ⅋ source-of Q ≡ 

  -- consequence[Q = const end]: ∀ P R → sink-of P ⅋ R ≡ sink-of P >> R

Log-⅋-× : ∀ {P Q} → Log (P ⅋ Q) → Log P × Log Q
Log-⅋-× {end}   {Q}      q           = end , q
Log-⅋-× {recv P}{Q}      (m , p)     = first  (_,_ m) $ Log-⅋-× {P m} {Q} p
Log-⅋-× {send P}{end}    (m , p)     = (m , p) , end
Log-⅋-× {send P}{recv Q} (m , p)     = second (_,_ m) $ Log-⅋-× {send P} {Q m} p
Log-⅋-× {send P}{send Q} (inl m , p) = first  (_,_ m) $ Log-⅋-× {P m} {send Q} p
Log-⅋-× {send P}{send Q} (inr m , p) = second (_,_ m) $ Log-⅋-× {send P} {Q m} p

module _ {{_ : FunExt}} where
  ⊗⅋-dual : ∀ P Q → dual (P ⅋ Q) ≡ dual P ⊗ dual Q
  ⊗⅋-dual end Q = refl
  ⊗⅋-dual (recv P) Q = com=′ _ λ m → ⊗⅋-dual (P m) _
  ⊗⅋-dual (send P) end = refl
  ⊗⅋-dual (send P) (recv Q) = com=′ _ λ n → ⊗⅋-dual (send P) (Q n)
  ⊗⅋-dual (send P) (send Q) = com=′ _
    [inl: (λ m → ⊗⅋-dual (P m) (send Q))
    ,inr: (λ n → ⊗⅋-dual (send P) (Q n)) ]

module _ {{_ : FunExt}}{{_ : UA}} where

  ⅋-sendR : ∀ {M}P{Q : M → Proto}(m : M) → ⟦ P ⅋ Q m ⟧ → ⟦ P ⅋ send Q ⟧
  ⅋-sendR end      m p = m , p
  ⅋-sendR (send P) m p = inr m , p
  ⅋-sendR (recv P) m p = λ x → ⅋-sendR (P x) m (p x)

  ⅋-sendL : ∀ {M}{P : M → Proto} Q (m : M) → ⟦ P m ⅋ Q ⟧ → ⟦ send P ⅋ Q ⟧
  ⅋-sendL {M} {P} Q m pq = coe (⅋-comm Q (send P)) (⅋-sendR Q m (coe (⅋-comm (P m) Q) pq))

  ⅋-id : ∀ P → ⟦ dual P ⅋ P ⟧
  ⅋-id end      = end
  ⅋-id (recv P) = λ x → ⅋-sendL (P x) x (⅋-id (P x))
  ⅋-id (send P) = λ x → ⅋-sendR (dual (P x)) x (⅋-id (P x))

  -- left-biased “strategy”
  par : ∀ P Q → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P ⅋ Q ⟧
  par (recv P) Q p       q = λ m → par (P m) Q (p m) q
  par (send P) Q (m , p) q = ⅋-sendL Q m (par (P m) Q p q)
  par end      Q end     q = q

⅋-apply : ∀ P Q → ⟦ P ⅋ Q ⟧ → ⟦ dual P ⟧ → ⟦ Q ⟧
⅋-apply end      Q        s           p       = s
⅋-apply (recv P) Q        s           (m , p) = ⅋-apply (P m) Q (s m) p
⅋-apply (send P) end      s           p       = _
⅋-apply (send P) (recv Q) s           p n     = ⅋-apply (send P) (Q n) (s n) p
⅋-apply (send P) (send Q) (inl m , s) p       = ⅋-apply (P m) (send Q) s (p m)
⅋-apply (send P) (send Q) (inr m , s) p       = m , ⅋-apply (send P) (Q m) s p


module _ {{_ : FunExt}}{{_ : UA}} where
⊗-pair : ∀ {P Q} → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P ⊗ Q ⟧
⊗-pair {end}    {Q}      p q       = q
⊗-pair {send P} {Q}      (m , p) q = m , ⊗-pair {P m} p q
⊗-pair {recv P} {end}    p end     = p
⊗-pair {recv P} {send Q} p (m , q) = m , ⊗-pair {recv P} {Q m} p q
⊗-pair {recv P} {recv Q} p q       = [inl: (λ m → ⊗-pair {P m}    {recv Q} (p m) q)
                                      ,inr: (λ n → ⊗-pair {recv P} {Q n}    p     (q n)) ]

⊗-fst : ∀ P Q → ⟦ P ⊗ Q ⟧ → ⟦ P ⟧
⊗-fst end      Q        pq       = _
⊗-fst (send P) Q        (m , pq) = m , ⊗-fst (P m) Q pq
⊗-fst (recv P) end      pq       = pq
⊗-fst (recv P) (send Q) (_ , pq) = ⊗-fst (recv P) (Q _) pq
⊗-fst (recv P) (recv Q) pq       = λ m → ⊗-fst (P m) (recv Q) (pq (inl m))

⊗-snd : ∀ P Q → ⟦ P ⊗ Q ⟧ → ⟦ Q ⟧
⊗-snd end      Q        pq       = pq
⊗-snd (send P) Q        (_ , pq) = ⊗-snd (P _) Q pq
⊗-snd (recv P) end      pq       = end
⊗-snd (recv P) (send Q) (m , pq) = m , ⊗-snd (recv P) (Q m) pq
⊗-snd (recv P) (recv Q) pq       = λ m → ⊗-snd (recv P) (Q m) (pq (inr m))

module _ {{_ : FunExt}} where
    ⊗-pair-fst : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → ⊗-fst P Q (⊗-pair {P} {Q} p q) ≡ p
    ⊗-pair-fst end      Q        p q       = refl
    ⊗-pair-fst (send P) Q        (m , p) q = pair= refl (⊗-pair-fst (P m) Q p q)
    ⊗-pair-fst (recv P) end      p q       = refl
    ⊗-pair-fst (recv P) (send Q) p (m , q) = ⊗-pair-fst (recv P) (Q m) p q
    ⊗-pair-fst (recv P) (recv Q) p q       = λ= λ m → ⊗-pair-fst (P m) (recv Q) (p m) q

    ⊗-pair-snd : ∀ P Q (p : ⟦ P ⟧)(q : ⟦ Q ⟧) → ⊗-snd P Q (⊗-pair {P} {Q} p q) ≡ q
    ⊗-pair-snd end      Q        p q       = refl
    ⊗-pair-snd (send P) Q        (m , p) q = ⊗-pair-snd (P m) Q p q
    ⊗-pair-snd (recv P) end      p q       = refl
    ⊗-pair-snd (recv P) (send Q) p (m , q) = pair= refl (⊗-pair-snd (recv P) (Q m) p q)
    ⊗-pair-snd (recv P) (recv Q) p q       = λ= λ m → ⊗-pair-snd (recv P) (Q m) p (q m)

module _ P Q where
  ⊗→× : ⟦ P ⊗ Q ⟧ → ⟦ P ⟧ × ⟦ Q ⟧
  ⊗→× pq = ⊗-fst P Q pq , ⊗-snd P Q pq

  ×→⊗ : ⟦ P ⟧ × ⟦ Q ⟧ → ⟦ P ⊗ Q ⟧
  ×→⊗ (p , q) = ⊗-pair {P} {Q} p q

  module _ {{_ : FunExt}} where
    ×→⊗→× : ×→⊗ RightInverseOf ⊗→×
    ×→⊗→× = λ { (x , y) → pair×= (⊗-pair-fst P Q x y) (⊗-pair-snd P Q x y) }

    ⊗→×-has-rinv : Rinv ⊗→×
    ⊗→×-has-rinv = record { rinv = ×→⊗ ; is-rinv = ×→⊗→× }

{- WRONG
⊗→×→⊗ : (×→⊗ P Q) LeftInverseOf (⊗→× P Q)
⊗≃×   : ⟦ P ⊗ Q ⟧ ≃ ⟦ P ⟧ × ⟦ Q ⟧
⟦⊗⟧≡× : P ⟦⊗⟧ Q ≡ (⟦ P ⟧ × ⟦ Q ⟧)
-}

module _ {{_ : FunExt}}{{_ : UA}} where
    switchL' : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧) (r : ⟦ R ⟧) → ⟦ P ⅋ (Q ⊗ R) ⟧
    switchL' end      Q        R        q            r       = ⊗-pair {Q} {R} q r
    switchL' (send P) end      R        p            r       = par (send P) R p r
    switchL' (send P) (send Q) R        (inl m , pq) r       = inl m , switchL' (P m) (send Q) R pq r
    switchL' (send P) (send Q) R        (inr m , pq) r       = inr m , switchL' (send P) (Q m) R pq r
    switchL' (send P) (recv Q) end      pq           r       = pq
    switchL' (send P) (recv Q) (send R) pq           (m , r) = inr m , switchL' (send P) (recv Q) (R m) pq r
    switchL' (send P) (recv Q) (recv R) pq           r       = [inl: (λ m → switchL' (send P) (Q m) (recv R) (pq m) r)
                                                                ,inr: (λ m → switchL' (send P) (recv Q) (R m) pq (r m)) ]
    switchL' (recv P) Q        R        pq           r       = λ m → switchL' (P m) Q R (pq m) r

    switchL : ∀ P Q R → ⟦ (P ⅋ Q) ⊗ R ⟧ → ⟦ P ⅋ (Q ⊗ R) ⟧
    switchL P Q R pqr = switchL' P Q R (⊗-fst (P ⅋ Q) R pqr) (⊗-snd (P ⅋ Q) R pqr)

    ⊸-apply : ∀ {P Q} → ⟦ dual P ⅋ Q ⟧ → ⟦ P ⟧ → ⟦ Q ⟧
    ⊸-apply {P} {Q} pq p = ⅋-apply (dual P) Q pq (subst ⟦_⟧ (! (dual-involutive P)) p)

    o-o-apply : ∀ P Q → ⟦ P o-o Q ⟧ → ⟦ P ⟧ → ⟦ Q ⟧
    o-o-apply P Q Po-oQ p = ⊸-apply {P} {Q} (⊗-fst (P ⊸ Q) (Q ⊸ P) Po-oQ) p

    o-o-comm : ∀ P Q → ⟦ P o-o Q ⟧ ≡ ⟦ Q o-o P ⟧
    o-o-comm P Q = ⊗-comm (dual P ⅋ Q) (dual Q ⅋ P)

    -- multiplicative mix (left-biased)
    mmix : ∀ P Q → ⟦ P ⊗ Q ⟧ → ⟦ P ⅋ Q ⟧
    mmix P Q pq = par P Q (⊗-fst P Q pq) (⊗-snd P Q pq)
-- -}
-- -}
-- -}
