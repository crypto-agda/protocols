{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Type.Identities
open import Data.Product.NP using (∃;Σ;_×_;_,_;first;second)
open import Data.Sum.NP hiding ([_,_]′)
open import Data.One using (𝟙)
open import Data.LR
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; ap; coe; coe!)
open import Function.Extensionality
open import HoTT
open Equivalences

open import Control.Protocol
open import Control.Protocol.Additive
open import Control.Protocol.Sequence
open import Control.Protocol.Multiplicative

module Control.Protocol.Multiplicative.Extra where

data View-⅋-proto : Proto → Proto → ★₁ where
  end-X     : ∀ Q → View-⅋-proto end Q
  recv-X    : ∀ {M}(P : M → Proto)Q → View-⅋-proto (recv P) Q
  send-send : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⅋-proto (send P) (send Q)
  send-recv : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⅋-proto (send P) (recv Q)
  send-end  : ∀ {M}(P : M → Proto) → View-⅋-proto (send P) end

view-⅋-proto : ∀ P Q → View-⅋-proto P Q
view-⅋-proto end      Q        = end-X Q
view-⅋-proto (recv P) Q        = recv-X P Q
view-⅋-proto (send P) end      = send-end P
view-⅋-proto (send P) (recv Q) = send-recv P Q
view-⅋-proto (send P) (send Q) = send-send P Q

data View-⊗-proto : Proto → Proto → ★₁ where
  end-X     : ∀ Q → View-⊗-proto end Q
  send-X    : ∀ {M}(P : M → Proto)Q → View-⊗-proto (send P) Q
  recv-recv : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⊗-proto (recv P) (recv Q)
  recv-send : ∀ {M N}(P : M → Proto)(Q : N → Proto) → View-⊗-proto (recv P) (send Q)
  recv-end  : ∀ {M}(P : M → Proto) → View-⊗-proto (recv P) end

view-⊗-proto : ∀ P Q → View-⊗-proto P Q
view-⊗-proto end      Q        = end-X Q
view-⊗-proto (send P) Q        = send-X P Q
view-⊗-proto (recv P) end      = recv-end P
view-⊗-proto (recv P) (recv Q) = recv-recv P Q
view-⊗-proto (recv P) (send Q) = recv-send P Q


-- the terminology used for the constructor follows the behavior of the combined process
data View-⅋ : ∀ P Q → ⟦ P ⅋ Q ⟧ → ★₁ where
  sendL' : ∀ {M N}(P : M → Proto)(Q : N → Proto)(m  : M )(p : ⟦ P m ⅋ send Q ⟧) → View-⅋ (send P) (send Q) (inl m  , p)
  sendR' : ∀ {M N}(P : M → Proto)(Q : N → Proto)(n : N)(p : ⟦ send P ⅋ Q n ⟧) → View-⅋ (send P) (send Q) (inr n , p)
  recvL' : ∀ {M} (P : M → Proto) Q (p : ((m : M) → ⟦ P m ⅋ Q ⟧)) → View-⅋ (recv P) Q p
  recvR' : ∀ {M N} (P : M → Proto) (Q : N → Proto)(p : (n : N) → ⟦ send P ⅋ Q n ⟧) → View-⅋ (send P) (recv Q) p
  endL   : ∀ Q (p : ⟦ Q ⟧) → View-⅋ end Q p
  send'  : ∀ {M}(P : M → Proto)(m : M)(p : ⟦ P m ⟧) → View-⅋ (send P) end (m , p)

view-⅋ : ∀ P Q (p : ⟦ P ⅋ Q ⟧) → View-⅋ P Q p
view-⅋ end Q p = endL Q p
view-⅋ (recv P) Q p = recvL' P Q p
view-⅋ (send P) end (m , p) = send' P m p
view-⅋ (send P) (recv Q) p = recvR' P Q p
view-⅋ (send P) (send Q) (inl x , p) = sendL' P Q x p
view-⅋ (send P) (send Q) (inr y , p) = sendR' P Q y p

{-
data View-∘ : ∀ P Q R → ⟦ P ⅋ Q ⟧ → ⟦ dual Q ⅋ R ⟧ → ★₁ where
  sendLL : ∀ {M N}(P : M → Proto)(Q : N → Proto) R (m : M)(p : ⟦ P m ⅋ send Q ⟧)(q : ⟦ dual (send Q) ⅋ R ⟧)
            → View-∘ (send P) (send Q) R (inl m , p) q
  recvLL : ∀ {M} (P : M → Proto) Q R
              (p : ((m : M) → ⟦ P m ⅋ Q ⟧))(q : ⟦ dual Q ⅋ R ⟧)
            → View-∘ (recv P) Q R p q
  recvR-sendR : ∀ {MP MQ MR}ioP(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
                  (mR : MR)(p : ⟦ com ioP P ⅋ recv Q ⟧)(q : ⟦ dual (recv Q) ⅋ R mR ⟧)
                  → View-∘ (com ioP P) (recv Q) (send R) p (inr mR , q)

  recvRR : ∀ {MP MQ MR}(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
              (p : ⟦ send P ⅋ recv Q ⟧)(q : (m : MR) → ⟦ dual (recv Q) ⅋ R m ⟧)
            → View-∘ (send P) (recv Q) (recv R) p q
  sendR-recvL : ∀ {MP MQ}(P : MP → Proto)(Q : MQ → Proto)R(m : MQ)
                  (p : ⟦ send P ⅋ Q m ⟧)(q : (m : MQ) → ⟦ dual (Q m) ⅋ R ⟧)
                → View-∘ (send P) (send Q) R (inr m , p) q
  recvR-sendL : ∀ {MP MQ MR}(P : MP → Proto)(Q : MQ → Proto)(R : MR → Proto)
                  (p : (m : MQ) → ⟦ send P ⅋ Q m ⟧)(m : MQ)(q : ⟦ dual (Q m) ⅋ send R ⟧)
                → View-∘ (send P) (recv Q) (send R) p (inl m , q)
  endL : ∀ Q R
          → (q : ⟦ Q ⟧)(qr : ⟦ dual Q ⅋ R ⟧)
          → View-∘ end Q R q qr
  sendLM : ∀ {MP}(P : MP → Proto)R
              (m : MP)(p : ⟦ P m ⟧)(r : ⟦ R ⟧)
            → View-∘ (send P) end R (m , p) r
  recvL-sendR : ∀ {MP MQ}(P : MP → Proto)(Q : MQ → Proto)
                  (m : MQ)(p : ∀ m → ⟦ send P ⅋ Q m ⟧)(q : ⟦ dual (Q m) ⟧)
                → View-∘ (send P) (recv Q) end p (m , q)

view-∘ : ∀ P Q R (pq : ⟦ P ⅋ Q ⟧)(qr : ⟦ dual Q ⅋ R ⟧) → View-∘ P Q R pq qr
view-∘ P Q R pq qr = view-∘-view (view-⅋ P Q pq) (view-⅋ (dual Q) R qr)
  where
  view-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ Q ⟧}{qr : ⟦ dual Q ⅋ R ⟧} → View-⅋ P Q pq → View-⅋ (dual Q) R qr → View-∘ P Q R pq qr
  view-∘-view (sendL' _ _ _ _) _                 = sendLL _ _ _ _ _ _
  view-∘-view (recvL' _ _ _)   _                 = recvLL _ _ _ _ _
  view-∘-view (sendR' _ _ _ _) _                 = sendR-recvL _ _ _ _ _ _
  view-∘-view (recvR' _ _ _)   (sendL' ._ _ _ _) = recvR-sendL _ _ _ _ _ _
  view-∘-view (recvR' _ _ _)   (sendR' ._ _ _ _) = recvR-sendR _ _ _ _ _ _ _
  view-∘-view (recvR' _ _ _)   (recvR' ._ _ _)   = recvRR _ _ _ _ _
  view-∘-view (recvR' _ _ _)   (send' ._ _ _)    = recvL-sendR _ _ _ _ _
  view-∘-view (endL _ _)       _                 = endL _ _ _ _
  view-∘-view (send' _ _ _)    _                 = sendLM _ _ _ _ _

module _ {{_ : FunExt}}{{_ : UA}} where
    ⅋-∘ : ∀ P Q R → ⟦ P ⅋ Q ⟧ → ⟦ dual Q ⅋ R ⟧ → ⟦ P ⅋ R ⟧
    ⅋-∘ P Q R pq qr = ⅋-∘-view (view-∘ P Q R pq qr)
      where
      ⅋-∘-view : ∀ {P Q R}{pq : ⟦ P ⅋ Q ⟧}{qr : ⟦ dual Q ⅋ R ⟧} → View-∘ P Q R pq qr → ⟦ P ⅋ R ⟧
      ⅋-∘-view (sendLL P Q R m p qr)          = ⅋-sendL R m (⅋-∘ (P m) (send Q) R p qr)
      ⅋-∘-view (recvLL P Q R p qr)            = λ m → ⅋-∘ (P m) Q R (p m) qr
      ⅋-∘-view (recvR-sendR ioP P Q R m pq q) = ⅋-sendR (com ioP P) m (⅋-∘ (com ioP P) (recv Q) (R m) pq q)
      ⅋-∘-view (recvRR P Q R pq q)            = λ m → ⅋-∘ (send P) (recv Q) (R m) pq (q m)
      ⅋-∘-view (sendR-recvL P Q R m p q)      = ⅋-∘ (send P) (Q m) R p (q m)
      ⅋-∘-view (recvR-sendL P Q R p m q)      = ⅋-∘ (send P) (Q m) (send R) (p m) q
      ⅋-∘-view (endL Q R pq qr)               = ⊸-apply {Q} {R} qr pq
      ⅋-∘-view (sendLM P R m pq qr)           = ⅋-sendL R m (par (P m) R pq qr)
      ⅋-∘-view (recvL-sendR P Q m pq qr)      = ⅋-∘ (send P) (Q m) end (pq m) (coe! (ap ⟦_⟧ (⅋-endR (dual (Q m)))) qr)
-}


module _ {{_ : FunExt}} {{_ : UA}} where
    ⅋-compose : ∀ P Q R → ⟦ P ⅋ Q ⟧ → ⟦ dual P ⅋ R ⟧ → ⟦ Q ⅋ R ⟧
    ⅋-compose end Q R pq pr = par Q R pq pr
    ⅋-compose (send P) end R (m , pq) pr = ⊸-apply {P m} {R} (pr m) pq
    ⅋-compose (send P) (send Q) R (inl m , pq) pr = ⅋-compose (P m) (send Q) R pq (pr m)
    ⅋-compose (send P) (send Q) R (inr m , pq) pr = ⅋-sendL R m (⅋-compose (send P) (Q m) R pq pr)
    ⅋-compose (send P) (recv Q) R pq pr = λ m → ⅋-compose (send P) (Q m) R (pq m) pr
    ⅋-compose (recv P) Q end pq pr = {!λ m → ⅋-compose (recv P) Q (R m) pq (pr m)!}
    ⅋-compose (recv P) Q (recv R) pq pr = {!λ m → ⅋-compose (recv P) Q (R m) pq (pr m)!}
    ⅋-compose (recv P) Q (send R) pq (inl m , pr) = {!!}
    ⅋-compose (recv P) Q (send R) pq (inr m , pr) = {!inr m , ⅋-compose (recv P) Q (R m) pq pr!}
--    ⅋-compose (recv P) (recv Q) R pq pr = λ m → ⅋-compose (recv P) (Q m) R (λ n → coe (⅋-comm (Q m) (P n)) (coe (⅋-comm (P n) (recv Q)) (pq n) m)) pr

{-
-- use coe (... ⅋-assoc P Q R)
⅋-assoc : ∀ P Q R → ⟦ P ⅋ (Q ⅋ R) ⟧ → ⟦ (P ⅋ Q) ⅋ R ⟧
⅋-assoc end      Q        R         s                 = s
⅋-assoc (recv P) Q        R         s m               = ⅋-assoc (P m) _ _ (s m)
⅋-assoc (send P) end      R         s                 = s
u⅋-assoc (send P) (recv Q) R         s m               = ⅋-assoc (send P) (Q m) _ (s m)
⅋-assoc (send P) (send Q) end       s                 = s
⅋-assoc (send P) (send Q) (recv R)  s m               = ⅋-assoc (send P) (send Q) (R m) (s m)
⅋-assoc (send P) (send Q) (send R) (inl m , s)       = inl (inl m) , ⅋-assoc (P m) (send Q) (send R) s
⅋-assoc (send P) (send Q) (send R) (inr (inl m) , s) = inl (inr m) , ⅋-assoc (send P) (Q m) (send R) s
⅋-assoc (send P) (send Q) (send R) (inr (inr m) , s) = inr m       , ⅋-assoc (send P) (send Q) (R m) s

-- use coe (⅋-endR P) instead
⅋-rend : ∀ P → ⟦ P ⅋ end ⟧  → ⟦ P ⟧
⅋-rend end      p = p
⅋-rend (send _) p = p
⅋-rend (recv P) p = λ m → ⅋-rend (P m) (p m)

-- use coe! (⅋-endR P) instead
⅋-rend! : ∀ P  → ⟦ P ⟧ → ⟦ P ⅋ end ⟧
⅋-rend! end      p = p
⅋-rend! (send _) p = p
⅋-rend! (recv P) p = λ m → ⅋-rend! (P m) (p m)

-- use coe! (⅋-recvR P Q) instead
⅋-isendR : ∀ {N} P Q → ⟦ P ⅋ recv Q ⟧ → (n : N) → ⟦ P ⅋ Q n ⟧
⅋-isendR end Q s n = s n
⅋-isendR (recv P) Q s n = λ m → ⅋-isendR (P m) Q (s m) n
⅋-isendR (send P) Q s n = s n


-- see ⅋-recvR
⅋-recvR : ∀ {M} P Q → ((m : M) → ⟦ P ⅋ Q m ⟧) → ⟦ P ⅋ recv Q ⟧
⅋-recvR end      Q s = s
⅋-recvR (recv P) Q s = λ x → ⅋-recvR (P x) Q (λ m → s m x)
⅋-recvR (send P) Q s = s
-}


{-
module _ {{_ : FunExt}}{{_ : UA}} where
  Log-⅋-⊗ : ∀ P Q → Log (P ⅋ Q) ≡ Log (dual P ⊗ dual Q)
  {-
  Log-⅋-⊗ end      Q        = {!!}
  Log-⅋-⊗ (recv P) Q        = {!!}
  Log-⅋-⊗ (send P) end      = {!Σ=′ _ λ m → ?!}
  Log-⅋-⊗ (send P) (recv Q) = {!Σ=′ _ λ m → ?!}
  Log-⅋-⊗ (send P) (send Q) = {!!}
  -}
  Log-⅋-⊗ P Q = Log (P ⅋ Q)
            ≡⟨ {!!} ⟩
              Log (dual (P ⅋ Q))
            ≡⟨ {!!} ⟩
              Log (dual P ⊗ dual Q)
            ∎
  where open ≡-Reasoning
  -}

                                                {-
  Log-⅋-× : ∀ P Q → Log (P ⅋ Q) ≡ (Log P × Log Q)
  Log-⅋-× end      Q        = {!!}
  Log-⅋-× (recv P) Q        = Σ=′ _ (λ m → Log-⅋-× {P m} {Q}) ∙ Σ-assoc
  Log-⅋-× (send P) end      = {!!}
  Log-⅋-× (send P) (recv Q) = {!? ∙ ΣΣ-comm!} ∙ Σ-assoc
  Log-⅋-× (send P) (send Q) = {!!}
  -}


-- P ⟦⊗⟧ Q ≃ ⟦ P ⊗ Q ⟧
-- but potentially more convenient
_⟦⊗⟧_ : Proto → Proto → ★
end    ⟦⊗⟧ Q      = ⟦ Q ⟧
send P ⟦⊗⟧ Q      = ∃ λ m → P m ⟦⊗⟧ Q
P      ⟦⊗⟧ end    = ⟦ P ⟧
P      ⟦⊗⟧ send Q = ∃ λ m → P ⟦⊗⟧ Q m
recv P ⟦⊗⟧ recv Q = (Π _ λ m → P m    ⟦⊗⟧ recv Q)
                  × (Π _ λ n → recv P ⟦⊗⟧ Q n)

module _ {{_ : FunExt}}{{_ : UA}} where
  ⟦⊗⟧-correct : ∀ P Q → P ⟦⊗⟧ Q ≡ ⟦ P ⊗ Q ⟧
  ⟦⊗⟧-correct end      Q        = refl
  ⟦⊗⟧-correct (send P) Q        = Σ=′ _ λ m → ⟦⊗⟧-correct (P m) Q
  ⟦⊗⟧-correct (recv P) end      = refl
  ⟦⊗⟧-correct (recv P) (send Q) = Σ=′ _ λ n → ⟦⊗⟧-correct (recv P) (Q n)
  ⟦⊗⟧-correct (recv P) (recv Q) = ! dist-×-Π
                                ∙ Π=′ (_ ⊎ _) λ { (inl m)  → ⟦⊗⟧-correct (P m) (recv Q)
                                                ; (inr n) → ⟦⊗⟧-correct (recv P) (Q n) }

-- an alternative, potentially more convenient
_⟦⅋⟧_ : Proto → Proto → ★
end    ⟦⅋⟧ Q      = ⟦ Q ⟧
recv P ⟦⅋⟧ Q      = ∀ m → P m ⟦⅋⟧ Q
P      ⟦⅋⟧ end    = ⟦ P ⟧
P      ⟦⅋⟧ recv Q = ∀ n → P ⟦⅋⟧ Q n
send P ⟦⅋⟧ send Q = (∃ λ m → P m    ⟦⅋⟧ send Q)
                  ⊎ (∃ λ n → send P ⟦⅋⟧ Q n)

module _ {{_ : FunExt}}{{_ : UA}} where
  ⟦⅋⟧-correct : ∀ P Q → P ⟦⅋⟧ Q ≡ ⟦ P ⅋ Q ⟧
  ⟦⅋⟧-correct end      Q        = refl
  ⟦⅋⟧-correct (recv P) Q        = Π=′ _ λ m → ⟦⅋⟧-correct (P m) Q
  ⟦⅋⟧-correct (send P) end      = refl
  ⟦⅋⟧-correct (send P) (recv Q) = Π=′ _ λ n → ⟦⅋⟧-correct (send P) (Q n)
  ⟦⅋⟧-correct (send P) (send Q) = ! dist-⊎-Σ
                                ∙ Σ=′ (_ ⊎ _) λ { (inl m) → ⟦⅋⟧-correct (P m) (send Q)
                                                ; (inr n) → ⟦⅋⟧-correct (send P) (Q n) }


  {-
  foo : ∀ M N (P : M → N → Proto) → (recvE M λ m → recvE N λ n → P m n) ≡ (recvE N λ n → recvE M λ m → P m n)
  foo = λ M N P → {!!}
  ⅋-recvR : ∀ P{M}(Q : M → Proto) → P ⅋ recv Q ≡ recv λ m → P ⅋ Q m
  ⅋-recvR end      Q = refl
  ⅋-recvR (send P) Q = refl
  ⅋-recvR (recv P) Q = (recv=′ λ m → ⅋-recvR (P m) Q) ∙ {!!}

  ⅋-comm : ∀ P Q → P ⅋ Q ≡ Q ⅋ P
  ⅋-comm end      Q        = ! ⅋-endR Q
  ⅋-comm (recv P) Q        = recv=′ (λ m → ⅋-comm (P m) Q) ∙ ! ⅋-recvR Q P
  ⅋-comm (send P) end      = refl
  ⅋-comm (send P) (recv Q) = recv=′ λ m → ⅋-comm (send P) (Q m)
  ⅋-comm (send P) (send Q) = send≃ ⊎-comm-equiv [inl: (λ m → ⅋-comm (P m) (send Q))
                                                ,inr: (λ m → ⅋-comm (send P) (Q m)) ]
  -}
{-
⅋-⊗-com' : ∀ P Q {M}(R : M → Proto)(m : M) → ⟦ P ⅋ (Q ⊗ recv R) ⟧ → ⟦ P ⅋ (Q ⊗ R m) ⟧
⅋-⊗-com' end      Q        R m t = {!!}
⅋-⊗-com' (recv P) Q        R m t = λ n → ⅋-⊗-com' (P n) Q R m (t n)
⅋-⊗-com' (send P) end      R m t = t m
⅋-⊗-com' (send P) (recv Q) R m t = t (inr m)
⅋-⊗-com' (send P) (send Q) R m (inl n , t) = {!!}
⅋-⊗-com' (send P) (send Q) R m (inr n , t) = {!!}

⅋-⊗-com : ∀ P Q → ⟦ P ⅋ (Q ⊗ dual Q) ⟧ → ⟦ P ⅋ source-of Q ⟧
⅋-⊗-com end Q t = telecom Q {!!} {!!}
⅋-⊗-com (recv P) Q t = λ m → ⅋-⊗-com (P m) Q (t m)
⅋-⊗-com (send P) end t = t
⅋-⊗-com (send P) (send Q) (inl m , t) = inl m , ⅋-⊗-com (P m) (send Q) t
⅋-⊗-com (send P) (send Q) (inr m , t) = inr m , ⅋-⊗-com (send P) (Q m) (⅋-⊗-com' (send P) (Q m) (dual ∘ Q) m t)
⅋-⊗-com (send P) (recv Q) (inl m , t) = inl m , ⅋-⊗-com (P m) (recv Q) t
⅋-⊗-com (send P) (recv Q) (inr m , t) = inr m , ⅋-⊗-com (send P) (Q m) {!⅋-⊗-com' (send P) (dual (Q m)) Q m t!}
-}

{-
⅋-⊗-com : ∀ P Q → ⟦ P ⅋ (Q ⊗ dual Q) ⟧ → ⟦ P ⟧
⅋-⊗-com end Q t = end -- HERE WE DID NOT DO ANY COM
⅋-⊗-com (recv P) Q t = λ m → ⅋-⊗-com (P m) Q (t m)
⅋-⊗-com (send P) end t = t
⅋-⊗-com (send P) (send Q) (inl m , t) = m , ⅋-⊗-com (P m) (send Q) t
⅋-⊗-com (send P) (send Q) (inr m , t) = ⅋-⊗-com (send P) (Q m) {!t m !}
⅋-⊗-com (send P) (recv Q) (inl m , t) = m , ⅋-⊗-com (P m) (recv Q) t
⅋-⊗-com (send P) (recv Q) (inr m , t) = {!!}
-}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
