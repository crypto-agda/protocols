{-# OPTIONS --copatterns #-}
open import Data.Product
open import Data.Zero
open import Data.Sum
open import Relation.Binary.PropositionalEquality.NP

module partensor.Channels.Term
  (ℂ : Set) where

import partensor.Channels.Proto as Proto
open Proto ℂ

data ⟪_⟫ : (Δ : Proto) → Set₁ where
  end : ∀ {Δ} → PEnded Δ → ⟪ Δ ⟫

  input : ∀ c {Δ M P} (l : (c , recv P) ∈ Δ)
    → ((m : M) → ⟪ Δ [ l ≔ P m ] ⟫)
    → ⟪ Δ ⟫

  output : ∀ c {Δ M P} (l : (c , send P) ∈ Δ)
    → (m : M) → ⟪ Δ [ l ≔ P m ] ⟫
    → ⟪ Δ ⟫

  wk : ∀ c {Δ}(l : τ c ∈' Δ) → ⟪ Δ [ l ≔ end ]' ⟫ → ⟪ Δ ⟫

  pair : ∀ {Δ Γ Γ' A B}
    → (l : A ⊗ B ⊆ Δ) → (Δ / l) ≈' (Γ ⅋ Γ')
    → ⟪ Γ ⅋ A ⟫ → ⟪ Γ' ⅋ B ⟫
    → ⟪ Δ ⟫

conv' : ∀ {P Q} → P ≈' Q → ⟪ P ⟫ → ⟪ Q ⟫
conv' e (end x) = end (≈'-PEnd e x)
conv' e (wk c l p) = wk c (∈'-conv τ e l) (conv' (≔'-conv τ e l) p)
conv' e (input c l x) = input c (∈-conv e l) (λ m → conv' (≔-conv e l) (x m))
conv' e (output c l m p) = output c (∈-conv e l) m (conv' (≔-conv e l) p)
conv' e (pair l x p p₁) = pair (⊆-conv e l ) (!' /-conv e l · x) p p₁

mutual
  fwd-S : ∀ c {S S'} → DualS S S' → ⟪ act c S ⅋ act c S' ⟫
  fwd-S c (?! P P')
    = input c (left here) λ m →
      output c (right here) m (fwd (P m))
  fwd-S c (!? P P')
    = input c (right here) λ m →
      output c (left here) m (fwd (P m))

  fwd : ∀ {Γ Γ'} → Dual Γ Γ' → ⟪ Γ ⅋ Γ' ⟫
  fwd end = end (P⅋ ε ε)
  fwd (act {c} x) = fwd-S c x
  fwd (⊗⅋ Γ Γ₁ Γ₂ Γ₃)
    = pair (⊆-in (left here)) (⅋-comm · ⅋ε) (conv' ⅋-comm (fwd Γ)) (conv' ⅋-comm (fwd Γ₂))
  fwd (⅋⊗ Γ Γ₁ Γ₂ Γ₃)
    = pair (⊆-in (right here)) ⅋ε (fwd Γ) (fwd Γ₂)

mix : ∀ {P Q} → ⟪ P ⟫ → ⟪ Q ⟫ → ⟪ P ⅋ Q ⟫
mix (end x) q = conv' (⅋ε' · ⅋-comm · ⅋-congₗ (PEnd-≈' ε x)) q
mix (wk c l p) q = wk c (left l) (mix p q)
mix (input c l x) q = input c (left l) λ m → mix (x m) q
mix (output c l m p) q = output c (left l) m (mix p q)
mix (pair (⊆-in l) x p p₁) q = pair (⊆-in (left l)) (⅋-congₗ x · ⅋-assoc)
  p (conv' (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc) (mix p₁ q))

end' : ∀ {Δ} → PEnded' Δ → ⟪ Δ ⟫
end' ε = end ε
end' (P⅋ p p₁) = mix (end' p) (end' p₁)
end' (P⊗ p p₁) = pair (⊆-in here) ⅋ε' (conv' (⅋ε' · ⅋-comm) (end' p)) (conv' (⅋ε' · ⅋-comm) (end' p₁))

module _ {C Δ'} where

  record Cont Γ : Set₁ where
    field
      ⊗-cont : ∀ {A B Γ₀ Γ₁} → Γ ≡ A ⊗ B → ⟪ Γ₀ ⅋ A ⟫ → ⟪ Γ₁ ⅋ B ⟫ → ⟪ (Γ₀ ⅋ Γ₁) ⅋ (C ⅋ Δ') ⟫
      ?-cont : ∀ {M c P Γ'} → Γ ≡ act c (com IN {M} P) → (l : Γ ∈' Γ') → (∀ m →  ⟪ Γ' [ l ≔ P m ]' ⟫) → ⟪ Γ' [ l ≔ C ]' ⅋ Δ' ⟫
      !-cont : ∀ {M P c Γ'} → Γ ≡ act c (com OUT {M} P) → (l : Γ ∈' Γ') → ∀ m →  ⟪ Γ' [ l ≔ P m ]' ⟫ → ⟪ Γ' [ l ≔ C ]' ⅋ Δ' ⟫
      τ-cont : ∀ {c Γ'} → Γ ≡ τ c → (l : Γ ∈' Γ') → ⟪ Γ' [ l ≔ C ]' ⅋ Δ' ⟫
  open Cont


  split : ∀ {Δ Γ}
    (np : NotPar Γ)
    (cont : Cont Γ)
    (l : Γ ∈' Δ) → ⟪ Δ ⟫ → ⟪ Δ [ l ≔ C ]' ⅋ Δ' ⟫
  split np cont l (end x) = 𝟘-elim (∉-End-np np x l)

  split np cont l (wk c l₁ p) with same-var np τ l l₁
  split np cont l (wk c l₁ p) | inj₁ (nl , nl₁ , s) = wk c (left nl₁) (conv' (⅋-congₗ s) (split np cont nl p))
  split np cont l (wk c .l p) | inj₂ (refl , refl) = τ-cont cont refl l

  split np cont l (input c l₁ x) with same-var np act l l₁
  split np cont l (input c l₁ x₁) | inj₁ (nl , nl₁ , s)
    = input c (left nl₁) (λ m → conv' (⅋-congₗ s)
        (split np cont nl (x₁ m)))
  split np cont l (input c .l x) | inj₂ (refl , refl)
    = ?-cont cont refl l x

  split np cont l (output c l₁ m p) with same-var np act l l₁
  split np cont l (output c l₁ m p) | inj₁ (nl , nl₁ , s)
    = output c (left nl₁) m (conv' (⅋-congₗ s)
        (split np cont nl p))
  split np cont l (output c .l m p) | inj₂ (refl , refl)
    = !-cont cont refl l m p

  split np cont l (pair (⊆-in l₁) x p p₁) with same-var np ten l l₁
  split np cont l (pair (⊆-in l₁) x₁ p p₁) | inj₁ (nl , nl₁ , s)
    with ∈'-conv np x₁ nl | ≔'-conv {S' = C} np x₁ nl
  ... | here    | S' = 𝟘-elim (np-par np)
  ... | left P  | S' = pair (⊆-in (left nl₁))
      (⅋-congₗ (!' s · S') · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
       (conv' (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
          (split np cont (left P) p))
       p₁
  ... | right P | S' = pair (⊆-in (left nl₁))
      (⅋-congₗ (!' s · S') · ⅋-assoc)
        p
        (conv' (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
            (split np cont (left P) p₁))
  split np cont l (pair (⊆-in .l) x p p₁) | inj₂ (refl , refl) = conv' (!' (⅋-congₗ (⅋≔ l · ⅋-congₗ x) · ⅋-assoc)) (⊗-cont cont refl p p₁)

  module _ {c M P} where

    ?-split : ∀ {Δ}
      (l : act c (com IN {M} P) ∈' Δ) → ⟪ Δ ⟫ →
      (?-cont : ∀ {Γ'} → (l : act c (com IN {M} P) ∈' Γ') → (∀ m →  ⟪ Γ' [ l ≔ P m ]' ⟫) → ⟪ Γ' [ l ≔ C ]' ⅋ Δ' ⟫)
      → ⟪ Δ [ l ≔ C ]' ⅋ Δ' ⟫
    ?-split l p cont = split act ?-Cont l p
      where
       ?-Cont : Cont (act c (com IN {M} P))
       ⊗-cont ?-Cont ()
       ?-cont ?-Cont refl = cont
       !-cont ?-Cont ()
       τ-cont ?-Cont ()

    !-split : ∀ {Δ}
      (l : act c (com OUT {M} P) ∈' Δ) → ⟪ Δ ⟫ →
      (?-cont : ∀ {Γ'} → (l : act c (com OUT {M} P) ∈' Γ') → ∀ m →  ⟪ Γ' [ l ≔ P m ]' ⟫ → ⟪ Γ' [ l ≔ C ]' ⅋ Δ' ⟫)
      → ⟪ Δ [ l ≔ C ]' ⅋ Δ' ⟫
    !-split l p cont = split act !-Cont l p
      where
       !-Cont : Cont (act c (com OUT {M} P))
       ⊗-cont !-Cont ()
       ?-cont !-Cont ()
       !-cont !-Cont refl = cont
       τ-cont !-Cont ()
  module _ {A B} where
    ⊗-split : ∀ {Δ}
      (l : A ⊗ B ∈' Δ) → ⟪ Δ ⟫ →
      (⊗-cont : ∀ {Γ₀ Γ₁} → ⟪ Γ₀ ⅋ A ⟫ → ⟪ Γ₁ ⅋ B ⟫ → ⟪ (Γ₀ ⅋ Γ₁) ⅋ (C ⅋ Δ') ⟫)
      → ⟪ Δ [ l ≔ C ]' ⅋ Δ' ⟫
    ⊗-split l p cont = split ten ⊗-Cont l p
      where
        ⊗-Cont : Cont (A ⊗ B)
        ⊗-cont ⊗-Cont refl = cont
        ?-cont ⊗-Cont ()
        !-cont ⊗-Cont ()
        τ-cont ⊗-Cont ()


_⊗,_ : ∀ {P Q} → ⟪ P ⟫ → ⟪ Q ⟫ → ⟪ P ⊗ Q ⟫
p ⊗, q = pair (⊆-in here) (!' ⅋ε) (conv' (⅋ε' · ⅋-comm) p)
                                  (conv' (⅋ε' · ⅋-comm) q)

{-
⊗-fst : ∀ {P Q} → ⟪ P ⊗ Q ⟫ → ⟪ P ⟫
⊗-fst (end ())
⊗-fst (input c () x)
⊗-fst (output c () m pq)
⊗-fst (wk c () pq)
⊗-fst (pair (⊆-in here) x₁ pq pq₁) = {!!}


⊗-snd : ∀ {P Q} → ⟪ P ⊗ Q ⟫ → ⟪ Q ⟫
⊗-snd (end ())
⊗-snd (input c () x)
⊗-snd (output c () m pq)
⊗-snd (wk c () pq)
⊗-snd (pair (⊆-in here) x₁ pq pq₁) = {!!}

conv⅋ : ∀ {P Q R} → P ≈ Q → ⟪ P ⅋ R ⟫ → ⟪ Q ⅋ R ⟫
conv⅋ (e · e₁) pr = conv⅋ e₁ (conv⅋ e pr)
conv⅋ (⅋-congₗ e) pr = conv' (!' ⅋-assoc)
  (conv⅋ e (conv' ⅋-assoc pr))
conv⅋ ⅋ε pr = conv' (⅋-congₗ ⅋ε) pr
conv⅋ ⅋ε' pr = conv' (⅋-congₗ ⅋ε') pr
conv⅋ ⅋-comm pr = conv' (⅋-congₗ ⅋-comm) pr
conv⅋ ⅋-assoc pr = conv' (⅋-congₗ ⅋-assoc) pr
conv⅋ (⊗-congₗ e) pr = {!!}
conv⅋ ⊗ε pr = {!!}
conv⅋ ⊗ε' pr = pair (⊆-in (left here)) ⅋-comm
  (conv' ⅋-comm pr) (end (P⅋ ε ε))
conv⅋ ⊗-comm pr = conv' (⅋-assoc · ⅋'-congᵣ ⅋ε)
  (⊗-split (left here) pr (λ p q →
    pair (⊆-in (right (left here))) (⅋'-cong ⅋-comm ⅋ε · ⅋ε) q p))
conv⅋ ⊗-assoc pr = {!!}

conv : ∀ {P Q} → P ≈ Q → ⟪ P ⟫ → ⟪ Q ⟫
conv e p = conv' ⅋ε (conv⅋ e (conv' ⅋ε' p))

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
