{-# OPTIONS --copattern #-}
open import Function.NP
open import Data.Zero
open import Data.One
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality.NP

open import Session
open import Types
open import Channel
open import Terms

module Server where

infix 2 ⊢ˢ_

-- This is just to confirm that we have enough cases
telecom' : ∀ {Δ} → ⊢ᶜᶠ Δ → ⊢ˢ Δ → 𝟙
telecom' end q = _
telecom' (output l m p) q
  = telecom' p (server-input q l m)
telecom' (input l p) q
  = case server-output q l of λ { (m , s) →
      telecom' (p m) s }

module _ {Δ c} where
    ⊢ˢ-last : ∀ {A} → ⊢ˢ (Δ , c ↦ A) → ⊢ˢ (ε , c ↦ A)
    fst (server-output (⊢ˢ-last s) here) = _
    snd (server-output (⊢ˢ-last s) here) = ⊢ˢ-last (snd (server-output s here))
    server-output (⊢ˢ-last s) (there ())
    server-input (⊢ˢ-last s) here m = ⊢ˢ-last (server-input s here m)
    server-input (⊢ˢ-last s) (there ()) m

module _ {A c} where
    ⊢ˢ-init : ∀ {Δ} → ⊢ˢ (Δ , c ↦ A) → ⊢ˢ Δ
    fst (server-output (⊢ˢ-init s) l) = _
    snd (server-output (⊢ˢ-init s) l) = ⊢ˢ-init (snd (server-output s (there l)))
    server-input (⊢ˢ-init s) l m = ⊢ˢ-init (server-input s (there l) m)

module _ {Δ₀} where
    ⊢ˢ-fst : ∀ {Δ₁} → ⊢ˢ (Δ₀ ,, Δ₁) → ⊢ˢ Δ₀
    ⊢ˢ-fst {ε} s = s
    ⊢ˢ-fst {Δ₁ , d ↦ P} s = ⊢ˢ-fst {Δ₁} (⊢ˢ-init s)

module _ {c d} where
    ⊢ˢ-pair' : ∀ {A B} → ⊢ˢ (ε , c ↦ A) → ⊢ˢ (ε , d ↦ B) → ⊢ˢ (ε , c ↦ A , d ↦  B)
    server-output (⊢ˢ-pair' s₀ s₁) here =
      let (m , s') = server-output s₁ here in m , ⊢ˢ-pair' s₀ s'
    server-output (⊢ˢ-pair' s₀ s₁) (there here) =
      let (m , s') = server-output s₀ here in m , ⊢ˢ-pair' s' s₁
    server-output (⊢ˢ-pair' s₀ s₁) (there (there ()))
    server-input (⊢ˢ-pair' s₀ s₁) here m = ⊢ˢ-pair' s₀ (server-input s₁ here m)
    server-input (⊢ˢ-pair' s₀ s₁) (there here) m = ⊢ˢ-pair' (server-input s₀ here m) s₁
    server-input (⊢ˢ-pair' s₀ s₁) (there (there ())) m

⊢ˢ-pair : ∀ {Δ₀ Δ₁} → ⊢ˢ Δ₀ → ⊢ˢ Δ₁ → ⊢ˢ (Δ₀ ,, Δ₁)
server-output (⊢ˢ-pair {Δ₀} {Δ₁} s₀ s₁) {d} {M} {P} l = so
  where
    so : Σ M λ m → ⊢ˢ (Δ₀ ,, Δ₁) [ l ≔ m ]
    so with split-∈-,, Δ₁ l
    so | inl (r , e) with server-output s₀ r
    so | inl (r , e) | (m , s') = m , tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair s' s₁)
    so | inr (r , e) with server-output s₁ r
    so | inr (r , e) | (m , s') = m , tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair s₀ s')
server-input (⊢ˢ-pair {Δ₀} {Δ₁} s₀ s₁) {d} {M} {P} l m = si
  where
    si : ⊢ˢ (Δ₀ ,, Δ₁) [ l ≔ m ]
    si with split-∈-,, Δ₁ l
    ... | inl (r , e) = tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair (server-input s₀ r m) s₁)
    ... | inr (r , e) = tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair s₀ (server-input s₁ r m))


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
