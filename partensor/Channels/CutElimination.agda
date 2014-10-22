open import Data.Product
open import Data.Sum
open import Data.Zero
open import Relation.Binary.PropositionalEquality.NP

module partensor.Channels.CutElimination
  (ℂ : Set) where

import partensor.Channels.Proto as Proto
open Proto ℂ
import partensor.Channels.Term as Term
open Term ℂ

mutual
  cut₁ : ∀ {c M Δ Δ' G F}(d : (m : M) → Dual (G m) (F m))(l : (c , recv G) ∈ Δ)(l' : (c , send F) ∈ Δ')
    → ⟪ Δ ⟫ → ⟪ Δ' ⟫ → ⟪ Δ [ l ≔ end ] ⅋ Δ' [ l' ≔ end ] ⟫
  cut₁ d l l' p q = ?-split l p λ nl p' →
                     conv' ⅋-comm (!-split l' q λ nl' m q' →
                     conv' (⅋-comm · ⅋'-cong (sub-twice nl') (sub-twice nl))
                     (cut (d m) (in-sub nl) (in-sub nl') (p' m) q'))

  cut⊗ : ∀ {Δ Δ' A A' B B'} → Dual A A' → Dual B B' → (l : (A ⊗ B) ∈' Δ)(l' : (A' ⅋ B') ∈' Δ') →
    ⟪ Δ ⟫ → ⟪ Δ' ⟫ → ⟪ Δ [ l ≔ end ]'  ⅋ Δ' [ l' ≔ end ]' ⟫
  cut⊗ da db l l' p q = ⊗-split l p λ pa pb →
    conv' (⅋'-cong ⅋ε (⅋'-cong ⅋ε (∈⅋-≔ l')) · !' ⅋-assoc
          · ⅋'-cong ⅋-comm (⅋≔ l' · ⅋-comm · ⅋-congₗ ⅋ε))
    (cut db (right here) (right (∈⅋-snd l')) pb
            (cut da (right here) (∈⅋-fst l') pa q))

  cut : ∀ {Δ Δ' Ψ Ψ'} → Dual Ψ Ψ' → (l : Ψ ∈' Δ)(l' : Ψ' ∈' Δ')
    → ⟪ Δ ⟫ → ⟪ Δ' ⟫ → ⟪ Δ [ l ≔ end ]' ⅋ Δ' [ l' ≔ end ]' ⟫
  cut end l l' p q = conv' (⅋'-cong (≔-same l) (≔-same l')) (mix p q)
  cut (act (?! x x₁)) l l' p q = cut₁ x l l' p q
  cut (act (!? x x₁)) l l' p q = conv' ⅋-comm (cut₁ x₁ l' l q p)
  cut (⊗⅋ d d₁ d₂ d₃) l l' p q = cut⊗ d d₂ l l' p q
  cut (⅋⊗ d d₁ d₂ d₃) l l' p q = conv' ⅋-comm (cut⊗ d₁ d₃ l' l q p)

the-cut : ∀ {Δ Δ' Ψ Ψ'} → Dual Ψ Ψ' → ⟪ Δ ⅋ Ψ ⟫ → ⟪ Ψ' ⅋ Δ' ⟫ → ⟪ Δ ⅋ Δ' ⟫
the-cut Ψ p q = conv' (⅋'-cong ⅋ε (⅋-comm · ⅋ε)) (cut Ψ (right here) (left here) p q)



{-
mutual
  cut₁ : ∀ {c Δ Δ' S S'}(d : DualS S S')(l : (c , S) ∈ Δ)(l' : (c , S') ∈ Δ')
    → ⟪ Δ ⟫ → ⟪ Δ' ⟫ → ⟪ Δ [ l ≔ end ] ⅋ Δ' [ l' ≔ end ] ⟫
  cut₁ d cl cl' (wk c l p) q = wk c (left (∈'-≔' cl l act τ (λ ()))) (conv (⅋-congₗ (≔'-swap cl l act τ (λ ()) (λ ())))
    (cut₁ d (∈'-≔' l cl τ act (λ ())) cl' p q))
  cut₁ d cl cl' p (wk c l q) = wk c (right (∈'-≔' cl' l act τ (λ ()))) (conv (⅋'-congᵣ (≔'-swap cl' l act τ (λ ()) (λ ())))
    (cut₁ d cl (∈'-≔' l cl' τ act (λ ())) p q))
  cut₁ d cl cl' (pair (⊆-in tl) s p p₁) q
   with ∈'-≔' {S = end} cl tl act ten act≠⊗
      | ∈'-≔' {S = end} tl cl ten act ⊗≠act
      | ≔'-swap {M = end} {M' = end} cl tl act ten act≠⊗ ⊗≠act
  ... | ntl | ncl | sub with ∈-conv s ncl | ≔-conv {S' = end} s ncl
  ... | left gncl | sub' = pair (⊆-in (left ntl))
                              (⅋-congₗ (!' sub · sub')
                              · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
                              (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
                                (cut₁ d (left gncl) cl' p q))
                              p₁
  ... | right gncl | sub' = pair (⊆-in (left ntl))
         (⅋-congₗ (!' sub · sub') · ⅋-assoc)
         p
         (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
           (cut₁ d (left gncl) cl' p₁ q))
  cut₁ d cl cl' p (pair (⊆-in tl) s q q₁)
   with ∈'-≔' {S = end} cl' tl act ten act≠⊗
      | ∈'-≔' {S = end} tl cl' ten act ⊗≠act
      | ≔'-swap {M = end} {M' = end} cl' tl act ten act≠⊗ ⊗≠act
  ... | ntl | ncl' | sub with ∈-conv s ncl' | ≔-conv {S' = end} s ncl'
  ... | left gncl' | sub' = pair (⊆-in (right ntl))
    (⅋'-congᵣ (!' sub · sub') · !' ⅋-assoc)
    (conv (!' ⅋-assoc) (cut₁ d cl (left gncl') p q))
    q₁
  ... | right gncl' | sub' = pair (⊆-in (right ntl))
    (⅋'-congᵣ (!' sub · sub') · !' ⅋-assoc · ⅋-congₗ ⅋-comm · ⅋-assoc)
    q
    (conv (!' ⅋-assoc) (cut₁ d cl (left gncl') p q₁))
  cut₁ d cl cl' (end p) q = 𝟘-elim (∉-PEnd p cl)
  cut₁ d cl cl' p (end q) = 𝟘-elim (∉-PEnd q cl')

  cut₁ d cl cl' (input c l x) (input c' l' x₁) with same-var act act cl l | same-var act act cl' l'
  cut₁ d cl cl' (input c l x₁) (input c' l' x₂) | inj₁ (ncl , nl , s) | Q = input c (left nl) λ m
    → conv (⅋-congₗ s) (cut₁ d ncl cl' (x₁ m) (input c' l' x₂))
  cut₁ d cl cl' (input c l x₁) (input c' l' x₂) | inj₂ y | inj₁ (ncl' , nl' , s) = input c' (right nl') λ m
    → conv (⅋'-congᵣ s) (cut₁ d cl ncl' (input c l x₁) (x₂ m))
  cut₁ () cl cl' (input c l x) (input .c l' x₁) | inj₂ (refl , proj₂) | inj₂ (refl , proj₄)

  cut₁ d cl cl' (input c l p) (output c' l' m q) with same-var act act cl l | same-var act act cl' l'
  cut₁ d cl cl' (input c l p) (output c' l' m q) | inj₁ (ncl , nl , s) | Q = input c (left nl) λ m'
   → conv (⅋-congₗ s) (cut₁ d ncl cl' (p m') (output c' l' m q))
  cut₁ d cl cl' (input c l p) (output c' l' m q) | inj₂ y | inj₁ (ncl' , nl' , s) = output c' (right nl') m
    (conv (⅋'-congᵣ s) (cut₁ d cl ncl' (input c l p) q))
  cut₁ (?! d d₁) cl cl' (input c .cl p) (output .c .cl' m q) | inj₂ (refl , refl) | inj₂ (refl , refl)
    = conv (⅋'-cong (sub-twice cl) (sub-twice cl')) (cut (d m) (in-sub cl) (in-sub cl') (p m) q )


  cut₁ d cl cl' (output c l m p) (input c' l' q) with same-var act act cl l | same-var act act cl' l'
  cut₁ d cl cl' (output c l m p) (input c' l' q) | inj₁ (ncl , nl , s) | Q = output c (left nl) m
    (conv (⅋-congₗ s) (cut₁ d ncl cl' p (input c' l' q)))
  cut₁ d cl cl' (output c l m p) (input c' l' q) | inj₂ y | inj₁ (ncl' , nl' , s) = input c' (right nl') λ m' →
    conv (⅋'-congᵣ s) (cut₁ d cl ncl' (output c l m p) (q m'))
  cut₁ (!? d d₁) cl cl' (output c .cl m p) (input .c .cl' q) | inj₂ (refl , refl) | inj₂ (refl , refl)
    = conv (⅋'-cong (sub-twice cl) (sub-twice cl')) (cut (d m) (in-sub cl) (in-sub cl') p (q m))

  cut₁ d cl cl' (output c l m p) (output c' l' m₁ q) with same-var act act cl l | same-var act act cl' l'
  cut₁ d cl cl' (output c l m p) (output c' l' m₁ q) | inj₁ (ncl , nl , s) | Q = output c (left nl) m (conv (⅋-congₗ s)
    (cut₁ d ncl cl' p (output c' l' m₁ q)))
  cut₁ d cl cl' (output c l m p) (output c' l' m₁ q) | inj₂ y | inj₁ (ncl' , nl' , s) = output c' (right nl') m₁
    (conv (⅋'-congᵣ s) (cut₁ d cl ncl' (output c l m p) q))
  cut₁ () cl cl' (output c l m p) (output .c l' m₁ q) | inj₂ (refl , proj₂) | inj₂ (refl , proj₄)

  cut⊗ : ∀ {Δ Δ' A A' B B'} → Dual A A' → Dual B B' → (l : (A ⊗ B) ∈' Δ)(l' : (A' ⅋ B') ∈' Δ') →
    ⟪ Δ ⟫ → ⟪ Δ' ⟫ → ⟪ Δ [ l ≔ end ]'  ⅋ Δ' [ l' ≔ end ]' ⟫
  cut⊗ da db cl cl' (end x) q = 𝟘-elim (⊈-PEnd x (⊆-in cl))
  cut⊗ da db cl cl' (wk c l p) q = wk c (left (∈'-≔' cl l ten τ (λ ()))) (conv (⅋-congₗ (≔'-swap cl l ten τ (λ ()) (λ ()))) (cut⊗ da db (∈'-≔' l cl τ ten (λ ())) cl' p q))
  cut⊗ da db cl cl' (input c l x) q = input c (left (∈-/ (⊆-in cl) l)) λ m → conv
    (⅋-congₗ (≔'-swap cl l ten act (λ ()) (λ ())))
    (cut⊗ da db (∈'-≔' l cl act ten (λ ())) cl' (x m) q)
  cut⊗ da db cl cl' (output c l m p) q = output c (left (∈-/ (⊆-in cl) l)) m (conv
    (⅋-congₗ (≔'-swap cl l ten act (λ ()) (λ ())))
    (cut⊗ da db (∈'-≔' l cl act ten (λ ())) cl' p q))
  cut⊗ da db cl cl' (pair (⊆-in l) x p p₁) q with same-var ten ten cl l
  cut⊗ da db cl cl' (pair (⊆-in l) x₁ p p₁) q | inj₁ (ncl , nl , s) with ∈'-conv ten x₁ ncl | ≔'-conv {S' = end} ten x₁ ncl
  ... | left P | sub = pair (⊆-in (left nl)) (⅋-congₗ (!' s · sub) · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
    (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc) (cut⊗ da db (left P) cl' p q)) p₁
  ... | right P | sub
     = pair (⊆-in (left nl)) (⅋-congₗ (!' s · sub) · ⅋-assoc) p
     (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc) (cut⊗ da db (left P) cl' p₁ q ))
  cut⊗ da db cl cl' (pair (⊆-in .cl) x p p₁) q | inj₂ (refl , refl)
    = let X = cut da (right here) (∈⅋-fst cl') p q
       in conv (!' ⅋-assoc · ⅋'-cong ((⅋'-cong ⅋ε ⅋ε · ⅋-comm) · !' x) (∈⅋-≔ cl' · ≔-≈ cl' ⅋ε))
          (cut db (right here) (right (∈⅋-snd cl')) p₁ X)

  cut : ∀ {Δ Δ' Ψ Ψ'} → Dual Ψ Ψ' → (l : Ψ ∈' Δ)(l' : Ψ' ∈' Δ')
    → ⟪ Δ ⟫ → ⟪ Δ' ⟫ → ⟪ Δ [ l ≔ end ]' ⅋ Δ' [ l' ≔ end ]' ⟫
  cut end l l' p q = conv (⅋'-cong (≔-same l) (≔-same l')) (mix p q)
  cut (act x x₁) l l' p q = cut₁ x l l' p q
  cut (⊗⅋ d d₁ d₂ d₃) l l' p q = cut⊗ d d₂ l l' p q
  cut (⅋⊗ d d₁ d₂ d₃) l l' p q = conv ⅋-comm (cut⊗ d₁ d₃ l' l q p)

the-cut : ∀ {Δ Δ' Ψ Ψ'} → Dual Ψ Ψ' → ⟪ Δ ⅋ Ψ ⟫ → ⟪ Ψ' ⅋ Δ' ⟫ → ⟪ Δ ⅋ Δ' ⟫
the-cut Ψ p q = conv (⅋'-cong ⅋ε (⅋-comm · ⅋ε)) (cut Ψ (right here) (left here) p q)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
