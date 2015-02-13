open import DeepParTensor.Terms-merge renaming (conv to conv')
open import Data.Zero
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality.NP

module DeepParTensor.TermsAssoc where

module _ {C} where
  ⊗-split' : ∀ {Γ A B}(l : A ⊗ B ∈' Γ) → ⟪ Γ ⟫
    → (∀ {Γ' Γ₀ Γ₁} → Γ' ≈' Γ₀ ⅋ Γ₁ → ⟪ Γ₀ ⅋ A ⟫ → ⟪ Γ₁ ⅋ B ⟫ → ⟪ Γ' ⅋ C ⟫)
    → ⟪ Γ [ l ≔ C ]' ⟫
  ⊗-split' l (end x) f = 𝟘-elim (⊈-PEnd x (⊆-in l))
  ⊗-split' l (input l₁ x) f = input (∈'-≔' l l₁ ten act (λ ()))
    (λ m → conv' (≔'-swap l l₁ ten act (λ ()) (λ ())) (⊗-split' (∈'-≔' l₁ l act ten (λ ())) (x m) f))
  ⊗-split' l (output l₁ m p) f = output (∈'-≔' l l₁ ten act (λ ())) m
    (conv' (≔'-swap l l₁ ten act (λ ()) (λ ())) (⊗-split' (∈'-≔' l₁ l act ten (λ ())) p f))
  ⊗-split' l (pair (⊆-in l₁) x p p₁) f with same-var ten ten l l₁
  ⊗-split' l (pair (⊆-in l₁) x₁ p p₁) f | inj₁ (nl , nl₁ , s)
    with ∈'-conv ten x₁ nl | ≔'-conv {S' = C} ten x₁ nl
  ⊗-split' l (pair (⊆-in l₁) x₁ p p₁) f | inj₁ (nl , nl₁ , s)
   | left nnl | s' = pair (⊆-in nl₁)
    (!' s · s') (⊗-split' (left nnl) p f) p₁
  ⊗-split' l (pair (⊆-in l₁) x₁ p p₁) f | inj₁ (nl , nl₁ , s)
   | right nnl | s' = pair (⊆-in nl₁) (!' s · s') p (⊗-split' (left nnl) p₁ f)
  ⊗-split' l (pair (⊆-in .l) x p p₁) f | inj₂ (refl , refl) = conv' (!' (⅋≔ l)) (f x p p₁)

⊗-split : ∀ {Γ A B C} → ⟪ Γ ⅋ (A ⊗ B) ⟫
  → (∀ {Γ' Γ₀ Γ₁} → Γ' ≈' Γ₀ ⅋ Γ₁ → ⟪ Γ₀ ⅋ A ⟫ → ⟪ Γ₁ ⅋ B ⟫ → ⟪ Γ' ⅋ C ⟫)
  → ⟪ Γ ⅋ C ⟫
⊗-split p f = ⊗-split' (right here) p f


⟪⊗⟫-assoc : ∀ {Γ A B C} → ⟪ Γ ⅋ (A ⊗ (B ⊗ C)) ⟫ → ⟪ Γ ⅋ ((A ⊗ B) ⊗ C) ⟫
⟪⊗⟫-assoc p = ⊗-split p λ e pa pbc →
             conv' (!' (⅋-congₗ (e · ⅋-comm) · ⅋-assoc))
           (⊗-split pbc λ e' pb pc → pair (⊆-in (right (right here)))
             (⅋'-cong e' ⅋ε · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
           (pair (⊆-in (right here)) (⅋ε · ⅋-comm) pa pb)
           pc)

⟪⊗⟫-assoc' : ∀ {Γ A B C} → ⟪ Γ ⅋ ((A ⊗ B) ⊗ C) ⟫ → ⟪ Γ ⅋ (A ⊗ (B ⊗ C)) ⟫
⟪⊗⟫-assoc' p = ⊗-split p λ e pab pc →
              conv' (!' (⅋-congₗ e · ⅋-assoc)) (⊗-split pab λ e' pa pb →
              pair (⊆-in (right (right here))) (⅋-congₗ e' · ⅋-assoc) pa
              (pair (⊆-in (right here)) (⅋ε · ⅋'-congᵣ ⅋ε) pb pc))

_,⊗_ : ∀ {A B} → ⟪ A ⟫ → ⟪ B ⟫ → ⟪ A ⊗ B ⟫
p ,⊗ q = pair (⊆-in here) ⅋ε' (conv' (⅋ε' · ⅋-comm) p) (conv' (⅋ε' · ⅋-comm) q)

⊗-fst : ∀ {A B} → ⟪ A ⊗ B ⟫ → ⟪ A ⟫
⊗-fst (end ())
⊗-fst (input () x)
⊗-fst (output () m p)
⊗-fst (pair (⊆-in here) x₁ p p₁) with ≈'-PEnd x₁ ε
⊗-fst (pair (⊆-in here) x₁ p p₁) | P⅋ X X₁ = conv' (⅋-congₗ (PEnd-≈' X ε) · ⅋-comm · ⅋ε) p

⊗-snd : ∀ {A B} → ⟪ A ⊗ B ⟫ → ⟪ B ⟫
⊗-snd (end ())
⊗-snd (input () x)
⊗-snd (output () m p)
⊗-snd (pair (⊆-in here) x₁ p p₁) with ≈'-PEnd x₁ ε
... | P⅋ X X₁ = conv' (⅋-congₗ (PEnd-≈' X₁ ε) · ⅋-comm · ⅋ε) p₁

conv⅋ : ∀ {P Q R} → P ≈ Q → ⟪ P ⅋ R ⟫ → ⟪ Q ⅋ R ⟫
conv⅋ (e · e₁) p = conv⅋ e₁ (conv⅋ e p)
conv⅋ (⅋-congₗ e) p = conv' (!' ⅋-assoc) (conv⅋ e (conv' ⅋-assoc p))
conv⅋ ⅋ε p = conv' (⅋-congₗ ⅋ε) p
conv⅋ ⅋ε' p = conv' (⅋-congₗ ⅋ε') p
conv⅋ ⅋-comm p = conv' (⅋-congₗ ⅋-comm) p
conv⅋ ⅋-assoc p = conv' (⅋-congₗ ⅋-assoc) p
conv⅋ (⊗-congₗ e) p = conv' ⅋-comm (⊗-split (conv' ⅋-comm p) (λ e' pa pb
  → pair (⊆-in (right here)) (⅋ε · e') (conv' ⅋-comm (conv⅋ e (conv' ⅋-comm pa))) pb))
conv⅋ ⊗ε p = conv' ⅋-comm (⊗-split (conv' ⅋-comm p) λ e pa pb →
  conv' (!' (⅋-congₗ (e · ⅋-comm) · ⅋-assoc))
  (mix (conv' ⅋ε pb) pa))
conv⅋ ⊗ε' p = pair (⊆-in (left here)) ⅋-comm (conv' ⅋-comm p) (end (P⅋ ε ε))
conv⅋ ⊗-comm p = conv' ⅋-comm (⊗-split (conv' ⅋-comm p) (λ e' pa pb →
  pair (⊆-in (right here)) (⅋ε · e' · ⅋-comm) pb pa))
conv⅋ ⊗-assoc p = conv' ⅋-comm (⟪⊗⟫-assoc' (conv' ⅋-comm p))

conv : ∀ {P Q} → P ≈ Q → ⟪ P ⟫ → ⟪ Q ⟫
conv (e · e₁) p = conv e₁ (conv e p)
conv (⅋-congₗ e) p = conv⅋ e p
conv ⅋ε p = conv' ⅋ε p
conv ⅋ε' p = conv' ⅋ε' p
conv ⅋-comm p = conv' ⅋-comm p
conv ⅋-assoc p = conv' ⅋-assoc p
conv (⊗-congₗ e) p = conv e (⊗-fst p) ,⊗ ⊗-snd p
conv ⊗ε p = ⊗-fst p
conv ⊗ε' p = p ,⊗ end ε
conv ⊗-comm p = ⊗-snd p ,⊗ ⊗-fst p
conv ⊗-assoc p = (⊗-fst (⊗-fst p)) ,⊗ (⊗-snd (⊗-fst p) ,⊗ ⊗-snd p)



-- -}
-- -}
-- -}
-- -}
-- -}
