open import Terms
open import Types
open import proto
open import prelude

module Terms.Multiplicative where

wk : ∀ {Δ d} → ⊢ᶜᶠ Δ → ⊢ᶜᶠ (Δ , d ↦ end)
wk end = end {allEnded = … , _} -- instance arguments should eta more yah
wk (output l m der) = output (there l) m (wk der)
wk (input l x₁) = input (there l) (λ m → wk (x₁ m))

⅋-split : ∀ {dp dq} P Q → ⟦ P ⅋ Q ⟧ → ⊢ᶜᶠ (ε , dp ↦ P , dq ↦ Q)
⅋-split end end der = end
⅋-split end (recv P) der = input here (λ m → ⅋-split end (P m) (der m))
⅋-split end (send P) (m , der) = output here m (⅋-split end (P m) der)
⅋-split (recv P) Q der = input (there here) (λ m → ⅋-split (P m) Q (der m))
⅋-split (send P) end (m , der) = output (there here) m (wk (cut-elim (⟦⟧→⊢ der)))
⅋-split (send P) (recv Q) der = input here (λ m → ⅋-split (send P) (Q m) (der m))
⅋-split (send P) (send Q) (inl m , der) = output (there here) m (⅋-split (P m) (send Q) der)
⅋-split (send P) (send Q) (inr m , der) = output here m (⅋-split (send P) (Q m) der)

split-⅋ : ∀ {dp dq} P Q → ⊢ᶜᶠ (ε , dp ↦ P , dq ↦ Q) → ⟦ P ⅋ Q ⟧
split-⅋ P Q der = {!!}

⅋'-split : ∀ {dp dq} P Q → ⟦ P ⅋' Q ⟧ → ⊢ᶜᶠ (ε , dp ↦ P , dq ↦ Q)
⅋'-split end end der = end
⅋'-split end (recv P) der = input here λ m → ⅋'-split end (P m) (der m)
⅋'-split end (send P) (m , der) = output here m (⅋'-split end (P m) der)
⅋'-split (com x P) end der = wk (cut-elim (⟦⟧→⊢ der))
⅋'-split (recv P) (com y Q) (L , der) = input (there here) λ m → ⅋'-split (P m) (com y Q) (der m)
⅋'-split (send P) (com y Q) (L , (m , der)) = output (there here) m (⅋'-split (P m) (com y Q) der)
⅋'-split (com x P) (recv Q) (R , der) = input here λ m → ⅋'-split (com x P) (Q m) (der m)
⅋'-split (com x P) (send Q) (R , (m , der)) = output here m (⅋'-split (com x P) (Q m) der)

urk : ∀ {P} → ⟦ P ⅋' end ⟧ → ⟦ P ⟧
urk {end} = id
urk {com x P} = id

split-⅋' : ∀ {dp dq} P Q → ⊢ᶜᶠ (ε , dp ↦ P , dq ↦ Q) → ⟦ P ⅋' Q ⟧
split-⅋' end end der = _
split-⅋' end (recv P) (end {(<> , <>) , ()}) m
split-⅋' end (recv P) (output (there (there ())) m der) m₁
split-⅋' end (recv P) (input here x₁) m = split-⅋' end (P m) (x₁ m)
split-⅋' end (recv P) (input (there (there ())) x₁) m
split-⅋' end (send P) (end {(<> , <>) , ()})
split-⅋' end (send P) (output here m der) = m , split-⅋' end (P m) der
split-⅋' end (send P) (output (there (there ())) m der)
split-⅋' end (send P) (input (there (there ())) x₁)
split-⅋' (com IN P) end (end {(<> , ()) , <>}) m
split-⅋' (com IN P) end (output (there (there ())) m der) m₁
split-⅋' (com IN P) end (input (there here) x₁) m = urk (split-⅋' (P m) end (x₁ m))
split-⅋' (com IN P) end (input (there (there ())) x₁) m
split-⅋' (com OUT P) end (end {(<> , ()) , <>})
split-⅋' (com OUT P) end (output (there here) m der) = m , urk (split-⅋' (P m) end der)
split-⅋' (com OUT P) end (output (there (there ())) m der)
split-⅋' (com OUT P) end (input (there (there ())) x₁)
split-⅋' (com x P) (com x₁ P₁) (end {(<> , ()) , snd})
split-⅋' (com x P) (com .OUT P₁) (output here m der) = R , (m , split-⅋' _ _ der)
split-⅋' (com .OUT P) (com x₁ P₁) (output (there here) m der) = L , (m , split-⅋' _ _ der)
split-⅋' (com x P) (com x₁ P₁) (output (there (there ())) m der)
split-⅋' (com x P) (com .IN P₁) (input here x₃) = R , λ m → split-⅋' _ _ (x₃ m)
split-⅋' (com .IN P) (com x₁ P₁) (input (there here) x₃) = L , λ m → split-⅋' _ _ (x₃ m)
split-⅋' (com x P) (com x₁ P₁) (input (there (there ())) x₃)

postulate
  funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x}
           → (∀ x → f x ≡ g x) → f ≡ g

tofrom : ∀ {dp dq} P Q (x : ⟦ P ⅋' Q ⟧) → split-⅋' {dp} {dq} P Q (⅋'-split P Q x) ≡ x
tofrom end end x = refl
tofrom end (recv P) x₁ = funext λ m → tofrom end (P m) (x₁ m)
tofrom end (send P) (m , x₁) = ap (_,_ m) (tofrom end (P m) x₁)
tofrom (recv P) end x₁ = funext λ m → {!tofrom (P m) end (x₁ m)!}
tofrom (send P) end (m , x₁) = ap (_,_ m) {!!}
tofrom (recv P) (com x₁ P₁) (L , x₂) = ap (_,_ L) (funext λ m → tofrom (P m) (com x₁ P₁) (x₂ m) )
tofrom (send P) (com x₁ P₁) (L , x₂) = {!!}
tofrom (com x P) (com x₁ P₁) (R , x₂) = {!!}
