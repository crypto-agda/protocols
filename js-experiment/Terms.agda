open import proto
open import Types
open import proc
open import prelude

module Terms where


data ⊢_ (Δ : Env) : Set₁ where
  end : {_ : AllEnv (λ _ → Ended) Δ} → ⊢ Δ
  output : ∀ {d M P}{{_ : SER M}}
         → (l : d ↦ send is P ∈ Δ) → (m : M)
         → ⊢ Δ [ l ≔ m ]
         → ⊢ Δ
  input : ∀ {d M P}{{_ : SER M}}
    → (l : d ↦ recv is P ∈ Δ)
    → (∀ m → ⊢ Δ [ l ≔ m ])
    → ⊢ Δ
  start : ∀ P
        → ⊢ [ clientURI ↦ dual P ]
        → (∀ d → ⊢ (Δ , d ↦ P))
        → ⊢ Δ

⊢toProc : ∀ {Δ} → ⊢ Δ → JSProc
⊢toProc end = end
⊢toProc (output {d = d} l m prg) = output d (serialize m) (⊢toProc prg)
⊢toProc (input {d = d} l prg) = input d ([succeed: (λ m → ⊢toProc (prg m)) ,fail: error ] ∘ parse)
⊢toProc (start P prg x) = start (⊢toProc prg) (λ d → ⊢toProc (x d))


⊢toProc-WT : ∀ {Δ} (der : ⊢ Δ) → Δ ⊢ ⊢toProc der
⊢toProc-WT (end {x}) = end {_} {x}
⊢toProc-WT (output {{x}} l m der) = output l (sym (rinv m)) (⊢toProc-WT der)
⊢toProc-WT (input {{x}} l x₁) = input l λ s m x →
  subst (λ X → _ [ l ≔ m ] ⊢ [succeed: (⊢toProc ∘ x₁) ,fail: error ] X) x (⊢toProc-WT (x₁ m))
⊢toProc-WT (start P der x) = start P (⊢toProc-WT der) (λ d → ⊢toProc-WT (x d))
