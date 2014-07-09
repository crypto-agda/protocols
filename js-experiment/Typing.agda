module _ where
open import prelude
open import proc
open import proto
open import Types
open import uri

data _⊢_ (Δ : Env) : JSProc → Set₁ where

  end : {_ : AllEnv (λ _ p → Ended p) Δ}
     → --------------
         Δ ⊢ end

  output : ∀ {d M s m p}{{_ : SER M}}{P : M → Proto}
        → (l : d ↦ send P ∈ Δ) → s parsesTo m → Δ [ l ≔ m ] ⊢ p
        → ------------------
          Δ ⊢ output d s p

  input : ∀ {d p M}{{_ : SER M}}{P : M → Proto}
        → (l : d ↦ recv P ∈ Δ) → (∀ s m → s parsesTo m → Δ [ l ≔ m ] ⊢ p s)
        → --------------------
           Δ ⊢ input d p

  start : ∀ {s p} P
        → [ clientURI ↦ dual P ] ⊢ s → (∀ d → (Δ , d ↦ P) ⊢ p d)
        → -------------------
          Δ ⊢ start s p

toProcWT : ∀ {d} P → (p : ⟦ P ⟧) → [ d ↦ P ] ⊢ toProc d P p
toProcWT end p = end
toProcWT (send P) (m , p) = output here (sym (rinv m)) (toProcWT (P m) p)
toProcWT (recv P) p = input here λ { s m prf → subst (λ X → _ ⊢ [succeed: _ ,fail: _ ] X)
                                                     prf (toProcWT (P m) (p m)) }
