open import proto
open import Types
open import proc
open import prelude

module Terms where

infix 2 ⊢_ ⊢ᶜᶠ_

data ⊢_ (Δ : Env) : Set₁ where
  end : {allEnded : AllEnv (λ _ → Ended) Δ} → ⊢ Δ
  output : ∀ {d M P}{{_ : SER M}}
         → (l : d ↦ send P ∈ Δ) → (m : M)
         → ⊢ Δ [ l ≔ m ]
         → ⊢ Δ
  input : ∀ {d M}{P : M → _}{{_ : SER M}}
    → (l : d ↦ recv P ∈ Δ)
    → (∀ m → ⊢ Δ [ l ≔ m ])
    → ⊢ Δ
  start : ∀ P
        → ⊢ [ clientURI ↦ dual P ]
        → (∀ d → ⊢ (Δ , d ↦ P))
        → ⊢ Δ

data ⊢ᶜᶠ_ (Δ : Env) : Set₁ where
  end : {allEnded : AllEnv (λ _ → Ended) Δ} → ⊢ᶜᶠ Δ
  output : ∀ {d M P}{{_ : SER M}}
         → (l : d ↦ send P ∈ Δ) → (m : M)
         → ⊢ᶜᶠ Δ [ l ≔ m ]
         → ⊢ᶜᶠ Δ
  input : ∀ {d M}{P : M → _}{{_ : SER M}}
    → (l : d ↦ recv P ∈ Δ)
    → (∀ m → ⊢ᶜᶠ Δ [ l ≔ m ])
    → ⊢ᶜᶠ Δ

⟦⟧→⊢ : ∀ {P d} → ⟦ P ⟧ → ⊢ [ d ↦ P ]
⟦⟧→⊢ {end} p = end
⟦⟧→⊢ {recv P} p = input here (λ m → ⟦⟧→⊢ (p m))
⟦⟧→⊢ {send P} (m , p) = output here m (⟦⟧→⊢ p)

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


⟦_⟧E : Env → Set
⟦ ε ⟧E = 𝟙
⟦ Δ , d ↦ P ⟧E = ⟦ Δ ⟧E × ⟦ P ⟧

mapEnv : (Proto → Proto) → Env → Env
mapEnv f ε = ε
mapEnv f (Δ , d ↦ P) = mapEnv f Δ , d ↦ f P

mapEnv-all : ∀ {P Q : URI → Proto → Set}{Δ}{f : Proto → Proto}
  → (∀ d x → P d x → Q d (f x))
  → AllEnv P Δ → AllEnv Q (mapEnv f Δ)
mapEnv-all {Δ = ε} f₁ ∀Δ = ∀Δ
mapEnv-all {Δ = Δ , d ↦ P₁} f₁ (∀Δ , P) = (mapEnv-all f₁ ∀Δ) , f₁ d P₁ P

mapEnv-Ended : ∀ {f : Proto → Proto}{Δ} → Ended (f end)
  → AllEnv (λ _ → Ended) Δ → AllEnv (λ _ → Ended) (mapEnv f Δ)
mapEnv-Ended eq = mapEnv-all (λ { d end _ → eq ; d (send P) () ; d (recv P) () })

mapEnv-∈ : ∀ {d P f Δ} → d ↦ P ∈ Δ → d ↦ f P ∈ mapEnv f Δ
mapEnv-∈ here = here
mapEnv-∈ (there der) = there (mapEnv-∈ der)

module _ {d c M cf}{m : M}{{_ : M ≃? SERIAL}}{p} where
  subst-lemma-one-point-four : ∀ {Δ}( l : d ↦ com c p ∈ Δ ) →
    let f = mapProto cf
    in (mapEnv f (Δ [ l ≔ m ])) ≡ (_[_≔_]{c = cf c} (mapEnv f Δ) (mapEnv-∈ l) m)
  subst-lemma-one-point-four here = refl
  subst-lemma-one-point-four (there {d' = d'}{P'} l) = ap (λ X → X , d' ↦ mapProto cf P') (subst-lemma-one-point-four l)

module _ {d P} where
  project : ∀ {Δ} → d ↦ P ∈ Δ → ⟦ Δ ⟧E → ⟦ P ⟧
  project here env = snd env
  project (there mem) env = project mem (fst env)

empty : ∀ {Δ} → AllEnv (λ _ → Ended) Δ → ⟦ Δ ⟧E
empty {ε} <> = _
empty {Δ , d ↦ end} (fst , <>) = empty fst , _
empty {Δ , d ↦ com x P} (fst , ())

noRecvInLog : ∀ {d M}{{_ : M ≃? SERIAL}}{P : M → _}{Δ} → d ↦ recv P ∈ mapEnv log Δ → 𝟘
noRecvInLog {Δ = ε} ()
noRecvInLog {Δ = Δ , d₁ ↦ end} (there l) = noRecvInLog l
noRecvInLog {Δ = Δ , d₁ ↦ com x₁ P₁} (there l) = noRecvInLog l

module _ {d M P}{{_ : M ≃? SERIAL}} where
  lookup : ∀ {Δ}(l : d ↦ send P ∈ Δ) → ⟦ Δ ⟧E → Σ M λ m → ⟦ Δ [ l ≔ m ] ⟧E
  lookup here (env , (m , p)) = m , (env , p)
  lookup (there l) (env , P') = let (m , env') = lookup l env in m , (env' , P')

  set : ∀ {Δ}(l : d ↦ recv P ∈ Δ) → ⟦ Δ ⟧E → (m : M) → ⟦ Δ [ l ≔ m ] ⟧E
  set here (env , f) m = env , f m
  set (there l) (env , P') m = set l env m , P'

  setΣ : ∀ {Δ}(l : d ↦ send P ∈ Δ) → (m : M) → ⟦ Δ [ l ≔ m ] ⟧E → ⟦ Δ ⟧E
  setΣ here m env = fst env , (m , snd env)
  setΣ (there l) m env = setΣ l m (fst env) , snd env

{-
forgetConc : ∀ {Δ} → ⊢ᶜᶠ mapEnv log Δ → ⟦ mapEnv log Δ ⟧E
forgetConc end = empty …
forgetConc {Δ} (output l m der) = setΣ l m (forgetConc {{!setΣ l m!}} der) -- (forgetConc der)
forgetConc (input l x₁) with noRecvInLog l
... | ()
-}


⊢telecom : ∀ {Δ} → ⊢ᶜᶠ Δ → ⟦ mapEnv dual Δ ⟧E → ⊢ mapEnv log Δ
⊢telecom end env = end {allEnded = mapEnv-Ended _ …}
⊢telecom (output l m der) env = output (mapEnv-∈ l) m (subst (⊢_)
  (subst-lemma-one-point-four l) (⊢telecom der (subst ⟦_⟧E (sym (subst-lemma-one-point-four l)) (set (mapEnv-∈ l) env m))))
⊢telecom (input l x₁) env = let (m , env') = lookup (mapEnv-∈ l) env
                                hyp = ⊢telecom (x₁ m) (subst (⟦_⟧E) (sym (subst-lemma-one-point-four l)) env')
                             in output (mapEnv-∈ l) m
                             (subst (⊢_) (subst-lemma-one-point-four l) hyp)

⊢ᶜᶠ→⟦⟧ : ∀ {P d} → ⊢ᶜᶠ [ d ↦ P ] → ⟦ P ⟧
⊢ᶜᶠ→⟦⟧ {end} (end {<> , <>}) = _
⊢ᶜᶠ→⟦⟧ {com x P} (end {<> , ()})
⊢ᶜᶠ→⟦⟧ (output here m der) = m , ⊢ᶜᶠ→⟦⟧ der
⊢ᶜᶠ→⟦⟧ (output (there ()) m der)
⊢ᶜᶠ→⟦⟧ (input here x₁) m = ⊢ᶜᶠ→⟦⟧ (x₁ m)
⊢ᶜᶠ→⟦⟧ (input (there ()) x₁)

cut : ∀ {Δ d P} → ⟦ dual P ⟧ → ⊢ᶜᶠ Δ , d ↦ P → ⊢ᶜᶠ Δ
cut D (end {allEnded = ΔE , PE }) = end {allEnded = ΔE}
cut D (output here m E) = cut (D m) E
cut D (output (there l) m E) = output l m (cut D E)
cut (m , D) (input here x₁) = cut D (x₁ m)
cut D (input (there l) x₁) = input l (λ m → cut D (x₁ m))


cut-elim : ∀ {Δ} → ⊢ Δ → ⊢ᶜᶠ Δ
cut-elim end = end {allEnded = …}
cut-elim (output l m der) = output l m (cut-elim der)
cut-elim (input l x₁) = input l (λ m → cut-elim (x₁ m))
cut-elim (start P der x) = cut (⊢ᶜᶠ→⟦⟧ (cut-elim der)) (cut-elim (x clientURI))

Satisfy : ∀ {p d} P → (R : ⟦ log P ⟧ → Set p) → ⊢ [ d ↦ P ] → Set p
Satisfy P Rel d = (d' : ⟦ dual P ⟧) → Rel (telecom P (⊢ᶜᶠ→⟦⟧ (cut-elim d)) d')
{-
cut : ∀ {Δ Δ' Γ Γ' d P} → ⊢ Δ , clientURI ↦ dual P +++ Δ' → ⊢ Γ , d ↦ P +++ Γ' → ⊢ (Δ +++ Δ') +++ (Γ +++ Γ')
cut D E = {!!}



-- -}
-- -}
-- -}
-- -}
