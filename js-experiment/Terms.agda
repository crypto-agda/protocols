open import proto
open import Types
open import prelude
open import uri

module Terms where

infix 2 ⊢_ ⊢ᶜᶠ_

data ⊢_ : (Δ : Env) → Set₁ where
  end : ∀{Δ}{e : EndedEnv Δ}
       ------------------
      → ⊢ Δ

  output : ∀ {Δ d M P}{{_ : SER M}}
             (l : d ↦ send P ∈ Δ)(m : M)
             (p : ⊢ Δ [ l ≔ m ])
             -------------------
               → ⊢ Δ

  input : ∀ {Δ d M}{P : M → _}{{_ : SER M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → ⊢ Δ [ l ≔ m ])
                 ----------------------
                     → ⊢ Δ

  end-last : ∀ {Δ d}
               (p : ⊢ (Δ , d ↦ end))
               ----------------------
                 → ⊢ Δ

  mix : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
          (p : ⊢ Δ₀) (q : ⊢ Δ₁)
          --------------------
        → ⊢ Δ

  cut : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) {P d}
          (p : ⊢ (Δ₀ , d ↦ dual P))
          (q : ⊢ (Δ₁ , d ↦ P))
          ---------------------
        → ⊢ Δ

  fwd : ∀ c d {P} → ⊢ (ε , c ↦ P , d ↦ dual P)

  exch-last :
      ∀ {Δ c d P Q} →
      (p : ⊢ Δ , c ↦ P , d ↦ Q)
      → ⊢ Δ , d ↦ Q , c ↦ P

data ⊢ᶜᶠ_ (Δ : Env) : Set₁ where
  end : {e : EndedEnv Δ} → ⊢ᶜᶠ Δ

  output : ∀ {d M P}{{_ : SER M}}
            (l : d ↦ send P ∈ Δ) → (m : M)
            (p : ⊢ᶜᶠ Δ [ l ≔ m ])
            --------------------
              → ⊢ᶜᶠ Δ

  input : ∀ {d M}{P : M → _}{{_ : SER M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → ⊢ᶜᶠ Δ [ l ≔ m ])
            ----------------------------
                     → ⊢ᶜᶠ Δ

embedᶜᶠ : ∀ {Δ} → ⊢ᶜᶠ Δ → ⊢ Δ
embedᶜᶠ (end {e = e}) = end {e = e}
embedᶜᶠ (output l m p) = output l m (embedᶜᶠ p)
embedᶜᶠ (input l p) = input l λ m → embedᶜᶠ (p m)

mixᶜᶠ : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
         (p : ⊢ᶜᶠ Δ₀)
         (q : ⊢ᶜᶠ Δ₁)
         -------------
           → ⊢ᶜᶠ Δ
mixᶜᶠ Δₛ end q = tr ⊢ᶜᶠ_ (Zip-identity  Δₛ) q
mixᶜᶠ Δₛ (output l m p) q
  = output (Zip-com∈₀ Δₛ l) m (mixᶜᶠ (Zip-≔₀ l Δₛ) p q)
mixᶜᶠ Δₛ (input l p) q
  = input (Zip-com∈₀ Δₛ l) λ m → mixᶜᶠ (Zip-≔₀ l Δₛ) (p m) q

cutᶜᶠ : ∀ {Δ Δ₀ Δ₁}
         (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) d P
         (p : ⊢ᶜᶠ (Δ₀ , d ↦ dual P))
         (q : ⊢ᶜᶠ (Δ₁ , d ↦ P))
         ---------------------------
           → ⊢ᶜᶠ (Δ , d ↦ end)
cutᶜᶠ Δₛ d end p q = mixᶜᶠ (Δₛ , d ↦₀ end) p q

cutᶜᶠ Δₛ d (recv P) (output here m p) (input here q) = cutᶜᶠ Δₛ d (P m) p (q m)
cutᶜᶠ Δₛ d (send P) (input here p) (output here m q) = cutᶜᶠ Δₛ d (P m) (p m) q

cutᶜᶠ Δₛ d (send P) (output (there l) m p) q
  = output (there (Zip-com∈₀ Δₛ l)) m (cutᶜᶠ (Zip-≔₀ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d (recv P) (output (there l) m p) q
  = output (there (Zip-com∈₀ Δₛ l)) m (cutᶜᶠ (Zip-≔₀ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d (recv P) (input (there l) p) q
  = input (there (Zip-com∈₀ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₀ l Δₛ) d _ (p m) q
cutᶜᶠ Δₛ d (send P) (input (there l) p) q
  = input (there (Zip-com∈₀ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₀ l Δₛ) d _ (p m) q
cutᶜᶠ Δₛ d (recv P) p (output (there l) m q)
  = output (there (Zip-com∈₁ Δₛ l)) m (cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d (send P) p (output (there l) m q)
  = output (there (Zip-com∈₁ Δₛ l)) m (cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d (send P) p (input (there l) q)
  = input (there (Zip-com∈₁ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p (q m)
cutᶜᶠ Δₛ d (recv P) p (input (there l) q)
  = input (there (Zip-com∈₁ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p (q m)

cutᶜᶠ _ _ (com _ _) (end {e = _ , ()}) _
cutᶜᶠ _ _ (com _ _) _ (end {e = _ , ()})

end-lastᶜᶠ : ∀ {Δ d}
              (p : ⊢ᶜᶠ (Δ , d ↦ end))
              -----------------------
                → ⊢ᶜᶠ Δ
end-lastᶜᶠ (end {e = e , _}) = end {e = e}
end-lastᶜᶠ (output (there l) m p) = output l m (end-lastᶜᶠ p)
end-lastᶜᶠ (input (there l) p) = input l λ m → end-lastᶜᶠ (p m)

fwdᶜᶠ : ∀ c d {P} → ⊢ᶜᶠ (ε , c ↦ P , d ↦ dual P)
fwdᶜᶠ _ _ {end} = end
fwdᶜᶠ _ _ {recv P} = input (there here) λ m → output here m (fwdᶜᶠ _ _ {P m})
fwdᶜᶠ _ _ {send P} = input here λ m → output (there here) m (fwdᶜᶠ _ _ {P m})

-- only the last two are exchanged, some more has to be done
exch-lastᶜᶠ :
  ∀ {Δ c d P Q} →
  (p : ⊢ᶜᶠ Δ , c ↦ P , d ↦ Q)
  → ⊢ᶜᶠ Δ , d ↦ Q , c ↦ P
exch-lastᶜᶠ (end {e = (a , b) , c}) = end {e = (a , c) , b}
exch-lastᶜᶠ (output here m p) = output (there here) m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (output (there here) m p) = output here m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (output (there (there l)) m p) = output (there (there l)) m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (input here p) = input (there here) λ m → exch-lastᶜᶠ (p m)
exch-lastᶜᶠ (input (there here) p) = input here λ m → exch-lastᶜᶠ (p m)
exch-lastᶜᶠ (input (there (there l)) p) = input (there (there l)) λ m → exch-lastᶜᶠ (p  m)

{-
rotᶜᶠ : ∀ Δ {c P} →
         (p : ⊢ᶜᶠ Δ , c ↦ P)
      → ⊢ᶜᶠ ε , c ↦ P ,, Δ
rotᶜᶠ ε p = p
rotᶜᶠ (Δ , d ↦ P) p = {!rotᶜᶠ Δ p!}

exchᶜᶠ :
  ∀ {Δ₀} Δ₁ {c d P Q} →
  (p : ⊢ᶜᶠ Δ₀ , c ↦ P , d ↦ Q ,, Δ₁)
  → ⊢ᶜᶠ Δ₀ , d ↦ Q , c ↦ P ,, Δ₁
exchᶜᶠ ε p = exch-lastᶜᶠ p
exchᶜᶠ (Δ₁ , d ↦ P)  (end e) = end {!!}
exchᶜᶠ (Δ₁ , d₁ ↦ ._) (output here m p) = output here m ({!exchᶜᶠ Δ₁ p!})
exchᶜᶠ (Δ₁ , d ↦ P)  (output (there l) m p) = {!!}
exchᶜᶠ (Δ₁ , d ↦ P)  (input l p) = {!!}

_⊆_ : (Δ₀ Δ₁ : Env) → Set₁
_⊇_ : (Δ₀ Δ₁ : Env) → Set₁

Δ₀ ⊆ Δ₁ = ∀ {d P} → d ↦ P ∈ Δ₀ → d ↦ P ∈ Δ₁
Δ₀ ⊇ Δ₁ = Δ₁ ⊆ Δ₀

record _≈_ (Δ₀ Δ₁ : Env) : Set₁ where
  constructor _,_
  field
    ≈⊆ : Δ₀ ⊆ Δ₁
    ≈⊇ : Δ₀ ⊇ Δ₁
open _≈_ public

≈_[_≔_] : ∀ {Δ₀ Δ₁ d M} {P : M → Proto} {{ser : SER M}}
            (Δₑ : Δ₀ ≈ Δ₁) (l : d ↦ com OUT P ∈ Δ₀) (m : M) →
            (Δ₀ [ l ≔ m ]) ≈ (Δ₁ [ ≈⊆ Δₑ l ≔ m ])
≈ Δₑ [ l ≔ m ] = (λ l' → {!≈⊆ Δₑ!}) , {!!}

≈ᶜᶠ : ∀ {Δ₀ Δ₁}
       (Δₑ : Δ₀ ≈ Δ₁)
       (p : ⊢ᶜᶠ Δ₀)
       -----------
         → ⊢ᶜᶠ Δ₁
≈ᶜᶠ Δₑ (end e) = end {!!}
≈ᶜᶠ Δₑ (output l m p) = output (≈⊆ Δₑ l) m (≈ᶜᶠ (≈ Δₑ [ l ≔ m ]) p)
≈ᶜᶠ Δₑ (input l p) = {!!}
-}

cut-elim : ∀ {Δ} (p : ⊢ Δ)
                 ------------
                   → ⊢ᶜᶠ Δ
cut-elim (end {e = e}) = end {e = e}
cut-elim (output l m p) = output l m (cut-elim p)
cut-elim (input l p) = input l (λ m → cut-elim (p m))
cut-elim (mix Δₛ p q) = mixᶜᶠ Δₛ (cut-elim p) (cut-elim q)
cut-elim (cut Δₛ {P} {d} p q) = end-lastᶜᶠ (cutᶜᶠ Δₛ d P (cut-elim p) (cut-elim q))
cut-elim (end-last p) = end-lastᶜᶠ (cut-elim p)
cut-elim (fwd c d) = fwdᶜᶠ c d
cut-elim (exch-last p) = exch-lastᶜᶠ (cut-elim p)

{-

ends,, : Ended Δ₀ → ⊢ Δ₁ → ⊢ Δ₀ ,, Δ₁

start : ∀ {Δ} P
       → ⊢ [ clientURI ↦ dual P ]
       → (∀ d → ⊢ (Δ , d ↦ P))
       → ⊢ Δ
start P p q = cut {!!} (... p) (q {!!})
-}

⊢ᶜᶠ→⟦⟧ : ∀ {P d} → ⊢ᶜᶠ [ d ↦ P ] → ⟦ P ⟧
⊢ᶜᶠ→⟦⟧ {end} end = _
⊢ᶜᶠ→⟦⟧ {com x P} (end {e = _ , ()})
⊢ᶜᶠ→⟦⟧ (output here m der) = m , ⊢ᶜᶠ→⟦⟧ der
⊢ᶜᶠ→⟦⟧ (output (there ()) m der)
⊢ᶜᶠ→⟦⟧ (input here x₁) m = ⊢ᶜᶠ→⟦⟧ (x₁ m)
⊢ᶜᶠ→⟦⟧ (input (there ()) x₁)

Satisfy : ∀ {p d} P → (R : ⟦ log P ⟧ → Set p) → ⊢ [ d ↦ P ] → Set p
Satisfy P Rel d = (d' : ⟦ dual P ⟧) → Rel (telecom P (⊢ᶜᶠ→⟦⟧ (cut-elim d)) d')

⟦⟧→⊢ᶜᶠ : ∀ {P d} → ⟦ P ⟧ → ⊢ᶜᶠ [ d ↦ P ]
⟦⟧→⊢ᶜᶠ {end} p = end
⟦⟧→⊢ᶜᶠ {recv P} p = input here (λ m → ⟦⟧→⊢ᶜᶠ (p m))
⟦⟧→⊢ᶜᶠ {send P} (m , p) = output here m (⟦⟧→⊢ᶜᶠ p)

⟦⟧→⊢ : ∀ {P d} → ⟦ P ⟧ → ⊢ [ d ↦ P ]
⟦⟧→⊢ {end} p = end
⟦⟧→⊢ {recv P} p = input here (λ m → ⟦⟧→⊢ (p m))
⟦⟧→⊢ {send P} (m , p) = output here m (⟦⟧→⊢ p)

{-
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
-}

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
forgetConc (end e) = empty …
forgetConc {Δ} (output l m der) = setΣ l m (forgetConc {{!setΣ l m!}} der) -- (forgetConc der)
forgetConc (input l x₁) with noRecvInLog l
... | ()
-}

⊢telecom : ∀ {Δ} → ⊢ᶜᶠ Δ → ⟦ mapEnv dual Δ ⟧E → ⊢ mapEnv log Δ
⊢telecom end env = end {e = mapEnv-Ended _ …}
⊢telecom (output l m der) env = output (mapEnv-∈ l) m (subst (⊢_)
  (subst-lemma-one-point-four l) (⊢telecom der (subst ⟦_⟧E (sym (subst-lemma-one-point-four l)) (set (mapEnv-∈ l) env m))))
⊢telecom (input l x₁) env = let (m , env') = lookup (mapEnv-∈ l) env
                                hyp = ⊢telecom (x₁ m) (subst (⟦_⟧E) (sym (subst-lemma-one-point-four l)) env')
                             in output (mapEnv-∈ l) m
                             (subst (⊢_) (subst-lemma-one-point-four l) hyp)

-- old version
{-
cutᶜᶠ : ∀ {Δ d P} → ⟦ dual P ⟧ → ⊢ᶜᶠ Δ , d ↦ P → ⊢ᶜᶠ Δ
cutᶜᶠ D (end {allEnded = ΔE , PE }) = end {allEnded = ΔE}
cutᶜᶠ D (output here m E) = cutᶜᶠ (D m) E
cutᶜᶠ D (output (there l) m E) = output l m (cutᶜᶠ D E)
cutᶜᶠ (m , D) (input here x₁) = cutᶜᶠ D (x₁ m)
cutᶜᶠ D (input (there l) x₁) = input l (λ m → cutᶜᶠ D (x₁ m))

cut : ∀ {Δ Δ' Γ Γ' d P} → ⊢ Δ , clientURI ↦ dual P +++ Δ' → ⊢ Γ , d ↦ P +++ Γ' → ⊢ (Δ +++ Δ') +++ (Γ +++ Γ')
cut D E = {!!}
-}



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
