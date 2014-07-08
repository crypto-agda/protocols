open import Terms
open import Types
open import libjs
open import proc
open import proto
open import prelude

module Terms.Syntax where


_,,_ : ∀ {Δ Δ'} → (⊢ Δ → ⊢ Δ') → ⊢ Δ → ⊢ Δ'
f ,, x = f x

record _×₀₁_ (A : Set)(B : Set₁) : Set₁ where
  constructor _,₀₁_
  field
    fst₀₁ : A
    snd₀₁ : B
open _×₀₁_

-- totally not a number *wink* *wink*
data Index : Set where
  zer : Index
  suc : Index → Index

lengthEnv : Env → Index
lengthEnv ε = zer
lengthEnv (Δ , d ↦ P) = suc (lengthEnv Δ)

sub : Index → Index → Index
sub i zer = i
sub zer (suc j) = zer -- shouldn't happen yah
sub (suc i) (suc j) = sub i j

Contains : Index → Env → Set
Contains i ε = 𝟘
Contains zer (e , x ↦ x₁) = 𝟙
Contains (suc i) (e , x ↦ x₁) = Contains i e

.findFirst : ∀ Δ {d P} → Contains (lengthEnv Δ) (Δ , d ↦ P)
findFirst ε = _
findFirst (Δ , d ↦ P) = findFirst Δ

.extend : ∀ i Δ {d P} → (_ : Contains i Δ) → Contains i (Δ , d ↦ P)
extend zer Δ c = _
extend (suc i) ε c = c
extend (suc i) (Δ , d ↦ P) c = extend i Δ c

.MassiveProof : (i : Index)(Δ : Env) → .(_ : Contains i Δ) → Contains (sub (lengthEnv Δ) (suc i)) Δ
MassiveProof i ε ()
MassiveProof zer (Δ , d ↦ P) c = findFirst Δ
MassiveProof (suc i) (Δ , d ↦ P) c = extend _ Δ (MassiveProof i Δ c)

lookupEnvd : (i : Index)(Δ : Env).(_ : Contains i Δ) → URI ×₀₁ Proto
lookupEnvd i ε ()
lookupEnvd zer (Δ , d ↦ P) _ = d ,₀₁ P
lookupEnvd (suc i) (Δ , d ↦ P) p = lookupEnvd i Δ p

buildProof : (i : Index){Δ : Env}.{p : Contains i Δ} →
             let d ,₀₁ P = lookupEnvd i Δ p
             in d ↦ P ∈ Δ
buildProof i {ε} {()}
buildProof zer {Δ , d ↦ P} = here
buildProof (suc i) {Δ , d ↦ P}{p} = there (buildProof i {Δ} {p})

w : (i : Index){Δ : Env}.{p : Contains i Δ} →
    let j = sub (lengthEnv Δ) (suc i)
        d ,₀₁ P = lookupEnvd j Δ (MassiveProof i Δ p)
    in d ↦ P ∈ Δ
w i {p = p} = buildProof _

-- -}
-- -}
-- -}
-- -}
