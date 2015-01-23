open import Data.Product
open import Data.Zero
open import Data.One
open import Data.Sum
open import Data.List

open import Relation.Binary.PropositionalEquality.NP hiding ([_])
open import partensor.Shallow.Session
open import partensor.Shallow.Proto

module partensor.Shallow.Term where

data ⊢ (Δ : Proto) : Set₁ where
  ⅋-in : ∀ {c S T} → (l : [ c ↦ (⅋ S T) ]∈ Δ )
         → (∀ {d e} → ⊢ (Δ [ l ≔* [ d ↦ S ] ∷ [ e ↦ T ] ∷ [] ]))
         → ⊢ Δ
  ⊗-out : ∀ {c d e S T η} → (l : [ η ]∈ Δ)
        → (l' : c ↦ ⊗ S T ∈ η)
        → ⊢ (Δ [ l ≔* [ η [ l' += ε , d ↦ S , e ↦ T ]η ] ])
        → ⊢ Δ
  split : ∀ {Δ₀ Δ₁} → ZipP 1 Δ Δ₀ Δ₁ → ⊢ Δ₀ → ⊢ Δ₁ → ⊢ Δ
