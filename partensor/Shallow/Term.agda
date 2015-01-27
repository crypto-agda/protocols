open import Data.Product hiding (zip)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Sum
open import Data.Nat
{-
open import Data.Vec
open import Data.Fin
-}
-- open import Data.List

open import Relation.Binary.PropositionalEquality.NP hiding ([_])
open import partensor.Shallow.Session
open import partensor.Shallow.Dom
open import partensor.Shallow.Map as Map
open import partensor.Shallow.Env as Env -- hiding (Env; module Env; _↦_∈_; module _↦_∈_)
open import partensor.Shallow.Proto as Proto -- hiding (Env; module Env; _↦_∈_; module _↦_∈_)

module partensor.Shallow.Term where

{-
data ⟨_⟩ (Δ : Proto) : Set₁ where
  end :
    Proto.Ended Δ
    → ⟨ Δ ⟩

  ⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ (ε , c ↦ S₀ ⅋ S₁) ]∈ Δ )
      (P : ∀ c₀ c₁ → ⟨ Δ [ l ≔* (· ,[ ε , c₀ ↦ S₀ ] ,[ ε , c₁ ↦ S₁ ]) ] ⟩)
    → ⟨ Δ ⟩

  ⊗-out :
    ∀ {c S₀ S₁ δ} {η : Env δ}
      (l : [ η ]∈ Δ)
      (l' : c ↦ S₀ ⊗ S₁ ∈ η)
      (P : ∀ c₁ → ⟨ Δ [ l ≔* · ,[ (η / l' , c₀ ↦ S₀ , c₁ ↦ S₁) ] ] ⟩)
      (P₀ : ∀ c₀ → ⟨ Δ [ l ≔* · ,[ (η / l' , c₀ ↦ S₀ , c₁ ↦ S₁) ] ] ⟩)
      (P₁ : ∀ c₁ → ⟨ Δ₁ ⟩)
    → ⟨ Δ ⟩

  split :
    ∀ {Δ₀ Δ₁}
      (Z : ZipP 1 Δ Δ₀ Δ₁)
    → ⟨ Δ ⟩

  nu :
    ∀ {S₀ S₁}
      (l : Point Δ)
      (P : ∀ c₀ c₁ → ⟨ insert Δ l (· ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ])⟩)
      (D : Dual S₀ S₁)
    → ⟨ Δ ⟩
-}

data ⟨_⟩{δs}(Δ : Proto δs) : Set₁ where
  end :
    Proto.Ended Δ
    → ⟨ Δ ⟩

  ⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ (ε , c ↦ S₀ ⅋ S₁) ]∈ Δ )
      (P : ∀ c₀ c₁ → ⟨ Δ [ l ≔* · ,[ ε , c₀ ↦ S₀ ] ,[ ε , c₁ ↦ S₁ ] ] ⟩)
    → ⟨ Δ ⟩

  ⊗-out :
    ∀ {c S₀ S₁ δ} {η : Env δ}
      (l : [ η ]∈ Δ)
      (l' : c ↦ S₀ ⊗ S₁ ∈ η)
      (P : ∀ c₀ c₁ → ⟨ Δ [ l ≔* · ,[ (η Env./ l' , c₀ ↦ S₀ , c₁ ↦ S₁) ] ] ⟩)
    → ⟨ Δ ⟩

  split :
      (Z : Proto.Selection δs)
      (P₀ : ⟨ Δ Proto./₀ Z ⟩)
      (P₁ : ⟨ Δ Proto./₁ Z ⟩)
    → ⟨ Δ ⟩

  nu :
    ∀ {S₀ S₁}
      (l : Point Δ)
      (P : ∀ c₀ c₁ → ⟨ insert Δ l (· ,[ ε , c₀ ↦ S₀ ] ,[ ε , c₁ ↦ S₁ ])⟩)
      (D : Dual S₀ S₁)
    → ⟨ Δ ⟩

{-
⊗Env→Session : ∀ {δ} → Env δ → Session
⊗Env→Session ε = end
⊗Env→Session (Δ , c ↦ v) = ⊗Env→Session Δ ⊗ v

Proto→Dom : Proto → Dom
Proto→Dom · = ε
Proto→Dom (I ,[ Δ ]) = Proto→Dom I , {!!}

Proto→Env : Proto → Env {!!}
Proto→Env · = ε
Proto→Env (I ,[ Δ ]) = Proto→Env I , ? ↦ {!⊗Env→Session!}
-}

module Translation
 {t}
 (T⟨_⟩ : ∀ {δs} → Proto δs → Set t)
 (⊗-out :
    ∀ {δ Δ c S₀ S₁}
      (l  : [ c ↦ (S₀ ⊗ S₁) ]∈ Δ)
      (σ  : Proto.Selection δ)
      (P₀ : ∀ c₀ → T⟨ (Δ Proto./ l) Proto./₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → T⟨ (Δ Proto./ l) Proto./₁ σ , c₁ ↦ S₁ ⟩)
    → T⟨ Δ ⟩)

 (⅋-inp :
    ∀ {δ}{Δ : Env δ}{c S₀ S₁}
      (l : c ↦ (S₀ ⅋ S₁) ∈ Δ)
      (P : ∀ c₀ c₁ → T⟨ (Δ Proto./ l) , c₀ ↦ S₀ , c₁ ↦ S₁ ⟩)
    → T⟨ Δ ⟩)

 (end :
    ∀ {δ}{Δ : Env δ}
      (E : Env.Ended Δ)
    → T⟨ Δ ⟩)

 (cut :
    ∀ {δ}{Δ : Env δ}{S₀ S₁}
      (σ  : Proto.Selection δ)
      (P₀ : ∀ c₀ → T⟨ Δ Proto./₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → T⟨ Δ Proto./₁ σ , c₁ ↦ S₁ ⟩)
      (D : Dual S₀ S₁)
    → T⟨ Δ ⟩) where

  go : ∀ {I : Proto} → ⟨ I ⟩ → T⟨ I ⟩
  go = {!!}

{-
data ⟨_⟩ {δ} (Δ : Env δ) : Set₁ where
  ⊗ :
    ∀ {c S₀ S₁}
      (l  : c ↦ (S₀ ⊗ S₁) ∈ Δ)
      (σ  : Selection δ)
      (P₀ : ∀ c₀ → ⟨ (Δ / l) /₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → ⟨ (Δ / l) /₁ σ , c₁ ↦ S₁ ⟩)
    → ⟨ Δ ⟩

  ⅋ :
    ∀ {c S₀ S₁}
      (l : c ↦ (S₀ ⅋ S₁) ∈ Δ)
      (P : ∀ c₀ c₁ → ⟨ (Δ / l) , c₀ ↦ S₀ , c₁ ↦ S₁ ⟩)
    → ⟨ Δ ⟩

  end :
    Env.Ended Δ
    → ⟨ Δ ⟩

  cut :
    ∀ {S₀ S₁}
      (σ  : Selection δ)
      (P₀ : ∀ c₀ → ⟨ Δ /₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → ⟨ Δ /₁ σ , c₁ ↦ S₁ ⟩)
      (D : Dual S₀ S₁)
    → ⟨ Δ ⟩

{-
data Env : Dom → Set₁ where
  ε     : Env ε
  _,_↦_ : ∀ {δ} (E : Env δ) c (S : Session) → Env (δ , c)
-}

{-

{-

{-
Dom = ℕ
Env : Dom → Set₁
Env n = Vec Session n

Layout : Dom → Set
Layout n = Vec 𝟚 n

projLayout : ∀ {n} (f : Session → 𝟚 → Session) (Δ : Env n) → Layout n → Env n
projLayout f = zipWith f

_/₀_ : ∀ {n} (Δ : Env n) → Layout n → Env n
_/₀_ = projLayout (λ S → [0: S 1: end ])

_/₁_ : ∀ {n} (Δ : Env n) → Layout n → Env n
_/₁_ = projLayout (λ S → [0: end 1: S ])

data ⟨_⟩ {n} (Δ : Env n) : Set₁ where
  ⊗ :
    ∀ {c S₀ S₁}
      (l  : Δ [ c ]= S₀ ⊗ S₁)
      (L  : Layout n)
      (P₀ : ⟨ Δ /₀ L [ c ]≔ S₀ ⟩)
      (P₁ : ⟨ Δ /₁ L [ c ]≔ S₁ ⟩)
    → ⟨ Δ ⟩
  ⅋ :
    ∀ {c S₀ S₁}
      (l : Δ [ c ]= S₀ ⅋ S₁)
      (P : Δ [ c ]=* (S₀ ∷ S₁ ∷ []))
    → ⟨ Δ ⟩
    -}

{-
data Layout : Env → Set where
  ε : Layout ε
  _,_↦_ : ∀ {σ} (L : Layout σ) c {S} (b : 𝟚) → Layout (σ , c ↦ S)

projLayout : (f : 𝟚 → Session → Session) (Δ : Env) → Layout Δ → Env
projLayout f ε ε = ε
projLayout f (Δ , .c ↦ S) (L , c ↦ b) = projLayout f Δ L , c ↦ f b S

_/₀_ : (Δ : Env) → Layout Δ → Env
_/₀_ = projLayout (λ b S → [0: S 1: end ] b)

_/₁_ : (Δ : Env) → Layout Δ → Env
_/₁_ = projLayout (λ b S → [0: end 1: S ] b)

data ⟨_⟩ (Δ : Env) : Set₁ where
{-
  ⅋-in :
    ∀ {c S T}
      (l : [ c ↦ (⅋ S T) ]∈ Δ )
      (P : ∀ d e → ⟨ Δ [ l ≔* · ,[ d ↦ S ] ,[ e ↦ T ] ] ⟩)
    → ⟨ Δ ⟩
-}
  ⊗-out :
    ∀ {c S T}
      (l : c ↦ ⊗ S T ∈ Δ)
      (L : Layout 
      (P : ∀ d → ⟨ Δ [ l ≔ S ] /₀ L ⟩)
      (Q : ∀ e → ⟨ Δ [ l ≔ T ] /₁ L ⟩)
    → ⟨ Δ ⟩

{-
  split :
    ∀ {Δ₀ Δ₁}
    → ZipP 1 Δ Δ₀ Δ₁ → ⟨ Δ₀ ⟩ → ⟨ Δ₁ ⟩ → ⟨ Δ ⟩

  end :
    EndedProto Δ
    → ⟨ Δ ⟩

  nu : ∀ {Δ' S T}
       → (l : []∈ Δ')
       → (∀ c d → ⟨ Δ' [ l ≔* (· ,[ c ↦ S ] ,[ d ↦ T ]) ]' ⟩)
       → Dual S T
       → Δ ≡ Δ' [ l ≔* · ]'
       → ⟨ Δ ⟩

{-
data ⟨_⟩ (Δ : Proto) : Set₁ where
  ⅋-in :
    ∀ {c S T}
      (l : [ c ↦ (⅋ S T) ]∈ Δ )
      (P : ∀ d e → ⟨ Δ [ l ≔* · ,[ d ↦ S ] ,[ e ↦ T ] ] ⟩)
    → ⟨ Δ ⟩

  ⊗-out :
    ∀ {c S T η}
      (l : [ η ]∈ Δ)
      (l' : c ↦ ⊗ S T ∈ η)
      (P : ∀ d e → ⟨ Δ [ l ≔* · ,[ η [ l' += ε , d ↦ S , e ↦ T ]η ] ] ⟩)
    → ⟨ Δ ⟩

  split :
    ∀ {Δ₀ Δ₁}
    → ZipP 1 Δ Δ₀ Δ₁ → ⟨ Δ₀ ⟩ → ⟨ Δ₁ ⟩ → ⟨ Δ ⟩

  end :
    EndedProto Δ
    → ⟨ Δ ⟩

  nu : ∀ {Δ' S T}
       → (l : []∈ Δ')
       → (∀ c d → ⟨ Δ' [ l ≔* (· ,[ c ↦ S ] ,[ d ↦ T ]) ]' ⟩)
       → Dual S T
       → Δ ≡ Δ' [ l ≔* · ]'
       → ⟨ Δ ⟩


{-
-- cut₁ : ∀ {Δ Δ' S}(l : S ∈ Δ)(l' : dual S ∈ Δ') → ⟨ Δ ⟩ → ⟨ Δ' ⟩ → ⟨ Δ [ l ≔ end ] ⅋ Δ' [ l' ≔ end ] ⟩
cut₁ : ∀ {Δ Δ' S}(l : S ∈ Δ)(l' : dual S ∈ Δ')
      → ⟨ Δ ⟩ → ⟨ Δ' ⟩ → ⟨ Δ [ l ≔ end ] ⅋ Δ' [ l' ≔ end ] ⟩
cut₁
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
-- -}
-- -}
