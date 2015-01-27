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
open import partensor.Shallow.Dom
import partensor.Shallow.Session as Session
import partensor.Shallow.Map as Map
import partensor.Shallow.Env as Env -- hiding (Env; module Env; _↦_∈_; module _↦_∈_)
import partensor.Shallow.Proto as Proto -- hiding (Env; module Env; _↦_∈_; module _↦_∈_)
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/_; Ended; Selection)
open Proto   hiding ()

module partensor.Shallow.Term where

{-
data ⟨_⟩ (Δ : Proto) : Set₁ where
  end :
    Ended Δ
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

data ⟨_⟩ {δs}(I : Proto δs) : Set₁ where
  end :
    Ended I
    → ⟨ I ⟩

  ⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I )
      (P : ∀ c₀ c₁ → ⟨ I / forget l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → ⟨ I ⟩

  ⊗-out :
    ∀ {c S₀ S₁ δ} {E : Env δ}
      (l : [ E ]∈ I)
      (l' : c ↦ S₀ ⊗ S₁ ∈ E)
      (P : ∀ c₀ c₁ → ⟨ I / forget l ,[ (E Env./ l' , c₀ ↦ S₀ , c₁ ↦ S₁) ] ⟩)
    → ⟨ I ⟩

  split :
      (Z : Selection δs)
      (A1 : AtMost 1 Z)
      (P₀ : ⟨ I /₀ Z ⟩)
      (P₁ : ⟨ I /₁ Z ⟩)
    → ⟨ I ⟩

  nu :
    ∀ {S₀ S₁}
      (P : ∀ c₀ c₁ → ⟨ I ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
      (D : Dual S₀ S₁)
    → ⟨ I ⟩

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
 (T-⊗-out :
    ∀ {δs I c S₀ S₁}
      (l  : [ c ↦ S₀ ⊗ S₁ ]∈ I)
      (σ  : Selection δs)
      (A0 : AtMost 0 σ)
      (P₀ : ∀ c₀ → T⟨ I / forget l /₀ σ ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I / forget l /₁ σ ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩)

 (T-⅋-inp :
    ∀ {δs}{I : Proto δs}{c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → T⟨ I / forget l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩)

 (T-end :
    ∀ {δs}{I : Proto δs}
      (E : Ended I)
    → T⟨ I ⟩)

 (T-cut :
    ∀ {δs}{I : Proto δs}{S₀ S₁}
      (σ  : Selection δs)
      (A0 : AtMost 0 σ)
      (P₀ : ∀ c₀ → T⟨ I /₀ σ ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I /₁ σ ,[ c₁ ↦ S₁ ] ⟩)
      (D : Dual S₀ S₁)
    → T⟨ I ⟩) where

  module _ {δF}(F : Env δF) where
    ⊗-split : ∀ {δ δs}{I : Proto δs}{E : Env δ}
                 (l : Doms'.[ δ ]∈ δs)
                 -- (l : [ E ]∈ I)
                 -- {c S}(l' : c ↦ S ∈ E)
                 (P : ⟨ I ⟩)
                 (κ : ∀ {c S}
                        -- E 
                        (l' : c ↦ S ∈ E)
                        {J : Proto δs}
                        (σ : Selection δs)
                        (A0 : AtMost 0 σ)
                        (P₀ : ⟨ J /₀ σ ,[ (E Env./ l' , c ↦ end) ] ,[ F ] ⟩)
                        (P₁ : ⟨ J /₁ σ ,[ (E Env./*   , c ↦   S) ] ,[ F ] ⟩)
                      → T⟨ J {-/ l-} ,[ F ] ⟩)
              → T⟨ I / l ,[ F ] ⟩
    ⊗-split l (end x) κ = {!!} -- elim
    ⊗-split l (⅋-inp l₁ P) κ = T-⅋-inp {!l₁!} {!!}
    ⊗-split l (⊗-out l₁ l₁' P) κ = {!!}
    ⊗-split l (split Z A1 P P₁) κ = {!!}
    ⊗-split l (nu P D) κ = {!!}

  go : ∀ {δs}{I : Proto δs} → ⟨ I ⟩ → T⟨ I ⟩
  go (end x) = T-end x
  go (⅋-inp l P) = T-⅋-inp l (λ c₀ c₁ → go (P c₀ c₁))
  go {δs}{I}(⊗-out {c} {S₀} {S₁} {δ} {E} l l' P) = {!SP!}
    where c0 = {!!}
          c1 = {!!}
          PP : ⟨ I / forget l ,[ (E Env./ l' , c0 ↦ S₀ , c1 ↦ S₁) ] ⟩
          PP = P c0 c1
          SP = ⊗-split {!!} here PP λ {J} σ P₀ P₁ →
                 {!⊗-split ? here P₀ λ {J'} σ' P₀' P₁' →
                     ?!}
  go (split Z A P₀ P₁) = {!!}
  go (nu P D) = {!!}

{-
data T⟨_⟩ {δs}(I : Proto δs) : Set₁ where
  ⊗ :
    ∀ {c S₀ S₁}
      (l  : [ c ↦ S₀ ⊗ S₁ ]∈ I)
      (σ  : Selection δs)
      (P₀ : ∀ c₀ → T⟨ I / l /₀ σ ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I / l /₁ σ ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

  ⅋ :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → T⟨ I / l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

  end :
    Ended I
    → T⟨ I ⟩

  cut :
    ∀ {S₀ S₁}
      (σ  : Selection δs)
      (P₀ : ∀ c₀ → T⟨ I /₀ σ ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I /₁ σ ,[ c₁ ↦ S₁ ] ⟩)
      (D : Dual S₀ S₁)
    → T⟨ I ⟩

{-
data T⟨_⟩ {δ} (E : Env δ) : Set₁ where
  ⊗ :
    ∀ {c S₀ S₁}
      (l  : c ↦ (S₀ ⊗ S₁) ∈ E)
      (σ  : Env.Selection δ)
      (P₀ : ∀ c₀ → T⟨ (E Env./ l) /₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → T⟨ (E Env./ l) /₁ σ , c₁ ↦ S₁ ⟩)
    → T⟨ E ⟩

  ⅋ :
    ∀ {c S₀ S₁}
      (l : c ↦ (S₀ ⅋ S₁) ∈ E)
      (P : ∀ c₀ c₁ → T⟨ (E / l) , c₀ ↦ S₀ , c₁ ↦ S₁ ⟩)
    → T⟨ E ⟩

  end :
    Env.Ended E
    → T⟨ E ⟩

  cut :
    ∀ {S₀ S₁}
      (σ  : Selection δ)
      (P₀ : ∀ c₀ → T⟨ E /₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → T⟨ E /₁ σ , c₁ ↦ S₁ ⟩)
      (D : Dual S₀ S₁)
    → T⟨ E ⟩

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
