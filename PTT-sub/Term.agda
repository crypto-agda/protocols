{-# OPTIONS --copatterns #-}
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J)
open import PTT.Dom
import PTT-sub.Session as Session
import PTT-sub.Map as Map
import PTT-sub.Env as Env
import PTT-sub.Proto as Proto
open Session hiding (Ended)
open Env     hiding (Ended)
open Proto
-- open import PTT.Equiv

module PTT-sub.Term where

data ⟨_⟩ {δI}(I : Proto δI) : Set₁ where
  end :
    Ended I
    → ⟨ I ⟩

  ⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I )
      (P : ∀ c₀ c₁ → ⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → ⟨ I ⟩

  ⊗-out :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ …]∈ I)
      (P : ∀ c₀ c₁ → ⟨ I [/…] l ,[ E/ l , c₀ ↦ « S₀ » , c₁ ↦ « S₁ » ] ⟩)
    → ⟨ I ⟩

  split :
      (σs : Selections δI)
      (A1 : AtMost 1 I σs)
      (P₀ : ⟨ I []/₀ σs ⟩)
      (P₁ : ⟨ I []/₁ σs ⟩)
    → ⟨ I ⟩

  nu :
    ∀ {S₀ S₁}
      (D : Dual S₀ S₁)
      (P : ∀ c₀ c₁ → ⟨ I ,[ ε , c₀ ↦ « S₀ » , c₁ ↦ « S₁ » ] ⟩)
    → ⟨ I ⟩


data TC'⟨_⟩ {δI}(I : Proto δI) : Set₁ where
 TC-⊗-out :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ ]∈ I)
      (σs : Selections δI)
      (A0 : AtMost 0 (I / l) σs)
      (P₀ : ∀ c₀ → TC'⟨ I / l []/₀ σs ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → TC'⟨ I / l []/₁ σs ,[ c₁ ↦ S₁ ] ⟩)
    → TC'⟨ I ⟩

 TC-⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → TC'⟨ I / l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → TC'⟨ I ⟩

 TC-𝟙-out :
    ∀ {c}
      (l : [ c ↦ 𝟙' …]∈ I)
      (P : TC'⟨ I /… l ⟩)
    → TC'⟨ I ⟩

 TC-⊥-inp :
    ∀ {c}
      (l : [ c ↦ ⊥' ]∈ I)
      (P : TC'⟨ I / l ⟩)
    → TC'⟨ I ⟩

 TC-?-inp :
    ∀ {c A S₁}
      (l : [ c ↦ act (recv {A} S₁) ]∈ I)
      (P : (m : A) → TC'⟨ [ I / l ]≔ « S₁ m »  ⟩)
    → TC'⟨ I ⟩

 TC-!-out :
    ∀ {c A S₁}
      (l : [ c ↦ act (send {A} S₁) ]∈ I)
      (m : A)(P : TC'⟨ [ I / l ]≔ « S₁ m » ⟩)
    → TC'⟨ I ⟩

 TC-end : ∀ (E : Ended I) → TC'⟨ I ⟩

 TC-split :
      (σs : Selections δI)
      (A1 : AtMost 1 I σs)
      (P₀ : TC'⟨ I []/₀ σs ⟩)
      (P₁ : TC'⟨ I []/₁ σs ⟩)
    → TC'⟨ I ⟩
{-
 TC-mix : ∀ {δF δG}{F : Env δF}{G : Env δG}(lF : [ F ]∈ I)(lG : [ G ]∈ I)
     (lF/=lG : DiffDoms ([]∈.lΔ lF) ([]∈.lΔ lG))
     (P : TC'⟨ ((I Proto./ lF) /Ds []∈.lΔ lG),[ F ♦Env G ] ⟩)
     → TC'⟨ I ⟩
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
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
