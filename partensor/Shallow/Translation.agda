
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
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

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J)
open import partensor.Shallow.Dom
import partensor.Shallow.Session as Session
import partensor.Shallow.Map as Map
import partensor.Shallow.Env as Env
import partensor.Shallow.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/_; Ended)
open Proto   hiding ()
open import partensor.Shallow.Equiv
open import partensor.Shallow.Term

module partensor.Shallow.Translation where
module Translation
 {t}
 (T⟨_⟩ : ∀ {δI} → Proto δI → Set t)
 (T-⊗-out :
    ∀ {δI I c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ …]∈ I)
      (σs : Selections δI)
      (σE : Selection ([↦…]∈.δE l))
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → T⟨ I [/…] l /₀ σs ,[ E/ l Env./₀ σE , c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I [/…] l /₁ σs ,[ E/ l Env./₁ σE , c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩)

 (T-⅋-inp :
    ∀ {δI}{I : Proto δI}{c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → T⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩)

 (T-end :
    ∀ {δI}{I : Proto δI}
      (E : Ended I)
    → T⟨ I ⟩)

 (T-cut :
    ∀ {δI}{I : Proto δI}{S₀ S₁}
      (D : Dual S₀ S₁)
      (σs : Selections δI)
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → T⟨ I /₀ σs ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I /₁ σs ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩)

 (T-⊗-reorg :
    ∀ {δI δE c c₀ c₁ S₀ S₁}{J : Proto δI}{E : Env δE}
      (l  : [ E ]∈ J)
      (l₀ : c₀ ↦ S₀ ∈ E)
      (l₁ : c₁ ↦ S₁ ∈ E)
      (P : T⟨ J ⟩)
    → T⟨ J / l ,[ (E Env./ l₀ /D (Env.forget l₁) , c ↦ S₀ ⊗ S₁) ] ⟩)

 -- (_≈T_ : ∀ {I J} → T⟨ I ⟩ → T⟨ J ⟩ → Set)
 (T-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → T⟨ I ⟩ → T⟨ J ⟩)


{-
      Σ (Selections
        T⟨ I /₀ σs ⟩
      × T⟨ I /₁ σs ⟩
-}

-- (T-gc : T⟨ I ⟩ → 

  where

  go : ∀ {δI}{I : Proto δI} → ⟨ I ⟩ → T⟨ I ⟩
  go (end x) = T-end x
  go (⅋-inp l P) = T-⅋-inp l (λ c₀ c₁ → go (P c₀ c₁))
  go {δI}{I}(⊗-out {c} {S₀} {S₁} (mk {δE} {E} lI lE) P) = T-conv e rPP
    where postulate c0 c1 : URI
          F = E Env./ lE , c0 ↦ S₀ , c1 ↦ S₁
          J = I / lI ,[ F ]
          G = F /D there here /D here , c ↦ S₀ ⊗ S₁
          K = J / here ,[ G ]
          rPP : T⟨ K ⟩
          rPP = T-⊗-reorg here (there here) here (go (P c0 c1))
          e : K ≈ I
          e = ≈-trans (≈,[] (≈,[end] (Ended-/* F)) (∼,↦ (∼-trans ∼,↦end ∼,↦end))) (≈-sym (thmA (mk lI lE)))
  {-
          PP  : ⟨ J ⟩
          PP  = P c0 c1
          gPP : T⟨ J ⟩
          gPP = go PP
          SP = ⊗-split {!!} here PP λ {J} σ P₀ P₁ →
                 {!⊗-split ? here P₀ λ {J'} σ' P₀' P₁' →
                     ?!}
   -}
  go (split Z A P₀ P₁) = {!!}
  go (nu D P) = {!!}
