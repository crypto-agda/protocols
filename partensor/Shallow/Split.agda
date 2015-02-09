{-# OPTIONS --copatterns #-}
open import Level.NP
open import Function
open import Data.Product renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J)
open import partensor.Shallow.Dom
import partensor.Shallow.Session as Session
import partensor.Shallow.Map as Map
import partensor.Shallow.Env as Env
open import partensor.Shallow.Proto as Proto
open import partensor.Shallow.Term
open import partensor.Shallow.Vars as Vars
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/[_]_; Ended)

module partensor.Shallow.Split where

postulate
  S-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → S⟨ I ⟩ → S⟨ J ⟩

record Split {δI} c A (I : Proto δI) : Set₁ where
  constructor mk
  field
    {δhere δthere} : _
    {Ihere} : Proto δhere
    {Ithere} : Proto δthere
    I≈ : Ihere ♦Proto' Ithere ≈ I
    lA : [ c ↦ A …]∈ Ihere
    Phere : TC'⟨ Ihere ⟩
    Pthere : S⟨ Ithere ⟩

𝟘S : S⟨ · ⟩
𝟘S = S-T (TC-end _)

split[_] : ∀ {δI c A}{I : Proto δI}(l : [ c ↦ A …]∈ I)(P : S⟨ I ⟩) → Split c A I
split[_] l (TC-⅋-inp l₁ P) = {!!}
split[_] l (TC-?-inp l₁ P) = {!!}
split[_] {δI}{c}{A}{I}(mk4 lΔ ↦Δ lA ↦A)(S-split σs A1 P₀ P₁)
    with Map.lookup (Proto.lookup σs lΔ) lA
       | select {I = I} σs lΔ lA
       | select-com {I = I} σs lΔ lA
... | 0₂ | q | r with split[ mk4 lΔ refl lA (! q ∙ ap (flip _‼_ lA) ↦Δ ∙ ↦A) ] P₀
... | mk {δh}{δt}{Ih}{It} I≈ lA' Phere Pthere =
   mk (Vars.♦-cong₂ ≈-refl Vars.♦-com ≈-∙ Vars.♦-assoc ≈-∙ ♦-cong₂ I≈ ≈-refl ≈-∙ Sel♦ σs ) lA' Phere
     (S-split (Selections♦ 0₂ σs δt) (atMost♦ 0₂ σs δt A1)
        (S-conv (≈-! (Selections♦'/same {K = It} 0₂ σs ≈-∙ ♦-cong₂ (Sel¬ 1₂ σs) ≈-refl ≈-∙ ·♦)) Pthere)
        (S-conv (≈-! (Selections♦'/not {K = It} 1₂ σs ≈-∙ Selections/red 1₂ σs )) P₁))
-- lA' Phere (S-split (Selections♦ 0₂ σs δt) (atMost♦ 0₂ σs δt A1) (S-conv (≈-sym {!!}) Pthere) (S-conv {!!} P₁) )
--{!ap (λ I → S⟨_⟩ {δI} I) r!}
{-
  where
    I'
    P₁ : S⟨ I []/[ 1₂ ] σs ⟩
-}
split[_] (mk4 lΔ ↦Δ lA ↦A) (S-split σs A1 P₀ P₁) | 1₂ | q | r = OK where postulate OK : _
split[_] l (S-T x) = mk OK l x 𝟘S
  where postulate OK : _


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
