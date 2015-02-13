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
open import partensor.Shallow.Vars
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/[_]_; Ended)

module partensor.Shallow.Split where

record Split {δI} c A (I : Proto δI) : Set₁ where
  constructor mk
  field
    {δhere δthere} : _
    {Ihere} : Proto δhere
    {Ithere} : Proto δthere
    I≈ : Ihere ♦Proto Ithere ≈ I
    lA : [ c ↦ A …]∈ Ihere
    Phere : TC'⟨ Ihere ⟩
    Pthere : S⟨ Ithere ⟩

𝟘S : S⟨ · ⟩
𝟘S = S-T (TC-end _)

split[_] : ∀ {δI c A}{I : Proto δI}(l : [ c ↦ A …]∈ I)(P : S⟨ I ⟩) → Split c A I
split[_] {δI}{c}{A}{I}(mk4 lΔ ↦Δ lA ↦A)(S-split σs A1 P₀ P₁)
    with Map.lookup (Proto.lookup σs lΔ) lA
       | select {I = I} σs lΔ lA
       | select-com {I = I} σs lΔ lA
... | 0₂ | q | r = {!ap (λ I → S⟨_⟩ {δI} I) r!}
{-
  where
    I'
    P₁ : S⟨ I []/[ 1₂ ] σs ⟩
-}
... | 1₂ | q | r = {!!}
split[_] l (S-T x) = mk ≈-refl l x 𝟘S
