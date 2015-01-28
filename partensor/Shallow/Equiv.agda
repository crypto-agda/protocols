{-# OPTIONS --copattern #-}
open import Function
open import Data.Product renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)

open import Relation.Nullary
import partensor.Shallow.Session as Session
import partensor.Shallow.Env as Env
import partensor.Shallow.Proto as Proto
open Env     hiding (_/₀_; _/₁_; _/_; Ended)
open Proto   hiding () renaming (Selection to Selections)

module partensor.Shallow.Equiv where

record _⊆_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor mk
  field
    get : ∀ c S (NES : ¬(Session.Ended S))(l : c ↦ S ∈ E) → c ↦ S ∈ F
open _⊆_ public

record _∼_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆ : E ⊆ F
    get-⊇ : F ⊆ E
open _∼_ public

record _⊆s_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor mk
  field
    gets : ∀ c S (NES : ¬(Session.Ended S))(l : [ c ↦ S …]∈ I)
           →
            Σ ([ c ↦ S …]∈ J) λ l' →
              [↦…]∈.E l ∼ [↦…]∈.E l'
open _⊆s_ public

record _≈_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆s : I ⊆s J
    get-⊇s : J ⊆s I 

there… : ∀ {δF δJ} {F : Env δF} {J : Proto δJ} {c S} →
            [ c ↦ S …]∈ J → [ c ↦ S …]∈ (J ,[ F ])
there… (mk l l') = mk (there l) l'

⊆-refl : ∀ {δE}(E : Env δE) → E ⊆ E
⊆-refl E = mk λ c S NES l → l

∼-refl : ∀ {δE}(E : Env δE) → E ∼ E
∼-refl I = ⟨ ⊆-refl I , ⊆-refl I ⟩

⊆s-refl : ∀ {δI}(I : Proto δI) → I ⊆s I
⊆s-refl I = mk λ c S NES l → ⟨ l , ∼-refl _ ⟩

≈-refl : ∀ {δI}(I : Proto δI) → I ≈ I
≈-refl I = ⟨ ⊆s-refl _ , ⊆s-refl _ ⟩

∼-sym : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → F ∼ E
∼-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

≈-sym : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
        → I ≈ J → J ≈ I
≈-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

⊆-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ⊆ F → F ⊆ G → E ⊆ G
⊆-trans (mk p) (mk q) = mk λ c S NES l → q c S NES (p c S NES l)

∼-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ∼ F → F ∼ G → E ∼ G
∼-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ ⊆-trans p r , ⊆-trans s q ⟩

⊆s-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
           → I ⊆s J → J ⊆s K → I ⊆s K
⊆s-trans (mk p) (mk q) = mk λ c S NES l →
  let p' = p c S NES l
      q' = q c S NES (fst p')
  in ⟨ fst q' , ∼-trans (snd p') (snd q') ⟩

≈-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
          → I ≈ J → J ≈ K → I ≈ K
≈-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ ⊆s-trans p r , ⊆s-trans s q ⟩

⊆,[] : ∀ {δF₀ δF₁ δI δJ}{F₀ : Env δF₀}{F₁ : Env δF₁}{I : Proto δI}{J : Proto δJ}
       → I ⊆s J → F₀ ∼ F₁ → (I ,[ F₀ ]) ⊆s (J ,[ F₁ ])
gets (⊆,[] I⊆J F₀F₁) c S NES (mk here lE₀)
  = ⟨ mk here (get (get-⊆ F₀F₁) c S NES lE₀) , F₀F₁ ⟩
gets (⊆,[] I⊆J F₀F₁) c S NES (mk (there lIF₀) lE₀)
  = ×map there… id (gets I⊆J c S NES (mk lIF₀ lE₀))

⊆,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ⊆ F → (E , c ↦ S) ⊆ (F , c ↦ S)
get (⊆,↦ E∼F) c' S' NES' here      = here
get (⊆,↦ E∼F) c' S' NES' (there l) = there (get E∼F c' S' NES' l)

∼,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ∼ F → (E , c ↦ S) ∼ (F , c ↦ S)
∼,↦ ⟨ p , q ⟩ = ⟨ ⊆,↦ p , ⊆,↦ q ⟩

≈,[] : ∀ {δE δF δI δJ}{E : Env δE}{F : Env δF}{I : Proto δI}{J : Proto δJ}
       → I ≈ J → E ∼ F → (I ,[ E ]) ≈ (J ,[ F ])
≈,[] ⟨ I⊆J , J⊆I ⟩ E∼F = ⟨ ⊆,[] I⊆J E∼F , ⊆,[] J⊆I (∼-sym E∼F) ⟩

{-
foo :
  ∀ {δE δF}{E : Env δE}{F : Env δF}
    (EF : E ⊆ F)
    {δI δJ}{I : Proto δI}{J : Proto δJ}
    (lE : [ E ]∈ I)(lF : [ F ]∈ J)
    (IJ/l : (I / lE) ⊆s (J / lF))
  → I ⊆s J
foo EF here here IJ/l c S NES (mk here lE₁) = {!!}
foo EF here (there lF) IJ/l c S NES (mk here lE₁) = {!!}
foo EF (there lE) here IJ/l c S NES (mk here lE₁) = {!!}
foo EF (there lE) (there lF) IJ/l c S NES (mk here lE₁) = {!!}
foo EF here here IJ/l c S NES (mk (there lI) lE₁) = {!!}
foo EF here (there lF) IJ/l c S NES (mk (there lI) lE₁) = {!!}
foo EF (there lE) here IJ/l c S NES (mk (there lI) lE₁) = {!!}
foo EF (there lE) (there lF) IJ/l c S NES (mk (there lI) lE₁) = {!!}
-}

{-
foo :
  ∀ {δE δF}{E : Env δE}{F : Env δF}
    (EF : E ∼ F)
    {δI δJ}{I : Proto δI}{J : Proto δJ}
    (lE : [ E ]∈ I)(lF : [ F ]∈ J)
    (IJ/l : (I / lE) ≈ (J / lF))
  → I ≈ J
foo = {!!}
-}

{-
bar' : ∀ {δI}{I : Proto δI}{c S}(l : [ c ↦ S …]∈ I) → (I [/…] l ,[ E/ l ]) ⊆s I
bar' l c₁ S₁ NES (mk here lE') = {!!}
bar' (mk lI lE) c₁ S₁ NES (mk (there lI') lE') = {!!}

bar : ∀ {δI}{I : Proto δI}{c S}(l : [ c ↦ S …]∈ I) → I ⊆s (I [/…] l ,[ E/ l ])
bar l = {!!}

-}
postulate
  thmA : ∀ {δI}{I : Proto δI}{c S}(l : [ c ↦ S …]∈ I) → I ≈ (I [/…] l ,[ E/ l ])
-- thmA l = {!!}
-- -}
-- -}
-- -}
-- -}
-- -}
