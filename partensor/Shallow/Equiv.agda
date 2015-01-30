{-# OPTIONS --copattern #-}
open import Function
open import Data.Zero
open import Data.Product renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)

open import Relation.Nullary
open import partensor.Shallow.Session as Session
open import partensor.Shallow.Env as Env
open import partensor.Shallow.Proto as Proto

module partensor.Shallow.Equiv where

infix 0 _⊆_
record _⊆_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor mk
  field
    un-⊆ : ∀ c S (NES : ¬(Session.Ended S))(l : c ↦ S ∈ E) → c ↦ S ∈ F
open _⊆_ public

⊆-refl : ∀ {δE}{E : Env δE} → E ⊆ E
⊆-refl = mk λ c S NES l → l

⊆-there : ∀ {δE}{E : Env δE}{c S} → E ⊆ E , c ↦ S
⊆-there = mk (λ _ _ _ → there)

⊆-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ⊆ F → F ⊆ G → E ⊆ G
⊆-trans (mk p) (mk q) = mk λ c S NES l → q c S NES (p c S NES l)

⊆,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ⊆ F → E , c ↦ S ⊆ F , c ↦ S
un-⊆ (⊆,↦ E∼F) c' S' NES' here      = here
un-⊆ (⊆,↦ E∼F) c' S' NES' (there l) = there (un-⊆ E∼F c' S' NES' l)

⊆,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ⊆ E
un-⊆ ⊆,↦end c .end NES here = 𝟘-elim (NES _)
un-⊆ ⊆,↦end c₁ S NES (there l) = l

infix 0 _∼_
record _∼_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆ : E ⊆ F
    get-⊇ : F ⊆ E
open _∼_ public

∼-refl : ∀ {δE}{E : Env δE} → E ∼ E
∼-refl = ⟨ ⊆-refl , ⊆-refl ⟩

∼-sym : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → F ∼ E
∼-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

∼-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ∼ F → F ∼ G → E ∼ G
∼-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ ⊆-trans p r , ⊆-trans s q ⟩

∼,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ∼ F → E , c ↦ S ∼ F , c ↦ S
∼,↦ ⟨ p , q ⟩ = ⟨ ⊆,↦ p , ⊆,↦ q ⟩

∼,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ∼ E
∼,↦end = ⟨ ⊆,↦end , ⊆-there ⟩

∼-cancel-unthere… : ∀ {δI}{I : Proto δI}
        {δE}{E : Env δE}(EE : Env.Ended E)
        {c S}(NES : ¬(Session.Ended S))(l : [ c ↦ S …]∈ I ,[ E ])
        → [_↦_…]∈_.E l ∼ [_↦_…]∈_.E (unthere… NES EE l)
∼-cancel-unthere… EE NES (mk here lE) = 𝟘-elim (not-there NES EE lE)
∼-cancel-unthere… EE NES (mk (there lI) lE) = ∼-refl

infix 0 _⊆s_
record _⊆s_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor mk
  field
    un-⊆s : ∀ c S (NES : ¬(Session.Ended S))(l : [ c ↦ S …]∈ I)
           →
            Σ ([ c ↦ S …]∈ J) λ l' →
              [↦…]∈.E l ∼ [↦…]∈.E l'
open _⊆s_ public

⊆s-there : ∀ {δE δJ}{E : Env δE}{J : Proto δJ} → J ⊆s J ,[ E ]
un-⊆s ⊆s-there c S NES l = ⟨ there… l , ∼-refl ⟩

⊆s-refl : ∀ {δI}{I : Proto δI} → I ⊆s I
⊆s-refl = mk λ c S NES l → ⟨ l , ∼-refl ⟩

⊆s-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
           → I ⊆s J → J ⊆s K → I ⊆s K
un-⊆s (⊆s-trans (mk p) (mk q)) c S NES l =
  let p' = p c S NES l
      q' = q c S NES (fst p')
  in ⟨ fst q' , ∼-trans (snd p') (snd q') ⟩

⊆,[] : ∀ {δF₀ δF₁ δI δJ}{F₀ : Env δF₀}{F₁ : Env δF₁}{I : Proto δI}{J : Proto δJ}
       → I ⊆s J → F₀ ∼ F₁ → I ,[ F₀ ] ⊆s J ,[ F₁ ]
un-⊆s (⊆,[] I⊆J F₀F₁) c S NES (mk here lE₀)
  = ⟨ mk here (un-⊆ (get-⊆ F₀F₁) c S NES lE₀) , F₀F₁ ⟩
un-⊆s (⊆,[] I⊆J F₀F₁) c S NES (mk (there lIF₀) lE₀)
  = ×map there… id (un-⊆s I⊆J c S NES (mk lIF₀ lE₀))

⊆,[end] : ∀ {δE δI}{E : Env δE}{I : Proto δI}(EE : Env.Ended E)
        → I ,[ E ] ⊆s I
un-⊆s (⊆,[end] EE) c S NES l = ⟨ unthere… NES EE l , ∼-cancel-unthere… EE NES l ⟩

infix 0 _≈_
record _≈_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆s : I ⊆s J
    get-⊇s : J ⊆s I

≈-refl : ∀ {δI}{I : Proto δI} → I ≈ I
≈-refl = ⟨ ⊆s-refl , ⊆s-refl ⟩

≈-sym : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
        → I ≈ J → J ≈ I
≈-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

≈-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
          → I ≈ J → J ≈ K → I ≈ K
≈-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ ⊆s-trans p r , ⊆s-trans s q ⟩

≈,[] : ∀ {δE δF δI δJ}{E : Env δE}{F : Env δF}{I : Proto δI}{J : Proto δJ}
       → I ≈ J → E ∼ F → I ,[ E ] ≈ J ,[ F ]
≈,[] ⟨ I⊆J , J⊆I ⟩ E∼F = ⟨ ⊆,[] I⊆J E∼F , ⊆,[] J⊆I (∼-sym E∼F) ⟩

≈,[end] : ∀ {δE δI}{E : Env δE}{I : Proto δI}(EE : Env.Ended E)
        → I ,[ E ] ≈ I
≈,[end] EE = ⟨ ⊆,[end] EE , ⊆s-there ⟩

⊆,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ⊆s I ,[ F ] ,[ E ]
un-⊆s ⊆,[swap] c S NES (mk here lE) = ⟨ (mk (there here) lE) , ∼-refl ⟩
un-⊆s ⊆,[swap] c S NES (mk (there here) lE) = ⟨ (mk here lE) , ∼-refl ⟩
un-⊆s ⊆,[swap] c S NES (mk (there (there lI)) lE) = ⟨ (mk (there (there lI)) lE) , ∼-refl ⟩

≈,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ≈ I ,[ F ] ,[ E ]
_≈_.get-⊆s ≈,[swap] = ⊆,[swap]
_≈_.get-⊇s ≈,[swap] = ⊆,[swap]

♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto (B ♦Proto C) ≈ (A ♦Proto B) ♦Proto C
♦-assoc {C = ·} = ≈-refl
♦-assoc {C = C ,[ Δ ]} = ≈,[] (♦-assoc {C = C}) ∼-refl

♦-com, : ∀ {δa δ δb}{A : Proto δa}{B : Proto δb}{E : Env δ} → (A ,[ E ]) ♦Proto B ≈ (A ♦Proto B),[ E ]
♦-com, {B = ·} = ≈-refl
♦-com, {B = B ,[ Δ ]} = ≈-trans (≈,[] (♦-com, {B = B}) ∼-refl) ≈,[swap]

♦-com· : ∀ {δa}{A : Proto δa} → · ♦Proto A ≈ A
♦-com· {A = ·} = ≈-refl
♦-com· {A = A ,[ Δ ]} = ≈,[] ♦-com· ∼-refl

♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto B) ≈ (B ♦Proto A)
♦-com {A = ·} = ♦-com·
♦-com {A = A ,[ Δ ]}{B} = ≈-trans (♦-com, {A = A}{B}) (≈,[] (♦-com {A = A}) ∼-refl)

/Ds-com : ∀ {δs δ δ'}{I : Proto δs}(l : Doms'.[ δ ]∈ δs)(l' : Doms'.[ δ' ]∈ δs)
    → I /Ds l /Ds l' ≈ I /Ds l' /Ds l
/Ds-com Doms'.here Doms'.here = ≈-refl
/Ds-com {I = I ,[ Δ ]} Doms'.here (Doms'.there l') = ≈-refl
/Ds-com {I = I ,[ Δ ]} (Doms'.there l) Doms'.here = ≈-refl
/Ds-com {I = I ,[ Δ ]} (Doms'.there l) (Doms'.there l') = ≈,[] (/Ds-com l l') ∼-refl
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
  thmA : ∀ {δI}{I : Proto δI}{c S}(l : [ c ↦ S …]∈ I)
         → I ≈ (I [/…] l ,[ E/ l , c ↦ S ])
-- thmA l = {!!}
-- -}
-- -}
-- -}
-- -}
-- -}
