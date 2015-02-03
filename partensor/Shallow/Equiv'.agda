
{-# OPTIONS --copattern #-}
open import Function
open import Data.Zero
open import Data.Product renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)

open import Relation.Binary.PropositionalEquality.NP
open import Relation.Nullary
open import partensor.Shallow.Session as Session
open import partensor.Shallow.Env as Env
open import partensor.Shallow.Proto as Proto
import partensor.Shallow.Dom as Dom

module partensor.Shallow.Equiv' where

infix 0 _⊆_
record _⊆_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor mk
  field
    un-⊆ : ∀ c S (NES : ¬(Session.Ended S))(l : c ↦ S ∈ E) → c ↦ S ∈ F
open _⊆_ public

⊆-refl : ∀ {δE}{E : Env δE} → E ⊆ E
⊆-refl = mk λ c S NES l → l

⊆-there : ∀ {δE}{E : Env δE}{c S} → E ⊆ E , c ↦ S
⊆-there = mk (λ _ _ _ → there')

⊆-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ⊆ F → F ⊆ G → E ⊆ G
⊆-trans (mk p) (mk q) = mk λ c S NES l → q c S NES (p c S NES l)

⊆,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ⊆ F → E , c ↦ S ⊆ F , c ↦ S
un-⊆ (⊆,↦ E∼F) c S₁ NES (mk Dom.here ↦A) = mk Dom.here ↦A
un-⊆ (⊆,↦ E∼F) c₁ S₁ NES (mk (Dom.there lA) ↦A) = there' (un-⊆ E∼F c₁ S₁ NES (mk lA ↦A))

⊆,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ⊆ E
un-⊆ ⊆,↦end c .end NES (mk Dom.here refl) = 𝟘-elim (NES _)
un-⊆ ⊆,↦end c₁ S NES (mk (Dom.there lA) ↦A) = mk lA ↦A

infix 0 _∼_
record _∼_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆ : E ⊆ F
    get-⊇ : F ⊆ E
open _∼_ public

∼-refl : ∀ {δE}{E : Env δE} → E ∼ E
∼-refl = ⟨ ⊆-refl , ⊆-refl ⟩

∼-reflexive : ∀ {δE}{E F : Env δE} → E ≡ F → E ∼ F
∼-reflexive refl = ∼-refl

∼-sym : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → F ∼ E
∼-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

∼-! = ∼-sym

∼-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ∼ F → F ∼ G → E ∼ G
∼-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ ⊆-trans p r , ⊆-trans s q ⟩

_∼-∙_ = ∼-trans

∼,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ∼ F → E , c ↦ S ∼ F , c ↦ S
∼,↦ ⟨ p , q ⟩ = ⟨ ⊆,↦ p , ⊆,↦ q ⟩

∼,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ∼ E
∼,↦end = ⟨ ⊆,↦end , ⊆-there ⟩

∼-Ended : ∀ {δE}{E : Env δE} → Env.Ended E → ε ∼ E
∼-Ended {E = ε} EE = ∼-refl
∼-Ended {E = E , c ↦ « _ »} ⟨ proj₁ , () ⟩
∼-Ended {E = E , c ↦ end} ⟨ proj₁ , proj₂ ⟩ = ∼-trans (∼-Ended proj₁)  (∼-sym ∼,↦end)

_∼-End_ : ∀ {δE δF}{E : Env δE}{F : Env δF} → Env.Ended E → Env.Ended F → E ∼ F
EE ∼-End EF = ∼-trans (∼-sym (∼-Ended EE)) (∼-Ended EF)

∼-cancel-unthere… : ∀ {δI}{I : Proto δI}
        {δE}{E : Env δE}(EE : Env.Ended E)
        {c S}(l : [ c ↦ S …]∈ I ,[ E ])
        → [_↦_…]∈_.E l ∼ [_↦_…]∈_.E (unthere…' EE l)
∼-cancel-unthere… EE (mk (mk Doms'.here refl) lE) = 𝟘-elim (not-there' id EE lE)
∼-cancel-unthere… EE (mk (mk (Doms'.there lΔ) ↦Δ) lE) = ∼-refl

infix 0 _⊆s_
record _⊆s_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor mk
  field
    un-⊆s : ∀ c S (l : [ c ↦ S …]∈ I)
            → Σ ([ c ↦ S …]∈ J) λ l' → [↦…]∈.E l ∼ [↦…]∈.E l'
open _⊆s_ public

⊆s-there : ∀ {δE δJ}{E : Env δE}{J : Proto δJ} → J ⊆s J ,[ E ]
un-⊆s ⊆s-there c S l = ⟨ there…' l , ∼-refl ⟩

⊆s-refl : ∀ {δI}{I : Proto δI} → I ⊆s I
⊆s-refl = mk λ c S l → ⟨ l , ∼-refl ⟩

⊆s-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
           → I ⊆s J → J ⊆s K → I ⊆s K
un-⊆s (⊆s-trans (mk p) (mk q)) c S l =
  let p' = p c S l
      q' = q c S (fst p')
  in ⟨ fst q' , ∼-trans (snd p') (snd q') ⟩

⊆,[] : ∀ {δF₀ δF₁ δI δJ}{F₀ : Env δF₀}{F₁ : Env δF₁}{I : Proto δI}{J : Proto δJ}
       → I ⊆s J → F₀ ∼ F₁ → I ,[ F₀ ] ⊆s J ,[ F₁ ]
un-⊆s (⊆,[] I⊆J F₀F₁) c S (mk (mk Doms'.here refl) lE)
  =  ⟨ (mk (mk Doms'.here refl) (un-⊆ (get-⊆ F₀F₁) c « S » id lE)) , F₀F₁ ⟩
un-⊆s (⊆,[] I⊆J F₀F₁) c S (mk (mk (Doms'.there lΔ) ↦Δ) lE)
  = ×map there…' id (un-⊆s I⊆J c S (mk (mk lΔ ↦Δ) lE))


⊆,[end] : ∀ {δE δI}{E : Env δE}{I : Proto δI}(EE : Env.Ended E)
        → I ,[ E ] ⊆s I
un-⊆s (⊆,[end] EE) c S l = ⟨ unthere…' EE l , ∼-cancel-unthere… EE l ⟩

infix 0 _≈_
record _≈_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆s : I ⊆s J
    get-⊇s : J ⊆s I

≈-refl : ∀ {δI}{I : Proto δI} → I ≈ I
≈-refl = ⟨ ⊆s-refl , ⊆s-refl ⟩

≈-reflexive : ∀ {δI}{I J : Proto δI} → I ≡ J → I ≈ J
≈-reflexive refl = ≈-refl

≈-sym : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
        → I ≈ J → J ≈ I
≈-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

≈-! = ≈-sym

≈-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
          → I ≈ J → J ≈ K → I ≈ K
≈-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ ⊆s-trans p r , ⊆s-trans s q ⟩

_≈-∙_ = ≈-trans

≈,[] : ∀ {δE δF δI δJ}{E : Env δE}{F : Env δF}{I : Proto δI}{J : Proto δJ}
       → I ≈ J → E ∼ F → I ,[ E ] ≈ J ,[ F ]
≈,[] ⟨ I⊆J , J⊆I ⟩ E∼F = ⟨ ⊆,[] I⊆J E∼F , ⊆,[] J⊆I (∼-sym E∼F) ⟩

≈,[end] : ∀ {δE δI}{E : Env δE}{I : Proto δI}(EE : Env.Ended E)
        → I ,[ E ] ≈ I
≈,[end] EE = ⟨ ⊆,[end] EE , ⊆s-there ⟩

⊆,[swap] : ∀ {δE c d A B}{E : Env δE} → E , c ↦ A , d ↦ B ⊆ E , d ↦ B , c ↦ A
un-⊆ ⊆,[swap] d B NES (mk Dom.here refl) = mk (Dom.there Dom.here) refl
un-⊆ ⊆,[swap] c A NES (mk (Dom.there Dom.here) refl) = mk Dom.here refl
un-⊆ ⊆,[swap] c₁ S NES (mk (Dom.there (Dom.there lA)) ↦A) = mk (Dom.there (Dom.there lA)) ↦A

∼,[swap] : ∀ {δE c d A B}{E : Env δE} → E , c ↦ A , d ↦ B ∼ E , d ↦ B , c ↦ A
get-⊆ ∼,[swap] = ⊆,[swap]
get-⊇ ∼,[swap] = ⊆,[swap]

⊆s,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ⊆s I ,[ F ] ,[ E ]
un-⊆s ⊆s,[swap] c S (mk (mk Doms'.here refl) lE) = ⟨ (mk (mk (Doms'.there Doms'.here) refl) lE) , ∼-refl ⟩
un-⊆s ⊆s,[swap] c S (mk (mk (Doms'.there Doms'.here) refl) lE) = ⟨ (mk (mk Doms'.here refl) lE) , ∼-refl ⟩
un-⊆s ⊆s,[swap] c S (mk (mk (Doms'.there (Doms'.there lΔ)) ↦Δ) lE) = ⟨ (mk (mk (Doms'.there (Doms'.there lΔ)) ↦Δ) lE) , ∼-refl ⟩

≈,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ≈ I ,[ F ] ,[ E ]
_≈_.get-⊆s ≈,[swap] = ⊆s,[swap]
_≈_.get-⊇s ≈,[swap] = ⊆s,[swap]

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
/Ds-com {I = I ,[ Δ ]} (Doms'.there l) (Doms'.there l') = ≈,[] (/Ds-com {I = I} l l') ∼-refl
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

∼-thmA : ∀ {c δE}(E : Env δE)(l : c Dom.Dom'.∈ δE)
  → E ∼ E [ l ]≔' end , c ↦ Env.lookup E l
∼-thmA (E , c ↦ v) Dom.here = ∼,↦ (∼-sym ∼,↦end)
∼-thmA (E , c₁ ↦ v) (Dom.there l) = ∼-trans (∼,↦ (∼-thmA E l)) ∼,[swap]

thmA : ∀ {δI}{I : Proto δI}{c S}(l : [ c ↦ S …]∈ I)
         → I ≈ (I [/…] l ,[ E/ l , c ↦ « S » ])
thmA {I = I ,[ Δ ]} (mk (mk Doms'.here refl) (mk lA eq)) rewrite ! eq = ≈,[] (≈-sym (≈,[end] (mapAll _ _))) (∼-thmA Δ lA)
thmA {I = I ,[ Δ ]} (mk (mk (Doms'.there lΔ) ↦Δ) lE) = ≈-trans (≈,[] (thmA {I = I} (mk (mk lΔ ↦Δ) lE)) ∼-refl) ≈,[swap]
-- thmA l = {!!}
-- -}
-- -}
-- -}
-- -}
-- -}
