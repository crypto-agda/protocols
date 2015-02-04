{-# OPTIONS --copattern #-}
open import Function
open import Data.Zero
open import Data.Product renaming (_,_ to ⟨_,_⟩; proj₁ to fst;
                                   proj₂ to snd; map to ×map)
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Nullary
open import partensor.Shallow.Session as Session
open import partensor.Shallow.Env as Env
open import partensor.Shallow.Proto as Proto
open import partensor.Shallow.Dom as Dom

module partensor.Shallow.Equiv where

infix 0 _⊆_
record _⊆_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor mk
  field
    un-⊆ : ∀ {c S}(NES : ¬(Session.Ended S))(l : c ↦ S ∈ E) → c ↦ S ∈ F
open _⊆_ public

⊆-refl : ∀ {δE}{E : Env δE} → E ⊆ E
un-⊆ ⊆-refl NES l = l

⊆-there : ∀ {δE}{E : Env δE}{c S} → E ⊆ E , c ↦ S
un-⊆ ⊆-there _ = there'

⊆-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ⊆ F → F ⊆ G → E ⊆ G
un-⊆ (⊆-trans p q) NES l = un-⊆ q NES (un-⊆ p NES l)

_⊆-∙_ = ⊆-trans

⊆,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ⊆ F → E , c ↦ S ⊆ F , c ↦ S
un-⊆ (⊆,↦ E∼F) NES  heRe = heRe
un-⊆ (⊆,↦ E∼F) NES (theRe lA) = there' (un-⊆ E∼F NES ⟨ lA R⟩)

⊆,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ⊆ E
un-⊆ ⊆,↦end NES heRe = 𝟘-elim (NES _)
un-⊆ ⊆,↦end NES (theRe lA) = ⟨ lA R⟩

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
∼-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ p ⊆-∙ r , s ⊆-∙ q ⟩

_∼-∙_ = ∼-trans

∼,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ∼ F → E , c ↦ S ∼ F , c ↦ S
∼,↦ ⟨ p , q ⟩ = ⟨ ⊆,↦ p , ⊆,↦ q ⟩

∼,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ∼ E
∼,↦end = ⟨ ⊆,↦end , ⊆-there ⟩

∼-Ended : ∀ {δE}{E : Env δE} → Env.Ended E → ε ∼ E
∼-Ended {E = ε} EE = ∼-refl
∼-Ended {E = E , c ↦ « _ »} ⟨ _ , () ⟩
∼-Ended {E = E , c ↦ end} ⟨ x , _ ⟩ = ∼-Ended x ∼-∙ (∼-! ∼,↦end)

_∼-End_ : ∀ {δE δF}{E : Env δE}{F : Env δF} → Env.Ended E → Env.Ended F → E ∼ F
EE ∼-End EF = ∼-! (∼-Ended EE) ∼-∙ ∼-Ended EF

∼-cancel-unthere… : ∀ {δI}{I : Proto δI}
        {δE}{E : Env δE}(EE : Env.Ended E)
        {c S}(l : [ c ↦ S …]∈ I ,[ E ])
        → [_↦_…]∈_.E l ∼ [_↦_…]∈_.E (unthere…' EE l)
∼-cancel-unthere… EE (mk heRe[] lE) = 𝟘-elim (Ended-↦∈ lE EE)
∼-cancel-unthere… EE (mk (theRe[] lΔ) lE) = ∼-refl

infix 0 _⊆s_
record _⊆s_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor mk
  field
    un-⊆s : ∀ {c S} (l : [ c ↦ S …]∈ I)
            → Σ ([ c ↦ S …]∈ J) λ l' → [↦…]∈.E l ∼ [↦…]∈.E l'
open _⊆s_ public

⊆s-there : ∀ {δE δJ}{E : Env δE}{J : Proto δJ} → J ⊆s J ,[ E ]
un-⊆s ⊆s-there l = ⟨ there…' l , ∼-refl ⟩

⊆s-refl : ∀ {δI}{I : Proto δI} → I ⊆s I
un-⊆s ⊆s-refl l = ⟨ l , ∼-refl ⟩

⊆s-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
           → I ⊆s J → J ⊆s K → I ⊆s K
un-⊆s (⊆s-trans (mk p) (mk q)) l =
  let p' = p l
      q' = q (fst p')
  in ⟨ fst q' , snd p' ∼-∙ snd q' ⟩

⊆,[] : ∀ {δF₀ δF₁ δI δJ}{F₀ : Env δF₀}{F₁ : Env δF₁}{I : Proto δI}{J : Proto δJ}
       → I ⊆s J → F₀ ∼ F₁ → I ,[ F₀ ] ⊆s J ,[ F₁ ]
un-⊆s (⊆,[] I⊆J F₀F₁) (mk heRe[] lE)
  =  ⟨ (mk heRe[] (un-⊆ (get-⊆ F₀F₁) id lE)) , F₀F₁ ⟩
un-⊆s (⊆,[] I⊆J F₀F₁) (mk (theRe[] lΔ) lE)
  = ×map there…' id (un-⊆s I⊆J (mk ⟨ lΔ R[]⟩ lE))

⊆,[end] : ∀ {δE δI}{E : Env δE}{I : Proto δI}(EE : Env.Ended E)
        → I ,[ E ] ⊆s I
un-⊆s (⊆,[end] EE) l = ⟨ unthere…' EE l , ∼-cancel-unthere… EE l ⟩

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
un-⊆ ⊆,[swap] NES heRe = theRe here
un-⊆ ⊆,[swap] NES (theRe here) = heRe
un-⊆ ⊆,[swap] NES (theRe (there lA)) = theRe (there lA)

∼,[swap] : ∀ {δE c d A B}{E : Env δE} → E , c ↦ A , d ↦ B ∼ E , d ↦ B , c ↦ A
get-⊆ ∼,[swap] = ⊆,[swap]
get-⊇ ∼,[swap] = ⊆,[swap]

⊆s,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ⊆s I ,[ F ] ,[ E ]
un-⊆s ⊆s,[swap] (mk heRe[] lE) = ⟨ mk (theRe[] here) lE , ∼-refl ⟩
un-⊆s ⊆s,[swap] (mk (theRe[] here) lE) = ⟨ mk heRe[] lE , ∼-refl ⟩
un-⊆s ⊆s,[swap] (mk (theRe[] (there l)) lE) = ⟨ mk (theRe[] (there l)) lE , ∼-refl ⟩

≈,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ≈ I ,[ F ] ,[ E ]
_≈_.get-⊆s ≈,[swap] = ⊆s,[swap]
_≈_.get-⊇s ≈,[swap] = ⊆s,[swap]

♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto (B ♦Proto C) ≈ (A ♦Proto B) ♦Proto C
♦-assoc {C = ·} = ≈-refl
♦-assoc {C = C ,[ Δ ]} = ≈,[] (♦-assoc {C = C}) ∼-refl

♦-com, : ∀ {δa δ δb}{A : Proto δa}{B : Proto δb}{E : Env δ} → (A ,[ E ]) ♦Proto B ≈ (A ♦Proto B),[ E ]
♦-com, {B = ·} = ≈-refl
♦-com, {B = B ,[ Δ ]} = ≈,[] (♦-com, {B = B}) ∼-refl ≈-∙ ≈,[swap]

♦-com· : ∀ {δa}{A : Proto δa} → · ♦Proto A ≈ A
♦-com· {A = ·} = ≈-refl
♦-com· {A = A ,[ Δ ]} = ≈,[] ♦-com· ∼-refl

♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto B) ≈ (B ♦Proto A)
♦-com {A = ·} = ♦-com·
♦-com {A = A ,[ Δ ]}{B} = ♦-com, {B = B} ≈-∙ (≈,[] (♦-com {A = A}) ∼-refl)

/Ds-com : ∀ {δs δ δ'}{I : Proto δs}(l : [ δ ]∈D δs)(l' : [ δ' ]∈D δs)
    → I /Ds l /Ds l' ≈ I /Ds l' /Ds l
/Ds-com here here = ≈-refl
/Ds-com {I = I ,[ Δ ]} here      (there l') = ≈-refl
/Ds-com {I = I ,[ Δ ]} (there l) here       = ≈-refl
/Ds-com {I = I ,[ Δ ]} (there l) (there l') = ≈,[] (/Ds-com {I = I} l l') ∼-refl

∼-[]≔end,↦lookup : ∀ {c δE}{E : Env δE}(l : c ∈D δE)
                   → E ∼ E [ l ]≔' end , c ↦ Env.lookup E l
∼-[]≔end,↦lookup {E = _ , _ ↦ _} here      = ∼,↦ (∼-! ∼,↦end)
∼-[]≔end,↦lookup {E = _ , _ ↦ _} (there l) = ∼,↦ (∼-[]≔end,↦lookup l) ∼-∙ ∼,[swap]

≈-/…,[…] : ∀ {δI}{I : Proto δI}{c S}(l : [ c ↦ S …]∈ I)
       → I ≈ (I [/…] l ,[ E/ l , c ↦ « S » ])
≈-/…,[…] {I = I ,[ Δ ]} (mk heRe[] ⟨ lA , eq ⟩) rewrite ! eq = ≈,[] (≈-! (≈,[end] (mapAll _ _))) (∼-[]≔end,↦lookup lA)
≈-/…,[…] {I = I ,[ Δ ]} (mk (theRe[] lΔ) lE) = ≈,[] (≈-/…,[…] {I = I} (mk ⟨ lΔ R[]⟩ lE)) ∼-refl ≈-∙ ≈,[swap]
-- -}
-- -}
-- -}
-- -}
-- -}
