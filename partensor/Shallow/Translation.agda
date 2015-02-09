open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two

open import partensor.Shallow.Dom
import partensor.Shallow.Session as Session
import partensor.Shallow.Map as Map
import partensor.Shallow.Env as Env
import partensor.Shallow.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; Ended)
open Proto   hiding ()
open import partensor.Shallow.Term
open import partensor.Shallow.Split
open import Relation.Binary.PropositionalEquality.NP hiding (J)

S-⅋-inp : ∀ {c c₀ c₁ δI S₀ S₁}{I : Proto δI}(l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
  → S⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩ → S⟨ I ⟩
S-⅋-inp l P = {!!}

translate : ∀ {δI}{I : Proto δI} → ⟨ I ⟩ → S⟨ I ⟩
translate (end x) = S-T (TC-end x)
translate (⅋-inp l P) = S-⅋-inp l (translate (P c₀ c₁))
  where postulate c₀ c₁ : URI
translate (⊗-out l P) = {!!}
translate (split σs A1 P P₁) = {!!}
translate (nu D P) = {!!}

{-
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
      (P₀ : ∀ c₀ → T⟨ I [/…] l /₀ σs ,[ E/ l Env./₀ σE , c₀ ↦ « S₀ » ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I [/…] l /₁ σs ,[ E/ l Env./₁ σE , c₁ ↦ « S₁ » ] ⟩)
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

 (T-split :
    ∀ {δI}{I : Proto δI}
      (σs : Selections δI)
      (A1 : AtMost 1 σs)
      (P₀ : T⟨ I /₀ σs ⟩)
      (P₁ : T⟨ I /₁ σs ⟩)
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
      (l₀ : c₀ ↦ « S₀ » ∈ E)
      (l₁ : c₁ ↦ « S₁ » ∈ E)
      (P : T⟨ J ⟩)
    → T⟨ J Proto./ l ,[ (E Env./' l₀ /D (↦∈.lA l₁) , c ↦ « S₀ ⊗ S₁ ») ] ⟩)

 (T-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → T⟨ I ⟩ → T⟨ J ⟩)

  where

  T-fwd : ∀ {S₀ S₁} (S : Dual S₀ S₁) c₀ c₁ → T⟨ · ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩
  T-fwd 𝟙⊥ c₀ c₁ = {!!}
  T-fwd ⊥𝟙 c₀ c₁ = {!!}
  T-fwd (act (?! S S₁)) c₀ c₁ = {!!}
  T-fwd (act (!? S S₁)) c₀ c₁ = {!!}
  T-fwd (⊗⅋ S₀ S₁ S₂ S₃) c₀ c₁ =
    T-⅋-inp here[]' λ c₂ c₃ →
      T-⊗-out (there…' (there…' (there…' here…')))
              ((((· ,[ (ε , c₀ ↦ 0₂) ]) ,[ (ε , c₁ ↦ 0₂) ]) ,[ (ε , c₂ ↦ 0₂) ]) ,[ (ε , c₃ ↦ 1₂) ])
              (ε , c₀ ↦ 0₂)
              ((((· ,[ {!!} ]) ,[ {!!} ]) ,[ {!!} ]) ,[ {!!} ])
              (λ c₄ → T-conv (≈,[] (≈-! (≈,[swap] ≈-∙ {!≈,[] ≈-refl ?!})) (∼,↦ (∼-! ∼,↦end))) (T-fwd S₁ c₃ c₄))
              (λ c₄ → T-conv (≈,[] (≈,[] (≈-! (≈,[end] _ ≈-∙ (≈,[end] _ ≈-∙ ≈,[end] _))) ∼-refl) (∼,↦ (∼-! ∼,↦end))) (T-fwd S₃ c₃ c₄))
  T-fwd (⅋⊗ S S₁ S₂ S₃) c₀ c₁ = {!!}
{-
  -}

  go : ∀ {δI}{I : Proto δI} → ⟨ I ⟩ → T⟨ I ⟩
  go (end x) = T-end x
  go (⅋-inp l P) = T-⅋-inp l (λ c₀ c₁ → go (P c₀ c₁))
  go {I = I}(⊗-out {c} {S₀} {S₁} l P) = T-conv e rPP
    where postulate c0 c1 : URI
          open [↦…]∈ l
          F = E Env./' lE , c0 ↦ « S₀ » , c1 ↦ « S₁ »
          J = I Proto./ lI ,[ F ]
          G = F /D there here /D here , c ↦ « S₀ ⊗ S₁ »
          K = J Proto./ heRe[] ,[ G ]
          rPP : T⟨ K ⟩
          rPP = T-⊗-reorg heRe[] (theRe here) heRe (go (P c0 c1))
          e : K ≈ I
          e = ≈,[] (≈,[end] (Ended-/* F)) (∼,↦ (∼,↦end ∼-∙ ∼,↦end)) ≈-∙ (≈-! (≈-/…,[…] l))
  go {I = I}(nu {S₀} {S₁} D P) = T-conv {!!} (T-cut {I = I'} D (sel₀ _ ,[ (ε , c ↦ 0₂) ] ,[ (ε , c' ↦ 1₂) ]) {!!} (λ c₀' → {!cPP!}) (λ c₁' → {!T-fwd!}))
    where postulate c c' c0 c1 : URI
          E   = ε , c0 ↦ « S₀ » , c1 ↦ « S₁ »
          E/* = ε , c0 ↦ end    , c1 ↦ end
          J = I ,[ E ]
          -- K = J / here ,[ E/* , c ↦ S₀ ⊗ S₁ ]
          K = I ,[ E/* ] ,[ E/* , c ↦ « S₀ ⊗ S₁ » ]
          gP : T⟨ J ⟩
          gP = go (P c0 c1)
          rPP : T⟨ K ⟩
          rPP = T-⊗-reorg {c = c} heRe[] (theRe here) heRe gP
          e : K ≈ I ,[ c ↦ S₀ ⊗ S₁ ]
          e = ≈,[] (≈,[end] _) (∼,↦ (∼,↦end ∼-∙ ∼,↦end))
          cPP : T⟨ I ,[ c ↦ S₀ ⊗ S₁ ] ⟩
          cPP = T-conv e rPP
          I' = I ,[ c ↦ S₀ ⊗ S₁ ] ,[ c' ↦ {!!} ]
  go (split σs A P₀ P₁) = T-split σs A (go P₀) (go P₁)
-}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
