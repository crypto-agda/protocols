{-# OPTIONS --copatterns #-}
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Nat

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J)
open import PTT.Dom
import PTT.Session as Session
import PTT.Map as Map
import PTT.Env as Env
import PTT.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/[_]_; Ended)
open Proto   hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com)
open import PTT.Term
open import PTT.Vars
module PTT.Split where

record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(l : [ d ↦ S …]∈ J)(l' : [ e ↦ T …]∈ J)
      → DifferentVars… l l' → TC'⟨ J ⟩
      → TC'⟨ (J /D[ [↦…]∈.lΔ l >> [↦…]∈.lA l ] /D[ [↦…]∈.lΔ l' >> [↦…]∈.lA l' ]) ♦Proto' K ⟩
    cont-⊗ : ∀ {S T} → A ≡ S ⊗ T → ∀ {d e δ₀ δ₁}{J₀ : Proto δ₀}{J₁ : Proto δ₁}(l : [ d ↦ S …]∈ J₀)(l' : [ e ↦ T …]∈ J₁)
      → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩ → TC'⟨ (J₀ /… l ♦Proto' J₁ /… l') ♦Proto' K ⟩
    cont-! : ∀ {M S} → A ≡ act (send {M} S) → ∀ {d δI}{I : Proto δI}(m : M)(l : [ d ↦ S m …]∈ I) → TC'⟨ I ⟩ → TC'⟨ I /… l ♦Proto' K ⟩
    cont-? : ∀ {M S} → A ≡ act (recv {M} S) → ∀ {d δE δI}{I : Proto δI}{E : Env δE}
      (lI : [ E ]∈ I)(lA : d ∈D δE)(C : (m : M) → TC'⟨ I [ []∈.lΔ lI >> lA ]≔ « S m » ⟩)
      → TC'⟨ I /D[ []∈.lΔ lI >> lA ] ♦Proto' K ⟩
open TC-Split


TC-∈Split : ∀ {δI δK c A}{I : Proto δI}{K : Proto δK} → TC-Split A K → (l : [ c ↦ A …]∈ I)
  → TC'⟨ I ⟩ → TC'⟨ I /… l ♦Proto' K ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? l l₁
TC-∈Split {I = I} cont l (TC-⊗-out .l σs σE A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (≈-trans (♦-cong₂
                      (≈-sym (≈-trans (/[]-/D[>>] 0₂ I σs ([↦…]∈.lΔ l)([↦…]∈.lA l))
                             {!thmA!}))
                      {!!})
{-(♦-cong₂ (≈-trans (≈-sym {!thmA {!!}!}) {!!})
                             {!!})-}
                    (Sel♦ σs))
   ≈-refl)
  {-(
  (♦-cong₂ (≈-trans (♦-cong₂ (≈,[end] ⟨ mapAll (λ _ → _) _ , _ ⟩)
                             (≈,[end] ⟨ (mapAll (λ _ → _) _) , _ ⟩))
             (≈-trans (Sel♦ σs) ([≔]-ext _ ([↦…]∈'.lI l) ({!!} ∼-End {!!}))))
           ≈-refl) ) -}
  (cont-⊗ cont refl (mk heRe[] heRe)
                    (mk heRe[] heRe)
                    (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) | diff x = {!!}
TC-∈Split cont l (TC-?-inp (mk l₁ E/c) P) with sameVar? l l₁
TC-∈Split {I = I} cont l (TC-?-inp {c} (mk .l E/c) P) | same = TC-conv
  ((♦-cong₂ (≈-trans (≈,[end] _) ([≔]-ext _ ([↦…]∈.lI l) (/*-End _ ∼-End E/c))) ≈-refl))
  (cont-? cont refl {I = I [/…] l ,[ c ↦end]} heRe[] here (λ m → P m ))
TC-∈Split cont l (TC-?-inp (mk l₁ E/c) P) | diff x = {!!}
TC-∈Split cont l (TC-!-out (mk l₁ E/c) m P) with sameVar? l l₁
TC-∈Split cont l (TC-!-out (mk .l E/c) m P) | same = TC-conv
  (♦-cong₂ (≈-trans (≈,[end] _) ([≔]-ext _ ([↦…]∈.lI l) (/*-End _ ∼-End E/c))) ≈-refl)
 (cont-! cont refl m (mk heRe[] heRe)  P )
--TC-∈Split cont l (TC-!-out (mk .l E/c) m P) | same = TC-conv
--  (♦-cong₂ {!!} ≈-refl)
-- (cont-! cont refl m (mk heRe (mk here refl))  (TC-conv {!!} P) )
TC-∈Split {I = I}{K} cont l (TC-!-out (mk l₁ E/c) m P) | diff x = TC-!-out (mk (∈♦₀… {I₁ = K} (move… l l₁ x)) E/c) m
  (TC-conv (≈-trans ♦-com,
           (≈,[] (≈-sym (≈-trans (∈♦₀-compute[…] (move… l l₁ x))
           (♦-cong₂ ([/]-/D[>>] I ([↦…]∈.lΔ l) ([↦…]∈.lΔ l₁) ([↦…]∈.lA l))
           ≈-refl)))
           ∼-refl))
    (TC-∈Split cont (there…' (move[…] l₁ l (Diff-sym… x))) P))
TC-∈Split cont l (TC-⅋-inp l₁ P) with sameVar? l ([↦]∈.l… l₁)
TC-∈Split cont l (TC-⅋-inp (mk .l E/c₁) P) | same = TC-conv
  ((♦-cong₂ (≈-trans (≈,[end] _) (≈-trans (≈,[end] _) ([≔]-ext _ ([↦…]∈.lI l) (/*-End _ ∼-End E/c₁)))) ≈-refl))
  (cont-⅋ cont refl (mk (theRe[] here) heRe)
                    (mk heRe[] heRe)
                    (diff-ten (t/h _)) (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split {I = I}{K} cont l (TC-⅋-inp (mk l₁ X) P) | diff x = TC-⅋-inp (mk (∈♦₀… {I₁ = K} (move… l l₁ x)) X) λ c₀ c₁ →
  TC-conv
         (≈-trans ♦-com,
         (≈,[] (≈-trans ♦-com,
         (≈,[] (≈-sym (≈-trans (∈♦₀-compute[…] (move… l l₁ x))
         (♦-cong₂ ([/]-/D[>>] I ([↦…]∈.lΔ l) ([↦…]∈.lΔ l₁) ([↦…]∈.lA l))
         ≈-refl)))
         ∼-refl))
         ∼-refl))
  (TC-∈Split cont (there…' (there…' (move[…] l₁ l (Diff-sym… x)))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim {!NES cont (Map.All∈' (Proto.All∈' E ([↦…]∈.lI l)) ([↦…]∈.lE l))!}
TC-∈Split cont l (TC-mix lF lG lF/=lG P) with sameDoms? ([↦…]∈.lΔ l) ([]∈.lΔ lF) | sameDoms? ([↦…]∈.lΔ l) ([]∈.lΔ lG)
TC-∈Split {δK = δK}{I = I}{K = K}cont (mk ⟨ lΔ R[]⟩ ⟨ lA , ↦A ⟩) (TC-mix {δG = δG}{G = G} ⟨ .lΔ R[]⟩ lG lF/=lG P) | inr ⟨ refl , refl ⟩ | Y
  = TC-mix ⟨ []∈♦₀ {δF = δK} lΔ          , lookup-[]∈♦'₀ _ K lΔ ⟩
           ⟨ []∈♦₀ {δF = δK} ([]∈.lΔ lG) , lookup-[]∈♦'₀ _ K ([]∈.lΔ lG) ∙ lookup-diff _ _ _ _ lF/=lG ∙ []∈.↦Δ lG ⟩
    ([]∈♦₀-diff {δF = δK} lF/=lG)
   (TC-conv (≈-trans ♦-com, (≈,[] (≈-reflexive lemma₀)
               (∼-reflexive ([∈♦₀]≔' (Proto.lookup I lΔ) G lA end ∙ ap (flip _♦Map_ G) (! lookup/D[>>] I lΔ lA )))))
   (TC-∈Split cont (mk heRe[] ⟨ ∈♦₀ {F = δG} lA , lookup-∈♦₀ _ G lA ∙ ↦A ⟩) P))
   where
     lemma₀ : (I /Ds lΔ) /Ds  ([]∈.lΔ lG) ♦Proto' K
         ≡ (I /D[ lΔ >> lA ] ♦Proto' K) /Ds []∈♦₀ {δF = δK} lΔ /Ds ([]∈♦₀ {δF = δK} ([_]∈_.lΔ lG))
     lemma₀ rewrite ! /Ds>>-red {x = end} I lΔ lA
                  | /Ds-[]∈♦'₀ {I = I /D[ lΔ >> lA ] /Ds lΔ} ([]∈.lΔ lG) K
                  | /Ds-[]∈♦'₀ {I = I /D[ lΔ >> lA ]} lΔ K = refl
TC-∈Split cont l (TC-mix lF lG lF/=lG P) | inl x | inr y = {!!}
TC-∈Split cont l (TC-mix lF lG lF/=lG P) | inl x | inl x₁ = {!!}

{- 
TC-mix {!!} {!!} {!!}
   (TC-conv {!!}
     (TC-∈Split cont {!!} P))
-}

{-
-- move logic to ⊗
TC-∈Split {I = I} cont (mk4 lΔ ↦Δ lA ↦A) (TC-split σs A1 P P₁)
    with Map.lookup (Proto.lookup σs lΔ) lA
    | select {I = I} σs lΔ lA
    | select-com {I = I} σs lΔ lA
TC-∈Split {δK = δK}{I = I}{K} cont (mk4 lΔ refl lA ↦A) (TC-split σs A1 P P₁)
  | 0₂ | x | y = TC-split (Selections♦ 0₂ σs δK) (atMost♦ 0₂ σs δK A1)
  (TC-conv (≈-trans (♦-cong₂ (≈-sym (/[]-/D[>>] 0₂ I σs lΔ lA)) ≈-refl)
                    (≈-sym (Selections♦'/same {I = I /D[ lΔ >> lA ]}{K} 0₂ σs)))
           (TC-∈Split cont (mk4 lΔ refl lA (! x ∙ ↦A)) P))
  (TC-conv (≈-trans y (≈-sym (Selections♦'/not {I = I /D[ lΔ >> lA ]} {K} 1₂ σs))) P₁)
TC-∈Split {δK = δK}{I = I}{K} cont (mk4 lΔ refl lA ↦A) (TC-split σs A1 P P₁)
  | 1₂ | x | y = TC-split (Selections♦ 1₂ σs δK) (atMost♦ 1₂ σs δK A1)
  (TC-conv (≈-trans y (≈-sym (Selections♦'/not {I = I /D[ lΔ >> lA ]}{K} 0₂ σs))) P)
  (TC-conv (≈-trans (♦-cong₂ (≈-sym (/[]-/D[>>] 1₂ I σs lΔ lA)) ≈-refl)
                    (≈-sym (Selections♦'/same {I = I /D[ lΔ >> lA ]}{K} 1₂ σs)))
           (TC-∈Split cont (mk4 lΔ refl lA (! x ∙ ↦A)) P₁))
-}

TC-∈! : ∀ {δI δK c A S}{I : Proto δI}{K : Proto δK}(l : [ c ↦ act (send {A} S) …]∈ I)
  → TC'⟨ I ⟩
  → (∀ {d δI}{I : Proto δI}(m : A)(l : [ d ↦ S m …]∈ I) → TC'⟨ I ⟩ → TC'⟨ I /… l ♦Proto' K ⟩)
  → TC'⟨ I /… l ♦Proto' K ⟩
TC-∈! {S = S}{K = K} l p cont = TC-∈Split cont' l p
  where
    cont' : TC-Split _ K
    cont-⅋ cont' () l₁ l' x₁ x₂
    cont-⊗ cont' () l₁ l' x₁ x₂
    cont-! cont' refl m l₁ x₁ = cont m l₁ x₁
    cont-? cont' () lI lA C

TC-∈? : ∀ {δI δK c A S}{I : Proto δI}{K : Proto δK}(l : [ c ↦ act (recv {A} S) …]∈ I)
  → TC'⟨ I ⟩
  → (∀ {d δE δI}{I : Proto δI}{E : Env δE}
      (lI : [ E ]∈ I)(lA : d ∈D δE)(C : (m : A) → TC'⟨ I [ []∈.lΔ lI >> lA ]≔ « S m » ⟩)
      → TC'⟨ I /D[ []∈.lΔ lI >> lA ] ♦Proto' K ⟩)
  → TC'⟨ I /… l ♦Proto' K ⟩
TC-∈? {S = S}{K = K} l p cont = TC-∈Split cont' l p
  where
    cont' : TC-Split (act (com IN S)) K
    cont-⅋ cont' () l₁ l' x₁ x₂
    cont-⊗ cont' () l₁ l' x₁ x₂
    cont-! cont' () m l₁ x₁
    cont-? cont' refl lI lA C = cont lI lA C

{-
-}

TC-∈⅋ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⅋ B …]∈ I)
  → TC'⟨ I ⟩
  → (∀ {d e δJ}{J : Proto δJ} (l : [ d ↦ A …]∈ J)(l' : [ e ↦  B …]∈ J) → DifferentVars… l l' → TC'⟨ J ⟩
     → TC'⟨ ((J /… l) /D[ [↦…]∈.lΔ l' >> [↦…]∈.lA l' ]) ♦Proto' K ⟩)
  →  TC'⟨ I /… l ♦Proto' K ⟩
TC-∈⅋ {A = A}{B}{K = K} l p cont = TC-∈Split cont' l p
  where
    cont' : TC-Split (A ⅋ B) K
    cont-⅋ cont' refl l₁ l' x₁ x₂ = cont l₁ l' x₁ x₂
    cont-⊗ cont' () l₁ l' x₁ x₂
    cont-! cont' () m l₁ x₁
    cont-? cont' () lI lA C

TC-∈⊗ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⊗ B …]∈ I)
  → TC'⟨ I ⟩
  → (∀ {d e δJ₀ δJ₁}{J₀ : Proto δJ₀}{J₁ : Proto δJ₁}
       (l₀ : [ d ↦ A …]∈ J₀)(l₁ : [ e ↦ B …]∈ J₁) → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩
        → TC'⟨ (J₀ /… l₀ ♦Proto' J₁ /… l₁) ♦Proto' K ⟩)
  → TC'⟨ I /… l ♦Proto' K ⟩
TC-∈⊗ {A = A}{B}{K = K} l p cont = TC-∈Split cont' l p
  where
    cont' : TC-Split (A ⊗ B) K
    cont-⅋ cont' () l₁ l' x₁ x₂
    cont-⊗ cont' refl l₁ l' x₁ x₂ = cont l₁ l' x₁ x₂
    cont-! cont' () m l₁ x₁
    cont-? cont' () lI lA C
