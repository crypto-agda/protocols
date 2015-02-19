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
open import PTT.Dom hiding (∈♦₀)
import PTT.Session as Session
import PTT.Map as Map
import PTT.Env as Env
import PTT.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/[_]_; Ended)
open Proto   hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com ; ♦-cong₂ ; select ; Sel♦)
open import PTT.Term
open import PTT.Vars
open import PTT.Conversion

module PTT.Split where


EndItσ : ∀ {c δI δE}(b : 𝟚)(I : Proto δI)(σs : Selections δI)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
  → Env.Ended (Proto.lookup I lΔ [ lA ]≔' end) → Env.Ended (Proto.lookup (I []/[ b ] σs) lΔ [ lA ]≔' end)
EndItσ b I σs lΔ lA E/c = tr Env.Ended
  (! (ap (λ I → I [ lA ]≔' end) ([]/[]-lookup b I σs lΔ)
   ∙ ! ([]≔/[]≡ b (Proto.lookup I lΔ) (Proto.lookup σs lΔ) lA)))
  (End→/[] b (Proto.lookup I lΔ [ lA ]≔' end) (Proto.lookup σs lΔ) E/c)

EndIt/Ds : ∀ {c d δI δE δF}(I : Proto δI)(lΔ' : [ δF ]∈D δI)(lA' : d ∈D δF)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
  → Env.Ended (Proto.lookup I lΔ [ lA ]≔' end) → Env.Ended (Proto.lookup (I /D[ lΔ' >> lA' ]) lΔ [ lA ]≔' end)
EndIt/Ds I lΔ' lA' lΔ lA E/c with Proto.sameDoms? lΔ' lΔ
EndIt/Ds I lΔ' lA' lΔ lA E/c | inl x = tr Env.Ended (! (ap (λ I₁ → I₁ [ lA ]≔' end) (lookup-diff I lΔ' lΔ _ x))) E/c
EndIt/Ds I lΔ' lA' .lΔ' lA E/c | inr ⟨ refl , refl ⟩ = tr Env.Ended
   (! (ap (λ I → I [ lA ]≔' end) (lookup-same I lΔ' _) ∙ ≔'-com (Proto.lookup I lΔ') lA' lA))
   (End/D _ lA' E/c)

record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(l : [ d ↦ S ]∈ J)(l' : [ e ↦ T ]∈ J)
      → DifferentVars… ([↦]∈.l… l) ([↦]∈.l… l') → TC'⟨ J ⟩
      → TC'⟨ (J /D[ [↦]∈.lΔ l >> [↦]∈.lA l ] /D[ [↦]∈.lΔ l' >> [↦]∈.lA l' ]) ♦Proto' K ⟩
    cont-⊗ : ∀ {S T} → A ≡ S ⊗ T → ∀ {d e δ₀ δ₁}{J₀ : Proto δ₀}{J₁ : Proto δ₁}(l : [ d ↦ S ]∈ J₀)(l' : [ e ↦ T ]∈ J₁)
      → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩ → TC'⟨ ((J₀ / l ♦Proto' J₁ / l')) ♦Proto' K ⟩
    cont-𝟙 : A ≡ 𝟙' → ∀ {δs}{J : Proto δs} → TC'⟨ J ⟩ → TC'⟨ J ♦Proto' K ⟩
    cont-⊥ : A ≡ ⊥' → ∀ {δs}{J : Proto δs} → TC'⟨ J ⟩ → TC'⟨ J ♦Proto' K ⟩
    cont-! : ∀ {M S} → A ≡ act (send {M} S) → ∀ {d δI}{I : Proto δI}(m : M)(l : [ d ↦ S m ]∈ I) → TC'⟨ I ⟩
      → TC'⟨ I / l ♦Proto' K ⟩
    cont-? : ∀ {M S} → A ≡ act (recv {M} S) → ∀ {d δE δI}{I : Proto δI}{E : Env δE}
      (lI : [ E ]∈ I)(lA : d ∈D δE)(E/c : Env.Ended (E Env./D lA)) (C : (m : M) → TC'⟨ I [ []∈.lΔ lI >> lA ]≔ « S m » ⟩)
      → TC'⟨ I /D[ []∈.lΔ lI >> lA ] ♦Proto' K ⟩
open TC-Split


TC-∈Split : ∀ {δI δK c A}{I : Proto δI}{K : Proto δK} → TC-Split A K → (l : [ c ↦ A ]∈ I)
  → TC'⟨ I ⟩ → TC'⟨ I /… [↦]∈.l… l ♦Proto' K ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs A0 P₀ P₁) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈Split {I = I} cont (mk l Y) (TC-⊗-out (mk .l X) σs A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (♦-cong₂ (≈,[end] _) (≈,[end] _) ≈-∙ Sel♦ A0) ≈-refl)
  (cont-⊗ cont refl (mk (mk heRe[] heRe) _)
                    (mk (mk heRe[] heRe) _)
                    (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
TC-∈Split {δK = δK}{I = I}{K} cont (mk5 lΔ refl lA ↦A E/c) (TC-⊗-out {S₀ = S₀}{S₁} l₁ σs A0 P₀ P₁) | diff l/=l'
  with Map.lookup (Proto.lookup σs lΔ) lA
  | select {I = I / l₁} σs lΔ lA
  | select-com {I = I / l₁} σs lΔ lA
... | 0₂ | x | y = TC-⊗-out (∈♦₀ (move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l'))) (Selections♦ 0₂ σs δK)
    (tr (λ X → AtMost 0 X (Selections♦ 0₂ σs δK))
        (! (∈♦₀-compute (move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l')) ∙ ap (flip _♦Proto'_ K)
           (/D[>>]-/D[>>]≡ I lΔ ([↦]∈.lΔ l₁) lA ([↦]∈.lA l₁))))
        (atMost♦' 0₂ σs K (atMost/[>>] lΔ lA σs A0)))
    (λ c₀ → TC-conv (♦-cong₂ (≈,[] (≈-sym (/[]-/D[>>] 0₂ (I / l₁) σs lΔ lA)) ∼-refl) ≈-refl
                    ≈-∙ ≈-sym (≈-reflexive (ap (λ I → I []/₀ (Selections♦ 0₂ σs δK) ,[ ε , c₀ ↦ « S₀ » ])
                                           (∈♦₀-compute {I₁ = K} (move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l'))))
                    ≈-∙ ≈,[] (Selections♦'/same 0₂ σs) ∼-refl
                    ≈-∙ ≈-sym ♦-com, ≈-∙ ♦-cong₂ (≈,[] (≈-reflexive (ap (flip _[]/₀_ σs)
                       (/D[>>]-/D[>>]≡ I lΔ ([↦]∈.lΔ l₁) lA ([↦]∈.lA l₁)))) ∼-refl) ≈-refl))
       (TC-∈Split cont (there[]' (mk5 lΔ refl lA
           (! x ∙ ap (flip _‼_ lA) (diff-lookup _ (mk {l = mk _ E/c} {l' = l₁} l/=l')) ∙ ↦A)
           ( EndItσ 0₂ (I / l₁) σs lΔ lA (EndIt/Ds I ([↦]∈.lΔ l₁) ([↦]∈.lA l₁) lΔ lA E/c) )))
          (P₀ c₀)))
    (λ c₁ → TC-conv (≈,[] (y ≈-∙ ≈-sym (≈-reflexive (ap (flip _[]/₁_ (Selections♦ 0₂ σs δK))
                           (∈♦₀-compute (move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l'))))
                     ≈-∙ Selections♦'/not 1₂ σs
                     ≈-∙ ≈-reflexive (ap (flip _[]/₁_ σs) (/D[>>]-/D[>>]≡ I lΔ ([↦]∈.lΔ l₁) lA ([↦]∈.lA l₁))))) ∼-refl)
                    (P₁ c₁))
... | 1₂ | x | y = TC-⊗-out (∈♦₀ (move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l'))) (Selections♦ 1₂ σs δK)
    (tr (λ X → AtMost 0 X (Selections♦ 1₂ σs δK))
        (! (∈♦₀-compute (move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l')) ∙ ap (flip _♦Proto'_ K)
           (/D[>>]-/D[>>]≡ I lΔ ([↦]∈.lΔ l₁) lA ([↦]∈.lA l₁))))
        (atMost♦' 1₂ σs K (atMost/[>>] lΔ lA σs A0)))
    (λ c₀ → TC-conv (≈,[] (y ≈-∙ ≈-sym (≈-reflexive (ap (flip _[]/₀_ (Selections♦ 1₂ σs δK)) (∈♦₀-compute (move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l'))))
                     ≈-∙ Selections♦'/not 0₂ σs
                     ≈-∙ ≈-reflexive (ap (flip _[]/₀_ σs) (/D[>>]-/D[>>]≡ I lΔ ([↦]∈.lΔ l₁) lA ([↦]∈.lA l₁))))) ∼-refl)
                    (P₀ c₀))
    (λ c₁ → TC-conv (♦-cong₂ (≈,[] (≈-sym (/[]-/D[>>] 1₂ (I / l₁) σs lΔ lA)) ∼-refl) ≈-refl
                     ≈-∙ ≈-sym (≈-reflexive (ap (λ I → I []/₁ (Selections♦ 1₂ σs δK) ,[ ε , c₁ ↦ « S₁ » ]) (∈♦₀-compute {I₁ = K}(move (mk5 lΔ refl lA ↦A E/c) l₁ (mk l/=l'))))
                     ≈-∙ ≈,[] (Selections♦'/same 1₂ σs) ∼-refl
                     ≈-∙ ≈-sym ♦-com, ≈-∙ ♦-cong₂ (≈,[] (≈-reflexive (ap (flip _[]/₁_ σs)
                           (/D[>>]-/D[>>]≡ I lΔ ([↦]∈.lΔ l₁) lA ([↦]∈.lA l₁)))) ∼-refl) ≈-refl))
                    (TC-∈Split cont (mk5 (there lΔ) refl lA
                          (! x ∙ ap (flip _‼_ lA) (diff-lookup _ (mk {l = mk _ E/c}{l' = l₁} l/=l')) ∙ ↦A)
                          (EndItσ 1₂ (I / l₁) σs lΔ lA (EndIt/Ds I ([↦]∈.lΔ l₁) ([↦]∈.lA l₁) lΔ lA E/c))) (P₁ c₁)))
TC-∈Split cont l (TC-𝟙-out l₁ P) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split cont l (TC-𝟙-out .([_↦_]∈_.l… l) P) | same = cont-𝟙 cont refl P
TC-∈Split {I = I}{K} cont l (TC-𝟙-out l₁ P) | diff x = TC-𝟙-out (∈♦₀… {I₁ = K} (move… ([↦]∈.l… l) l₁ x))
  (TC-conv (≈-sym (≈-reflexive (∈♦₀-compute… (move… ([↦]∈.l… l) l₁ x))
           ≈-∙ ♦-cong₂ (/D[>>]-/D[>>] I ([↦]∈.lΔ l) ([↦…]∈.lΔ l₁) ([↦]∈.lA l) ([↦…]∈.lA l₁)) ≈-refl))
    (TC-∈Split cont (mk (move… l₁ ([↦]∈.l… l) (Diff-sym… x)) (move-E/c (Diff-sym… x) ([↦]∈.E/c l))) P))
TC-∈Split cont l (TC-⊥-inp (mk l₁ E/c) P) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split cont l (TC-⊥-inp (mk .([_↦_]∈_.l… l) E/c) P) | same = cont-⊥ cont refl P
TC-∈Split {I = I}{K} cont l (TC-⊥-inp (mk l₁ E/c) P) | diff x = TC-⊥-inp (∈♦₀ {I₁ = K} (move l (mk l₁ E/c) (mk x)))
  (TC-conv (≈-sym (≈-reflexive (∈♦₀-compute (move l (mk l₁ E/c) (mk x)))
           ≈-∙ ♦-cong₂ (/D[>>]-/D[>>] I ([↦]∈.lΔ l) ([↦…]∈.lΔ l₁) ([↦]∈.lA l) ([↦…]∈.lA l₁)) ≈-refl))
     (TC-∈Split cont (move (mk l₁ E/c) l (mk (Diff-sym… x))) P))
TC-∈Split cont l (TC-?-inp (mk l₁ E/c) P) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split {I = I} cont (mk l E/c') (TC-?-inp {c} (mk .l E/c) P) | same = TC-conv
  ((♦-cong₂ (≈,[end] _) ≈-refl))
  (cont-? cont refl {I = I /… l ,[ c ↦end]} heRe[] here _ (λ m → P m ))
TC-∈Split {I = I}{K}cont l (TC-?-inp (mk l₁ E/c) P) | diff x = TC-?-inp (∈♦₀ {I₁ = K} (move l (mk l₁ E/c) (mk x))) λ m →
  TC-conv (≈-trans ♦-com,
          (≈,[] (≈-sym (≈-trans (≈-reflexive (∈♦₀-compute (move l (mk l₁ E/c) (mk x))))
          (♦-cong₂ (/D[>>]-/D[>>] I ([↦]∈.lΔ l) ([↦…]∈.lΔ l₁) ([↦]∈.lA l) ([↦…]∈.lA l₁))
          ≈-refl)))
          ∼-refl))
    (TC-∈Split cont (there[]' (move (mk l₁ E/c) l (mk (Diff-sym… x)))) (P m))
    -- (TC-∈Split cont (mk (there…' (move[…] l₁ ([↦]∈.l… l) (Diff-sym… x))) ([↦]∈.E/c l)) (P m))
TC-∈Split cont l (TC-!-out (mk l₁ E/c) m P) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split cont (mk l E/c') (TC-!-out (mk .l E/c) m P) | same = TC-conv
  (♦-cong₂ (≈,[end] _) ≈-refl)
 (cont-! cont refl m (mk (mk heRe[] heRe) _)  P )
TC-∈Split {I = I}{K} cont l (TC-!-out (mk l₁ E/c) m P) | diff x = TC-!-out (∈♦₀ {I₁ = K} (move l (mk l₁ E/c) (mk x))) m
  (TC-conv (≈-trans ♦-com,
           (≈,[] (≈-sym (≈-trans (≈-reflexive (∈♦₀-compute (move l (mk l₁ E/c) (mk x))))
           (♦-cong₂ (/D[>>]-/D[>>] I ([↦]∈.lΔ l) ([↦…]∈.lΔ l₁) ([↦]∈.lA l) ([↦…]∈.lA l₁))
           ≈-refl)))
           ∼-refl))
    (TC-∈Split cont (there[]' (move (mk l₁ E/c) l (mk (Diff-sym… x)))) P))
    --(TC-∈Split cont {!there[]' {!mk (there…' (move[…] l₁ ([↦]∈.l… l) (Diff-sym… x))) ([↦]∈.E/c l)!} P))
TC-∈Split cont (mk l E/c) (TC-⅋-inp l₁ P) with sameVar? l ([↦]∈.l… l₁)
TC-∈Split cont (mk l E/c) (TC-⅋-inp (mk .l E/c₁) P) | same = TC-conv
  ((♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl))
  (cont-⅋ cont refl (mk (mk (theRe[] here) heRe) _)
                    (mk (mk heRe[] heRe) _)
                    (diff-ten (t/h _)) (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split {I = I}{K} cont (mk l E/c) (TC-⅋-inp (mk l₁ X) P) | diff x = TC-⅋-inp (∈♦₀ {I₁ = K} (move (mk l E/c) (mk l₁ X) (mk x))) λ c₀ c₁ →
  TC-conv (≈-trans ♦-com,
         (≈,[] (≈-trans ♦-com,
         (≈,[] (≈-sym (≈-trans (≈-reflexive (∈♦₀-compute (move (mk l E/c) (mk l₁ X) (mk x))))
         (♦-cong₂ (/D[>>]-/D[>>] I ([↦…]∈.lΔ l) ([↦…]∈.lΔ l₁) ([↦…]∈.lA l) ([↦…]∈.lA l₁))
         ≈-refl)))
         ∼-refl))
         ∼-refl))
  (TC-∈Split cont (there[]' (there[]' (move (mk l₁ X) (mk l E/c) (mk (Diff-sym… x))))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim (Map.All∈' (Proto.All[]∈ ([↦]∈.lI l) E) ([↦]∈.lE l))
TC-∈Split {I = I} cont (mk5 lΔ ↦Δ lA ↦A E/c) (TC-split σs A1 P P₁)
    with Map.lookup (Proto.lookup σs lΔ) lA
    | select {I = I} σs lΔ lA
    | select-com {I = I} σs lΔ lA
TC-∈Split {δK = δK}{I = I}{K} cont (mk5 lΔ refl lA ↦A E/c) (TC-split σs A1 P P₁)
  | 0₂ | x | y = TC-split (Selections♦ 0₂ σs δK) (atMost♦' 0₂ σs K (atMost/[>>] lΔ lA σs A1))
  (TC-conv (≈-trans (♦-cong₂ (≈-sym (/[]-/D[>>] 0₂ I σs lΔ lA)) ≈-refl)
                    (≈-sym (Selections♦'/same {I = I /D[ lΔ >> lA ]}{K} 0₂ σs)))
           (TC-∈Split cont (mk5 lΔ refl lA (! x ∙ ↦A) (EndItσ 0₂ I σs lΔ lA E/c)) P))
  (TC-conv (≈-trans y (≈-sym (Selections♦'/not {I = I /D[ lΔ >> lA ]} {K} 1₂ σs))) P₁)
TC-∈Split {δK = δK}{I = I}{K} cont (mk5 lΔ refl lA ↦A E/c) (TC-split σs A1 P P₁)
  | 1₂ | x | y = TC-split (Selections♦ 1₂ σs δK) (atMost♦' 1₂ σs K (atMost/[>>] lΔ lA σs A1))
  (TC-conv (≈-trans y (≈-sym (Selections♦'/not {I = I /D[ lΔ >> lA ]}{K} 0₂ σs))) P)
  (TC-conv (≈-trans (♦-cong₂ (≈-sym (/[]-/D[>>] 1₂ I σs lΔ lA)) ≈-refl)
                    (≈-sym (Selections♦'/same {I = I /D[ lΔ >> lA ]}{K} 1₂ σs)))
           (TC-∈Split cont (mk5 lΔ refl lA (! x ∙ ↦A) (EndItσ 1₂ I σs lΔ lA E/c)) P₁))

{-
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

-}



module _ {δK}{K : Proto δK} where
  TC-∈! : ∀ {δI c A S}{I : Proto δI}(l : [ c ↦ act (send {A} S) ]∈ I)
    → TC'⟨ I ⟩
    → (∀ {d δI}{I : Proto δI}(m : A)(l : [ d ↦ S m ]∈ I) → TC'⟨ I ⟩ → TC'⟨ I / l ♦Proto' K ⟩)
    → TC'⟨ I / l ♦Proto' K  ⟩
  TC-∈! l p cont = TC-∈Split cont' l p -- TC-∈Split cont' (mk l ?)
    where
      cont' : TC-Split _ K
      cont-⅋ cont' () l₁ l' x₁ x₂
      cont-⊗ cont' () l₁ l' x₁ x₂
      cont-𝟙 cont' () p
      cont-⊥ cont' () p
      cont-! cont' refl m l₁ x₁ = cont m l₁ x₁
      cont-? cont' () lI lA E/c C

  TC-∈? : ∀ {δI c A S}{I : Proto δI}(l : [ c ↦ act (recv {A} S) ]∈ I)
    → TC'⟨ I ⟩
    → (∀ {d δE δI}{I : Proto δI}{E : Env δE}
        (lI : [ E ]∈ I)(lA : d ∈D δE)(E : Env.Ended (E Env./D lA))(C : (m : A) → TC'⟨ I [ []∈.lΔ lI >> lA ]≔ « S m » ⟩)
        → TC'⟨ I /D[ []∈.lΔ lI >> lA ] ♦Proto' K ⟩)
    → TC'⟨ I / l ♦Proto' K  ⟩
  TC-∈? l p cont = TC-∈Split cont' l p -- TC-∈Split cont' (mk l ?)
    where
      cont' : TC-Split _ K
      cont-⅋ cont' () l₁ l' x₁ x₂
      cont-⊗ cont' () l₁ l' x₁ x₂
      cont-𝟙 cont' () p
      cont-⊥ cont' () p
      cont-! cont' () m l₁ x₁
      cont-? cont' refl lI lA E/c C = cont lI lA E/c C

  TC-∈⅋ : ∀ {δI c A B}{I : Proto δI}(l : [ c ↦ A ⅋ B ]∈ I)
    → TC'⟨ I ⟩
    → (∀ {d e δJ}{J : Proto δJ} (l : [ d ↦ A ]∈ J)(l' : [ e ↦  B ]∈ J) → DifferentVars… ([↦]∈.l… l) ([↦]∈.l… l') → TC'⟨ J ⟩
       → TC'⟨ ((J /… [↦]∈.l… l) /D[ [↦]∈.lΔ l' >> [↦]∈.lA l' ]) ♦Proto' K ⟩)
    → TC'⟨ I / l ♦Proto' K  ⟩
  TC-∈⅋ l p cont = TC-∈Split cont' l p -- TC-∈Split cont' (mk l ?)
    where
      cont' : TC-Split _ K
      cont-⅋ cont' refl l₁ l' x₁ x₂ = cont l₁ l' x₁ x₂
      cont-⊗ cont' () l₁ l' x₁ x₂
      cont-𝟙 cont' () p
      cont-⊥ cont' () p
      cont-! cont' () m l₁ x₁
      cont-? cont' () lI lA E/c C

  TC-∈⊗ : ∀ {δI c A B}{I : Proto δI}(l : [ c ↦ A ⊗ B ]∈ I)
    → TC'⟨ I ⟩
    → (∀ {d e δJ₀ δJ₁}{J₀ : Proto δJ₀}{J₁ : Proto δJ₁}
         (l₀ : [ d ↦ A ]∈ J₀)(l₁ : [ e ↦ B ]∈ J₁) → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩
          → TC'⟨ (J₀ / l₀ ♦Proto' J₁ / l₁) ♦Proto' K ⟩)
    → TC'⟨ I / l ♦Proto' K  ⟩
  TC-∈⊗ l p cont = TC-∈Split cont' l p -- TC-∈Split cont' (mk l ?)
    where
      cont' : TC-Split _ K
      cont-⅋ cont' () l₁ l' x₁ x₂
      cont-⊗ cont' refl l₁ l' x₁ x₂ = cont l₁ l' x₁ x₂
      cont-𝟙 cont' () p
      cont-⊥ cont' () p
      cont-! cont' () m l₁ x₁
      cont-? cont' () lI lA E/c C

  TC-∈𝟙 : ∀ {δI c}{I : Proto δI}(l : [ c ↦ 𝟙' ]∈ I)
    → TC'⟨ I ⟩
    → (∀ {δJ}{J : Proto δJ} → TC'⟨ J ⟩
       → TC'⟨ J ♦Proto' K ⟩)
    → TC'⟨ I / l ♦Proto' K  ⟩
  TC-∈𝟙 l p cont = TC-∈Split cont' l p
    where
      cont' : TC-Split _ K
      cont-⅋ cont' () l₁ l' x₁ x₂
      cont-⊗ cont' () l₁ l' x₁ x₂
      cont-𝟙 cont' refl p = cont p
      cont-⊥ cont' () p
      cont-! cont' () m l₁ x₁
      cont-? cont' () lI lA E/c C

  TC-∈⊥ : ∀ {δI c}{I : Proto δI}(l : [ c ↦ ⊥' ]∈ I)
    → TC'⟨ I ⟩
    → (∀ {δJ}{J : Proto δJ} → TC'⟨ J ⟩
       → TC'⟨ J ♦Proto' K ⟩)
    → TC'⟨ I / l ♦Proto' K  ⟩
  TC-∈⊥ l p cont = TC-∈Split cont' l p
    where
      cont' : TC-Split _ K
      cont-⅋ cont' () l₁ l' x₁ x₂
      cont-⊗ cont' () l₁ l' x₁ x₂
      cont-𝟙 cont' () p
      cont-⊥ cont' refl p = cont p
      cont-! cont' () m l₁ x₁
      cont-? cont' () lI lA E/c C
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
