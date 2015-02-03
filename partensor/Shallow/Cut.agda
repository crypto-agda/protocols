{-# OPTIONS --copatterns #-}
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
open Env     hiding (_/₀_; _/₁_; _/[_]_; Ended)
open Proto   hiding ()
open import partensor.Shallow.Equiv' hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com)
open import partensor.Shallow.Term
open import partensor.Shallow.Vars

module partensor.Shallow.Cut where

record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    NES : ¬ (Session.Ended A)
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(l : [ d ↦ S …]∈' J)(l' : [ e ↦ T …]∈' J)
      → DifferentVars… l l' → TC'⟨ J ⟩
      → TC'⟨ (J /D[ [↦…]∈'.lΔ l >> [↦…]∈'.lA l ] /D[ [↦…]∈'.lΔ l' >> [↦…]∈'.lA l' ]) ♦Proto' K ⟩
    cont-⊗ : ∀ {S T} → A ≡ S ⊗ T → ∀ {d e δ₀ δ₁}{J₀ : Proto δ₀}{J₁ : Proto δ₁}(l : [ d ↦ S …]∈' J₀)(l' : [ e ↦ T …]∈' J₁)
      → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩ → TC'⟨ (J₀ /…' l ♦Proto' J₁ /…' l') ♦Proto' K ⟩
open TC-Split


TC-∈Split : ∀ {δI δK c A}{I : Proto δI}{K : Proto δK} → TC-Split A K → (l : [ c ↦ A …]∈' I)
  → TC'⟨ I ⟩ → TC'⟨ I /…' l ♦Proto' K ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? l l₁
TC-∈Split {I = I} cont l (TC-⊗-out .l σs σE A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (≈-trans (♦-cong₂
                      (≈-sym (≈-trans (/[]-/D[>>] 0₂ I σs ([↦…]∈'.lΔ l)([↦…]∈'.lA l))
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
  (cont-⊗ cont refl (mk (mk Doms'.here refl) (mk here refl))
                    (mk (mk Doms'.here refl) (mk here refl))
                    (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) | diff x = {!!}
TC-∈Split cont l (TC-⅋-inp l₁ P) with sameVar? l ([↦]∈'.l… l₁)
TC-∈Split cont l (TC-⅋-inp (mk .l E/c₁) P) | same = TC-conv
  ((♦-cong₂ (≈-trans (≈,[end] _) (≈-trans (≈,[end] _) ([≔]-ext _ ([↦…]∈'.lI l) (/*-End _ ∼-End E/c₁)))) ≈-refl))
  (cont-⅋ cont refl (mk (mk (Doms'.there Doms'.here) refl) (mk here refl))
                    (mk (mk Doms'.here refl) (mk here refl))
                    (diff-ten (t/h _)) (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split {I = I}{K} cont l (TC-⅋-inp (mk l₁ X) P) | diff x = TC-⅋-inp (mk (∈♦₀… {I₁ = K} (move… l l₁ x)) X) λ c₀ c₁ →
  TC-conv
         (≈-trans ♦-com,
         (≈,[] (≈-trans ♦-com,
         (≈,[] (≈-sym (≈-trans (∈♦₀-compute[…] (move… l l₁ x))
         (♦-cong₂ ([/]-/D[>>] I ([↦…]∈'.lΔ l) ([↦…]∈'.lΔ l₁) ([↦…]∈'.lA l))
         ≈-refl)))
         ∼-refl))
         ∼-refl))
  (TC-∈Split cont (there…' (there…' (move[…] l₁ l (Diff-sym… x)))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim (NES cont (Map.All∈' (Proto.All∈' E ([↦…]∈'.lI l)) ([↦…]∈'.lE l)))
TC-∈Split cont l (TC-mix lF lG lF/=lG P) with sameDoms? ([↦…]∈'.lΔ l) ([]∈'.lΔ lF) | sameDoms? ([↦…]∈'.lΔ l) ([]∈'.lΔ lG)
TC-∈Split {δK = δK}{I = I}{K = K}cont (mk (mk lΔ refl) (mk lA refl)) (TC-mix {δG = δG}{G = G} (mk .lΔ refl) lG lF/=lG P) | inj₂ ⟨ refl , refl ⟩ | Y
  = TC-mix (mk ([]∈♦₀ {δF = δK}lΔ) (lookup-[]∈♦'₀ _ K lΔ))
           (mk ([]∈♦₀ {δF = δK} ([]∈'.lΔ lG)) (lookup-[]∈♦'₀ _ K ([]∈'.lΔ lG) ∙ lookup-diff _ _ _ _ lF/=lG ∙ []∈'.↦Δ lG))
    ([]∈♦₀-diff {δF = δK} lF/=lG)
   (TC-conv (≈-trans ♦-com, (≈,[] (≈-reflexive lemma₀)
               (∼-reflexive ([∈♦₀]≔' (Proto.lookup I lΔ) G lA end ∙ ap (flip _♦Map_ G) (! lookup/D[>>] I lΔ lA )))))
   (TC-∈Split cont (mk (mk Doms'.here refl) (mk (∈♦₀ {F = δG} lA) (lookup-∈♦₀ _ G lA))) P))
   where
     lemma₀ : (I /Ds lΔ) /Ds  ([]∈'.lΔ lG) ♦Proto' K
         ≡ (I /D[ lΔ >> lA ] ♦Proto' K) /Ds []∈♦₀ {δF = δK} lΔ /Ds ([]∈♦₀ {δF = δK} ([_]∈'_.lΔ lG))
     lemma₀ rewrite ! /Ds>>-red I lΔ lA
                  | /Ds-[]∈♦'₀ {I = I /D[ lΔ >> lA ] /Ds lΔ} ([]∈'.lΔ lG) K
                  | /Ds-[]∈♦'₀ {I = I /D[ lΔ >> lA ]} lΔ K = refl

TC-∈Split cont l (TC-mix lF lG lF/=lG P) | inj₁ x | inj₂ y = {!!}
TC-∈Split cont l (TC-mix lF lG lF/=lG P) | inj₁ x | inj₁ x₁ = {!!}

{- 
TC-mix {!!} {!!} {!!}
   (TC-conv {!!}
     (TC-∈Split cont {!!} P))
-}
TC-∈Split {I = I} cont (mk (mk lΔ ↦Δ) (mk lA ↦A)) (TC-split σs A1 P P₁)
    with Map.lookup (Proto.lookup σs lΔ) lA
    | select {I = I} σs lΔ lA
    | select-com {I = I} σs lΔ lA
TC-∈Split {δK = δK}{I = I}{K} cont (mk (mk lΔ refl) (mk lA refl)) (TC-split σs A1 P P₁)
  | 0₂ | x | y = TC-split (Selections♦ 0₂ σs δK) (atMost♦ 0₂ σs δK A1)
  (TC-conv (≈-trans (♦-cong₂ (≈-sym (/[]-/D[>>] 0₂ I σs lΔ lA)) ≈-refl)
                    (≈-sym (Selections♦'/same {I = I /D[ lΔ >> lA ]}{K} 0₂ σs)))
           (TC-∈Split cont ((mk (mk lΔ refl) (mk lA (! x)))) P))
  (TC-conv (≈-trans y (≈-sym (Selections♦'/not {I = I /D[ lΔ >> lA ]} {K} 1₂ σs))) P₁)
TC-∈Split {δK = δK}{I = I}{K} cont (mk (mk lΔ refl) (mk lA refl)) (TC-split σs A1 P P₁)
  | 1₂ | x | y = TC-split (Selections♦ 1₂ σs δK) (atMost♦ 1₂ σs δK A1)
  (TC-conv (≈-trans y (≈-sym (Selections♦'/not {I = I /D[ lΔ >> lA ]}{K} 0₂ σs))) P)
  (TC-conv (≈-trans (♦-cong₂ (≈-sym (/[]-/D[>>] 1₂ I σs lΔ lA)) ≈-refl)
                    (≈-sym (Selections♦'/same {I = I /D[ lΔ >> lA ]}{K} 1₂ σs)))
           (TC-∈Split cont ((mk (mk lΔ refl) (mk lA (! x)))) P₁))


TC-∈⅋ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⅋ B …]∈' I)
  → TC'⟨ I ⟩
  → (∀ {d e δJ}{J : Proto δJ} (l : [ d ↦ A …]∈' J)(l' : [ e ↦  B …]∈' J) → DifferentVars… l l' → TC'⟨ J ⟩
     → TC'⟨ ((J /…' l) /D[ [↦…]∈'.lΔ l' >> [↦…]∈'.lA l' ]) ♦Proto' K ⟩)
  →  TC'⟨ I /…' l ♦Proto' K ⟩
TC-∈⅋ = {!!}

TC-∈⊗ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⊗ B …]∈' I)
  → TC'⟨ I ⟩
  → (∀ {d e δJ₀ δJ₁}{J₀ : Proto δJ₀}{J₁ : Proto δJ₁}
       (l₀ : [ d ↦ A …]∈' J₀)(l₁ : [ e ↦ B …]∈' J₁) → TC'⟨ J₀ ⟩ → TC'⟨ J₁ ⟩
        → TC'⟨ (J₀ /…' l₀ ♦Proto' J₁ /…' l₁) ♦Proto' K ⟩)
  → TC'⟨ I /…' l ♦Proto' K ⟩
TC-∈⊗ {A = A}{B}{K = K} l cont = {!!} -- TC-∈Split cont' (mk l ?)
{-
  where
     cont' : TC-Split (A ⊗ B) K
     NES cont' x = x
     cont-⅋ cont' () l₁ l' x₁ x₂
     cont-⊗ cont' refl = cont -- l₁ l' x₁ x₂ = {!!}
     -}

TC-cut :
    ∀ {c₀ c₁ S₀ S₁ δ₀ δ₁}{I₀ : Proto δ₀}{I₁ : Proto δ₁}
      (D : Dual S₀ S₁)
      (l₀ : [ c₀ ↦ S₀ …]∈' I₀)(l₁ : [ c₁ ↦ S₁ …]∈' I₁)
      (P₀ : TC'⟨ I₀ ⟩) (P₁ : TC'⟨ I₁ ⟩)
    → TC'⟨ (I₀ /…' l₀) ♦Proto' (I₁ /…' l₁) ⟩
TC-cut end l₀ l₁ P₀ P₁ = {!!}
TC-cut (⊗⅋ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = {!!}
TC-cut (⅋⊗ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-∈⅋ l₀ P₀ λ d e d/=e ab →
  TC-conv ♦-com
  (TC-∈⊗ l₁ P₁ λ d' e' a b →
    TC-conv (≈-trans (♦-cong₂ ≈-refl (∈♦₁-compute… (move… d e d/=e)))
            (≈-trans ♦-assoc
            (♦-cong₂ ♦-com ≈-refl)))
     (TC-cut D₃ e' (∈♦₁… (move… d e d/=e)) b (TC-cut D₁ d' d a ab))
  )
{-
TC-cut end l₀ l₁ P₀ P₁ = {!TC-split σs A0 P₀ P₁!}
TC-cut (⊗⅋ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = ?
{-TC-conv ♦-com
  (TC-∈⅋ l₁ (λ d e d/=e a'b' → TC-conv (≈-trans ♦-com (♦-cong₂ (≈-trans {!move-compute {!e!} {!d!} {!(Diff-sym d/=e)!}!} {!Proto.forget!}) ≈-refl))
   (TC-∈⊗ l₀ (λ d' e' a b → TC-conv (≈-trans (♦-cong₂ ≈-refl
               (∈♦₁-compute (move {!e!} {!d!} {!(Diff-sym d/=e)!}))) ♦-assoc)
     (TC-cut  D d' (∈♦₁ (move {!e!} {!d!} {!(Diff-sym d/=e)!})) a (TC-cut D₂ e' e b a'b')))
   P₀))
  P₁)
  -}
TC-cut (⅋⊗ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv ≈-refl
  (TC-∈⅋ l₀ (λ {_}{_}{_}{J} d e d/=e ab → TC-conv ♦-com
  (TC-∈⊗ l₁ (λ {_}{_}{_}{_}{J₀}{J₁} d' e' a b → let X = TC-cut D₁ d' d a ab
       in TC-conv (≈-trans (♦-cong₂ ≈-refl (∈♦₁-compute (move d e d/=e)))
               (≈-trans ♦-assoc (♦-cong₂ ♦-com (move-compute… ([↦]∈'.l… d) ([↦]∈'.l… e) (Diff… d/=e)))))
          (TC-cut D₃ e' (∈♦₁ (move d e d/=e)) b X))
   P₁)) P₀)
-}

{-
TC-∈Split {I = I} cont (mk (mk (mk lΔ ↦Δ) (mk lA ↦A)) E/c) (TC-split σs A1 P P₁) with select {I = I} σs lΔ lA
TC-∈Split {δK = δK}{I = I}{K} cont (mk (mk (mk lΔ refl) (mk lA refl)) E/c) (TC-split σs A1 P P₁)
  | inj₁ x = TC-split (Selections♦ 0₂ σs δK) (atMost♦ 0₂ σs δK A1)
  (TC-conv (≈-sym (≈-trans (Selections♦/same {I = I /Ds lΔ} {K} 0₂ σs)
                  (♦-cong₂ (/[]-/Ds 0₂ I σs lΔ) ≈-refl)))
           (TC-∈Split cont (mk (mk (mk lΔ refl) (mk lA (! x))) {!!}) P))
  (TC-conv (≈-sym (≈-trans (Selections♦/not {I = I /Ds lΔ} {K} 1₂ σs) {!!}))
           P₁)
TC-∈Split cont (mk (mk (mk lΔ ↦Δ) (mk lA ↦A)) E/c) (TC-split σs A1 P P₁)
  | inj₂ y = {!!}

{-
-- selection style
record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    NES : ¬ (Session.Ended A)
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(σ : Selections δJ)
      → K ≈ J /₁ σ →
      (l : [ d ↦ S ]∈ J /₀ σ)(l' : [ e ↦ T ]∈ J /₀ σ)
      → DifferentVars l l' → TC⟨ J /₀ σ ⟩ → TC⟨ J /₁ σ ⟩
      → TC⟨ (J /Ds Proto.forget ([↦]∈.lI l) /Ds Proto.forget ([↦]∈.lI l')) ⟩
open TC-Split

TC-∈Split : ∀ {δI c A}{I : Proto δI}(σ : Selections δI) → TC-Split A (I /₁ σ) → (l : [ c ↦ A ]∈ I /₀ σ)
  → TC⟨ I /₀ σ ⟩ → TC⟨ I /Ds Proto.forget ([↦]∈.lI l) ⟩
TC-∈Split σ cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) = {!!}
TC-∈Split σ cont l (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈Split σ cont (mk l X) (TC-⅋-inp (mk .l X₁) P) | same =
  let X = cont-⅋ cont refl {c₀}{c₁} ((σ ,[ ε , _ ↦ 0₂ ]) ,[ ε , _ ↦ 0₂ ])
          (≈-sym (≈-trans (≈,[end] _) (≈-trans (≈,[end] _) {!!})))
          (there[] (mk (mk here here) {!!})) (mk (mk here here) {!!}) {!!} (TC-conv {!≈-refl!} (P c₀ c₁)) {!!}
   in TC-conv (≈-trans (≈,[end] _) (≈,[end] _)) X
   where postulate c₀ c₁ : _
TC-∈Split σ cont l (TC-⅋-inp l₁ P) | diff x = TC-⅋-inp {!l₁!} {!!}
TC-∈Split σ cont l (TC-end E) = {!!}
TC-∈Split σ cont l (TC-split σs A1 P P₁) = {!!}
-}

-- OLD ATTEMPT
{-


record TC-Split (A : Session) {δK}(K : Proto δK) : Set₁ where
  field
    NES : ¬ (Session.Ended A)
    cont-⅋ : ∀ {S T} → A ≡ S ⅋ T → ∀ {d e δJ}{J : Proto δJ}(l : [ d ↦ S ]∈ J)(l' : [ e ↦ T ]∈ J)
      → DifferentVars l l' → TC⟨ J ⟩ → TC⟨ (J / [↦]∈.lI l /Ds Proto.forget ([↦]∈.lI l')) ♦Proto' K ⟩
    cont-⊗ : ∀ {S T} → A ≡ S ⊗ T → ∀ {d e δ₀ δ₁}{J₀ : Proto δ₀}{J₁ : Proto δ₁}(l : [ d ↦ S ]∈ J₀)(l' : [ e ↦ T ]∈ J₁)
      → TC⟨ J₀ ⟩ → TC⟨ J₁ ⟩ → TC⟨ (J₀ / [↦]∈.lI l ♦Proto' J₁ / ([↦]∈.lI l')) ♦Proto' K ⟩
open TC-Split

{-
-- need to add that the erasure of the result is the same
postulate
  ∈-selections : ∀ {c A δI}{I : Proto δI}(σ : Selections δI)(l : [ c ↦ A ]∈ I)
    → (c ↦ A ∈ (([↦]∈.E l) Env./₀ σ))
    ⊎ ([ c ↦ A ]∈ I /₁ σ)
-}

data ∈-select {c A}{δI}{I : Proto δI}:(σ : Selections δI) → [ c ↦ A ]∈ I → Set where

postulate
  End/₀ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₀ σ)
  End/₁ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₁ σ)
  Sel♦ : ∀ {δs}{I : Proto δs}(σ : Selections δs) → I /₀ σ ♦Proto' I /₁ σ ≈ I

--need continuation for ⊗
TC-∈Split : ∀ {δI δK c A}{I : Proto δI}{K : Proto δK} → TC-Split A K → (l : [ c ↦ A ]∈ I)
  → TC⟨ I ⟩ → TC⟨ I [/] l ♦Proto' K ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split cont (mk l X) (TC-⊗-out .l σs σE A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (≈-trans (♦-cong₂ (≈,[end] ⟨ mapAll _ _ , _ ⟩) (≈,[end] ⟨ mapAll _ _ , _ ⟩))
  (Sel♦ σs))
  ≈-refl)
  (cont-⊗ cont refl (mk (mk here here) E₀) (mk (mk here here) ⟨ End/₁ σE X , _ ⟩) (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
        E₀ = ⟨ End/₀ σE X , _ ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) | diff x = {!!}
TC-∈Split cont l (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈Split cont (mk l X) (TC-⅋-inp (mk .l Y) P) | same = TC-conv
  (♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl)
  (cont-⅋ cont refl (there[] (mk (mk here here) _)) (mk (mk here here) _) {!!} (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⅋-inp l₁ P) | diff x = TC-⅋-inp (∈♦₀ (move l l₁ (mk x))) λ c₀ c₁ →
  TC-conv (≈-trans ♦-com,
          (≈,[] (≈-trans ♦-com, (≈,[]
           (≈-sym (≈-trans (∈♦₀-compute (move l l₁ (mk x)))
           (♦-cong₂ (≈-trans (move-compute… _ _ _)
           (≈-trans (/Ds-com (Proto.forget ([↦]∈.lI l)) (Proto.forget ([↦]∈.lI l₁)))
           (≈-sym (move-compute… _ _ _))))
           ≈-refl)))
           ∼-refl))
           ∼-refl))
  (TC-∈Split cont (there[] (there[] (move l₁ l (Diff-sym (mk x))))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim (NES cont (Map.All∈ (Proto.All∈ E ([↦]∈.lI l)) ([↦]∈.lE l)))
TC-∈Split cont l (TC-split σs A1 P P₁) = {!!}

{-with ∈-selections σs l
TC-∈Split {δK = δK} cont l (TC-split σs A1 P P₁) | inj₁ x = TC-split (allLeft δK σs) {!!} (TC-conv {!!} (TC-∈Split cont x P)) (TC-conv {!!} P₁)
TC-∈Split cont l (TC-split σs A1 P P₁) | inj₂ y = {!!}

-}
-}
{-
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? ([↦]∈.l… l) l₁
TC-∈Split cont (mk l X) (TC-⊗-out .l σs σE A0 P₀ P₁) | same = TC-conv
  (♦-cong₂ (≈-trans (♦-cong₂ (≈,[end] ⟨ mapAll _ _ , _ ⟩) (≈,[end] ⟨ mapAll _ _ , _ ⟩))
  (Sel♦ σs))
  ≈-refl)
  (cont-⊗ cont refl (mk (mk here here) E₀) (mk (mk here here) ⟨ End/₁ σE X , _ ⟩) (P₀ c₀) (P₁ c₁))
  where postulate c₀ c₁ : _
        E₀ = ⟨ End/₀ σE X , _ ⟩
TC-∈Split cont l (TC-⊗-out l₁ σs σE A0 P₀ P₁) | diff x = {!!}
TC-∈Split cont l (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈Split cont (mk l X) (TC-⅋-inp (mk .l Y) P) | same = TC-conv
  (♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl)
  (cont-⅋ cont refl (there[] (mk (mk here here) _)) (mk (mk here here) _) {!!} (P c₀ c₁))
  -- postulate for channels.. grr
  where postulate c₀ c₁ : _
TC-∈Split cont l (TC-⅋-inp l₁ P) | diff x = TC-⅋-inp (∈♦₀ (move l l₁ (mk x))) λ c₀ c₁ →
  TC-conv (≈-trans ♦-com,
          (≈,[] (≈-trans ♦-com, (≈,[]
           (≈-sym (≈-trans (∈♦₀-compute (move l l₁ (mk x)))
           (♦-cong₂ (≈-trans (move-compute… _ _ _)
           (≈-trans (/Ds-com (Proto.forget ([↦]∈.lI l)) (Proto.forget ([↦]∈.lI l₁)))
           (≈-sym (move-compute… _ _ _))))
           ≈-refl)))
           ∼-refl))
           ∼-refl))
  (TC-∈Split cont (there[] (there[] (move l₁ l (Diff-sym (mk x))))) (P c₀ c₁))
TC-∈Split cont l (TC-end E) = 𝟘-elim (NES cont (Map.All∈ (Proto.All∈ E ([↦]∈.lI l)) ([↦]∈.lE l)))
TC-∈Split cont l (TC-split σs A1 P P₁) = {!!}
-}




{-

TC-∈⅋ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⅋ B ]∈ I)
  → (∀ {d e δJ}{J : Proto δJ} (l : [ d ↦ A ]∈ J)(l' : [ e ↦  B ]∈ J) → DifferentVars l l' → TC⟨ J ⟩
     → TC⟨ ((J / [↦]∈.lI l) /Ds Proto.forget ([↦]∈.lI l')) ♦Proto' K ⟩)
  → TC⟨ I ⟩ →  TC⟨ I [/] l ♦Proto' K ⟩
TC-∈⅋ l cont (TC-⊗-out l₁ σs σE A0 P₀ P₁) with sameVar? ([↦]∈.l… l) l₁
... | X = {!!}
TC-∈⅋ l cont (TC-⅋-inp l₁ P) with sameVar? ([↦]∈.l… l) ([↦]∈.l… l₁)
TC-∈⅋ (mk l y) cont (TC-⅋-inp (mk .l x) P) | same = TC-conv (♦-cong₂ (≈-trans (≈,[end] _) (≈,[end] _)) ≈-refl) (cont (mk (mk (there here) here) _) (mk (mk here here) _) {!!} (TC-conv ≈-refl (P c₀ c₁)))
  where
    postulate
      c₀ c₁ : _
TC-∈⅋ l cont (TC-⅋-inp l₁ P) | diff l/=l₁ = TC-⅋-inp (∈♦₀ (move  l l₁ (mk l/=l₁))) (λ c₀ c₁ →
   TC-conv (≈-trans ♦-com, (≈,[] (≈-trans ♦-com, (≈,[] (≈-sym (≈-trans (∈♦₀-compute (move l l₁ (mk l/=l₁)))
           (♦-cong₂ (≈-trans (move-compute… ([↦]∈.l… l) ([↦]∈.l… l₁) l/=l₁)
           (≈-trans {!!}
            (≈-sym (move-compute… _ _ _)))) ≈-refl))) ∼-refl)) ∼-refl))
  (TC-∈⅋ (there[] (there[] (move l₁ l (Diff-sym (mk l/=l₁))))) cont (P c₀ c₁)))
TC-∈⅋ l cont (TC-end E) = {!!}
TC-∈⅋ l cont (TC-split σs A1 P P₁) = {!!}

{-
TC-∈⊗ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⊗ B ]∈ I)
  → (∀ {d e δJ₀ δJ₁}{J₀ : Proto δJ₀}{J₁ : Proto δJ₁}
       (l₀ : [ d ↦ A ]∈ J₀)(l₁ : [ e ↦ B ]∈ J₁) → TC⟨ J₀ ⟩ → TC⟨ J₁ ⟩
        → TC⟨ (J₀ [/] l₀ ♦Proto' J₁ [/] l₁) ♦Proto' K ⟩)
  → TC⟨ I ⟩ → TC⟨ I [/] l ♦Proto' K ⟩
TC-∈⊗ = {!!}


{-
TC-cut :
    ∀ {c₀ c₁ S₀ S₁ δ₀ δ₁}{I₀ : Proto δ₀}{I₁ : Proto δ₁}
      (D : Dual S₀ S₁)
      (l₀ : [ c₀ ↦ S₀ ]∈ I₀)(l₁ : [ c₁ ↦ S₁ ]∈ I₁)
      (P₀ : TC⟨ I₀ ⟩) (P₁ : TC⟨ I₁ ⟩)
    → TC⟨ (I₀ [/] l₀) ♦Proto' (I₁ [/] l₁) ⟩
TC-cut end σs A0 P₀ P₁ = {!TC-split σs A0 P₀ P₁!}
TC-cut (⊗⅋ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv ♦-com
  (TC-∈⅋ l₁ (λ d e d/=e a'b' → TC-conv (≈-trans ♦-com (♦-cong₂ (≈-trans (move-compute {!e!} {!d!} {!(Diff-sym d/=e)!}) {!Proto.forget!}) ≈-refl))
   (TC-∈⊗ l₀ (λ d' e' a b → TC-conv (≈-trans (♦-cong₂ ≈-refl
               (∈♦₁-compute (move {!e!} {!d!} {!(Diff-sym d/=e)!}))) ♦-assoc)
     (TC-cut  D d' (∈♦₁ (move {!e!} {!d!} {!(Diff-sym d/=e)!})) a (TC-cut D₂ e' e b a'b')))
   P₀))
  P₁)
TC-cut (⅋⊗ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv ≈-refl
  (TC-∈⅋ l₀ (λ {_}{_}{_}{J} d e d/=e ab → TC-conv ♦-com
  (TC-∈⊗ l₁ (λ {_}{_}{_}{_}{J₀}{J₁} d' e' a b → let X = TC-cut D₁ d' d a ab
       in TC-conv (≈-trans (♦-cong₂ ≈-refl (∈♦₁-compute (move d e d/=e)))
               (≈-trans ♦-assoc (♦-cong₂ ♦-com (move-compute d e (mk d/=e)))))
          (TC-cut D₃ e' (∈♦₁ (move d e d/=e)) b X))
   P₁)) P₀)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
