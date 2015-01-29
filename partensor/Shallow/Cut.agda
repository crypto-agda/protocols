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
open Env     hiding (_/₀_; _/₁_; _/_; Ended)
open Proto   hiding ()
open import partensor.Shallow.Equiv
open import partensor.Shallow.Term

module partensor.Shallow.Cut where
infixl 4 _♦Proto'_
-- things we have but I want better unification
{-
  _≈'_ : ∀ {δI δJ} → Proto δI → Proto δJ → Set₁
  ≈'-refl : ∀ {δI}{I : Proto δI} → I ≈' I
  ≈'-sym : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈' J → J ≈' I
  ≈'-trans : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ≈' B → B ≈' C → A ≈' C
-}
postulate
  _♦Proto'_ : ∀ {δa δb}(A : Proto δa)(B : Proto δb) → Proto (δa ♦Doms δb)

{-
data DifferentVarsDoms : ∀ {δI c d} → Doms'.[ c ]∈ δI → Doms'.[ d ]∈ δI → Set where
  h/t : ∀ {a b Db l}
   → DifferentVarsDoms {Db ,[ a ]}{a}{b} Doms'.here (Doms'.there l)
  t/h : ∀ {a b Db l}
   → DifferentVarsDoms {Db ,[ a ]}{b}{a} (Doms'.there l) Doms'.here
  t/t : ∀ {a c d D l l'} → DifferentVarsDoms {D ,[ a ]}{c}{d} (Doms'.there l) (Doms'.there l')

-- Need to update this, they may point to the same tensor block but different inside it...
-- boring I know!
DifferentVars : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A ]∈ I → [ d ↦ B ]∈ I → Set
DifferentVars l l' = DifferentVarsDoms (Proto.forget ([↦]∈.lI l)) (Proto.forget ([↦]∈.lI l'))
-}
postulate
  DifferentVars… : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A …]∈ I → [ d ↦ B …]∈ I → Set
  Diff-sym… : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A …]∈ I}{l' : [ d ↦ B …]∈ I}
    → DifferentVars… l l' → DifferentVars… l' l

record DifferentVars {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I) : Set where
  constructor mk
  field
    Diff… : DifferentVars… ([↦]∈.l… l) ([↦]∈.l… l')
open DifferentVars

Diff-sym : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A ]∈ I}{l' : [ d ↦ B ]∈ I}
    → DifferentVars l l' → DifferentVars l' l
Diff… (Diff-sym df) = Diff-sym… (Diff… df)

data SameVar? {δI}{I : Proto δI} : ∀ {c c' A A'} → [ c ↦ A …]∈ I → [ c' ↦ A' …]∈ I → Set₁ where
  same : ∀ {c A}{l : [ c ↦ A …]∈ I} → SameVar? l l
  diff : ∀ {c c' A B}{l : [ c ↦ A …]∈ I}{l' : [ c' ↦ B …]∈ I} → DifferentVars… l l' → SameVar? l l'

postulate
  sameVar? : ∀ {δI}{I : Proto δI}{c c' A A'}(l : [ c ↦ A …]∈ I)(l' : [ c' ↦ A' …]∈ I) → SameVar? l l'

postulate
  TC-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
    → I ≈ J → TC⟨ I ⟩ → TC⟨ J ⟩


  move… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I) → DifferentVars… l l'
          → [ d ↦ B …]∈ (I [/…] l)

  ∈♦₀ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈ I₀ → [ c ↦ A ]∈ (I₀ ♦Proto' I₁)
  ∈♦₁ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈ I₁ → [ c ↦ A ]∈ (I₀ ♦Proto' I₁)
  ♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto' (B ♦Proto' C) ≈ (A ♦Proto' B) ♦Proto' C
  ♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto' B) ≈ (B ♦Proto' A)
  ∈♦₀-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈ I₀) →
          (I₀ ♦Proto' I₁) [/] (∈♦₀ l) ≈ (I₀ [/] l) ♦Proto' I₁
  ∈♦₁-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈ I₁) →
          (I₀ ♦Proto' I₁) [/] (∈♦₁ l) ≈ I₀ ♦Proto' (I₁ [/] l)
  ♦-cong₂ : ∀ {δa δb δc δd}{A : Proto δa}{B : Proto δb}{C : Proto δc}{D : Proto δd}
          → A ≈ B → C ≈ D → A ♦Proto' C ≈ B ♦Proto' D
  move-compute : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I)(l/=l' : DifferentVars… l l')
    → (I [/…] l) [/…] move… l l' l/=l' ≈ (I [/…] l) /Ds Proto.forget ([↦…]∈.lI l')

move : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I) → DifferentVars l l'
          → [ d ↦ B ]∈ (I [/] l)
move (mk l X) (mk l' Y) df = mk (move… l l' (Diff… df)) {!!}


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
   TC-conv {!there[]!} (TC-∈⅋ (there[] (there[] (move l₁ l (Diff-sym (mk l/=l₁))))) cont (P c₀ c₁)))
TC-∈⅋ l cont (TC-end E) = {!!}
TC-∈⅋ l cont (TC-split σs A1 P P₁) = {!!}

TC-∈⊗ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⊗ B ]∈ I)
  → (∀ {d e δJ₀ δJ₁}{J₀ : Proto δJ₀}{J₁ : Proto δJ₁}
       (l₀ : [ d ↦ A ]∈ J₀)(l₁ : [ e ↦ B ]∈ J₁) → TC⟨ J₀ ⟩ → TC⟨ J₁ ⟩
        → TC⟨ (J₀ [/] l₀ ♦Proto' J₁ [/] l₁) ♦Proto' K ⟩)
  → TC⟨ I ⟩ → TC⟨ I [/] l ♦Proto' K ⟩
TC-∈⊗ = {!!}


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
