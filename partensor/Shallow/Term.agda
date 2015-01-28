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

module partensor.Shallow.Term where

data ⟨_⟩ {δI}(I : Proto δI) : Set₁ where
  end :
    Ended I
    → ⟨ I ⟩

  ⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I )
      (P : ∀ c₀ c₁ → ⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → ⟨ I ⟩

  ⊗-out :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ …]∈ I)
      (P : ∀ c₀ c₁ → ⟨ I [/…] l ,[ E/ l , c₀ ↦ S₀ , c₁ ↦ S₁ ] ⟩)
    → ⟨ I ⟩

  split :
      (σs : Selections δI)
      (A1 : AtMost 1 σs)
      (P₀ : ⟨ I /₀ σs ⟩)
      (P₁ : ⟨ I /₁ σs ⟩)
    → ⟨ I ⟩

  nu :
    ∀ {S₀ S₁}
      (D : Dual S₀ S₁)
      (P : ∀ c₀ c₁ → ⟨ I ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → ⟨ I ⟩

module Translation
 {t}
 (T⟨_⟩ : ∀ {δI} → Proto δI → Set t)
 (T-⊗-out :
    ∀ {δI I c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ …]∈ I)
      (σs : Selections δI)
      (σE : Selection ([↦…]∈.δE l))
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → T⟨ I [/…] l /₀ σs ,[ E/ l Env./₀ σE , c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I [/…] l /₁ σs ,[ E/ l Env./₁ σE , c₁ ↦ S₁ ] ⟩)
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
      (l₀ : c₀ ↦ S₀ ∈ E)
      (l₁ : c₁ ↦ S₁ ∈ E)
      (P : T⟨ J ⟩)
    → T⟨ J / l ,[ (E Env./ l₀ /D (Env.forget l₁) , c ↦ S₀ ⊗ S₁) ] ⟩)

 -- (_≈T_ : ∀ {I J} → T⟨ I ⟩ → T⟨ J ⟩ → Set)
 (T-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ} → I ≈ J → T⟨ I ⟩ → T⟨ J ⟩)


{-
      Σ (Selections
        T⟨ I /₀ σs ⟩
      × T⟨ I /₁ σs ⟩
-}

-- (T-gc : T⟨ I ⟩ → 

  where

  go : ∀ {δI}{I : Proto δI} → ⟨ I ⟩ → T⟨ I ⟩
  go (end x) = T-end x
  go (⅋-inp l P) = T-⅋-inp l (λ c₀ c₁ → go (P c₀ c₁))
  go {δI}{I}(⊗-out {c} {S₀} {S₁} (mk {δE} {E} lI lE) P) = T-conv e rPP
    where postulate c0 c1 : URI
          F = E Env./ lE , c0 ↦ S₀ , c1 ↦ S₁
          J = I / lI ,[ F ]
          G = F /D there here /D here , c ↦ S₀ ⊗ S₁
          K = J / here ,[ G ]
          rPP : T⟨ K ⟩
          rPP = T-⊗-reorg here (there here) here (go (P c0 c1))
          e : K ≈ I
          e = ≈-trans (≈,[] (≈,[end] (Ended-/* F)) (∼,↦ (∼-trans ∼,↦end ∼,↦end))) (≈-sym (thmA (mk lI lE)))
  {-
          PP  : ⟨ J ⟩
          PP  = P c0 c1
          gPP : T⟨ J ⟩
          gPP = go PP
          SP = ⊗-split {!!} here PP λ {J} σ P₀ P₁ →
                 {!⊗-split ? here P₀ λ {J'} σ' P₀' P₁' →
                     ?!}
   -}
  go (split Z A P₀ P₁) = {!!}
  go (nu D P) = {!!}

{-
  module _ {δF}(F : Env δF) where
    ⊗-split : ∀ {δ δs}{I : Proto δs}{E : Env δ}
                 (l : Doms'.[ δ ]∈ δs)
                 -- (l : [ E ]∈ I)
                 -- {c S}(l' : c ↦ S ∈ E)
                 (P : ⟨ I ⟩)
                 (κ : ∀ {c S}
                        -- E 
                        (l' : c ↦ S ∈ E)
                        {J : Proto δs}
                        (σs : Selections δs)
                        (A0 : AtMost 0 σs)
                        (P₀ : ⟨ J /₀ σs ,[ (E Env./ l' , c ↦ end) ] ,[ F ] ⟩)
                        (P₁ : ⟨ J /₁ σs ,[ (E Env./*   , c ↦   S) ] ,[ F ] ⟩)
                      → T⟨ J {-/ l-} ,[ F ] ⟩)
              → T⟨ I / l ,[ F ] ⟩
    ⊗-split l (end x) κ = {!!} -- elim
    ⊗-split l (⅋-inp l₁ P) κ = T-⅋-inp {!l₁!} {!!}
    ⊗-split l (⊗-out l₁ l₁' P) κ = {!!}
    ⊗-split l (split Z A1 P P₁) κ = {!!}
    ⊗-split l (nu D P) κ = {!!}
-}

data T⟨_⟩ {δI}(I : Proto δI) : Set₁ where
 T-⊗-out :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ …]∈ I)
      (σs : Selections δI)
      (σE : Selection ([↦…]∈.δE l))
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → T⟨ I [/…] l /₀ σs ,[ E/ l Env./₀ σE , c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I [/…] l /₁ σs ,[ E/ l Env./₁ σE , c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

 T-⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → T⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

 T-end : ∀ (E : Ended I) → T⟨ I ⟩

 T-cut :
    ∀ {S₀ S₁}
      (D : Dual S₀ S₁)
      (σs : Selections δI)
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → T⟨ I /₀ σs ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I /₁ σs ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

 T-split :
      (σs : Selections δI)
      (A1 : AtMost 1 σs)
      (P₀ : T⟨ I /₀ σs ⟩)
      (P₁ : T⟨ I /₁ σs ⟩)
    → T⟨ I ⟩

data TC⟨_⟩ {δI}(I : Proto δI) : Set₁ where
 TC-⊗-out :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ …]∈ I)
      (σs : Selections δI)
      (σE : Selection ([↦…]∈.δE l))
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → TC⟨ I [/…] l /₀ σs ,[ E/ l Env./₀ σE , c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → TC⟨ I [/…] l /₁ σs ,[ E/ l Env./₁ σE , c₁ ↦ S₁ ] ⟩)
    → TC⟨ I ⟩

 TC-⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → TC⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → TC⟨ I ⟩

 TC-end : ∀ (E : Ended I) → TC⟨ I ⟩

 TC-split :
      (σs : Selections δI)
      (A1 : AtMost 1 σs)
      (P₀ : TC⟨ I /₀ σs ⟩)
      (P₁ : TC⟨ I /₁ σs ⟩)
    → TC⟨ I ⟩

infix 0 _≈'_
infixl 4 _♦Proto'_
-- things we have but I want better unification
postulate
  _≈'_ : ∀ {δI δJ} → Proto δI → Proto δJ → Set₁
  ≈'-refl : ∀ {δI}{I : Proto δI} → I ≈' I
  ≈'-trans : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ≈' B → B ≈' C → A ≈' C
  _♦Proto'_ : ∀ {δa δb}(A : Proto δa)(B : Proto δb) → Proto (δa ♦Doms δb)

postulate
  TC-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
    → I ≈' J → TC⟨ I ⟩ → TC⟨ J ⟩

  DifferentVars : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A ]∈ I → [ d ↦ B ]∈ I → Set

  move : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I) → DifferentVars l l'
          → [ d ↦ B ]∈ (I [/] l)

  -- ∈♦₀ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈ I₀ → [ c ↦ A ]∈ (I₀ ♦Proto I₁)
  ∈♦₁ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈ I₁ → [ c ↦ A ]∈ (I₀ ♦Proto' I₁)
  ♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto' (B ♦Proto' C) ≈' (A ♦Proto' B) ♦Proto' C
  ♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto' B) ≈' (B ♦Proto' A)
  ∈♦₁-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈ I₁) →
          (I₀ ♦Proto' I₁) [/] (∈♦₁ l) ≈' I₀ ♦Proto' (I₁ [/] l)
  ♦-cong₂ : ∀ {δa δb δc δd}{A : Proto δa}{B : Proto δb}{C : Proto δc}{D : Proto δd}
          → A ≈' B → C ≈' D → A ♦Proto' C ≈' B ♦Proto' D
  move-compute : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I)(l/=l' : DifferentVars l l')
    → (I [/] l) [/] move l l' l/=l' ≈' (I [/] l) /Ds Proto.forget ([↦]∈.lI l')


TC-∈⅋ : ∀ {δI δK c A B}{I : Proto δI}{K : Proto δK}(l : [ c ↦ A ⅋ B ]∈ I)
  → (∀ {d e δJ}{J : Proto δJ} (l : [ d ↦ A ]∈ J)(l' : [ e ↦  B ]∈ J) → DifferentVars l l' → TC⟨ J ⟩
     → TC⟨ ((J / [↦]∈.lI l) /Ds Proto.forget ([↦]∈.lI l')) ♦Proto' K ⟩)
  → TC⟨ I ⟩ →  TC⟨ I [/] l ♦Proto' K ⟩
TC-∈⅋ l cont P = {!!}

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
TC-cut (⊗⅋ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv {!!} (TC-∈⅋ l₁ {!!} P₁)
TC-cut (⅋⊗ D D₁ D₂ D₃) l₀ l₁ P₀ P₁ = TC-conv ≈'-refl
  (TC-∈⅋ l₀ (λ {_}{_}{_}{J} d e d/=e ab → TC-conv ♦-com
  (TC-∈⊗ l₁ (λ {_}{_}{_}{_}{J₀}{J₁} d' e' a b → let X = TC-cut D₁ d' d a ab
       in TC-conv (≈'-trans (♦-cong₂ ≈'-refl (∈♦₁-compute (move d e d/=e)))
               (≈'-trans ♦-assoc (♦-cong₂ ♦-com (move-compute d e d/=e))))
          (TC-cut D₃ e' (∈♦₁ (move d e d/=e)) b X))
   P₁)) P₀)

cut : ∀ {δI}{I : Proto δI} → T⟨ I ⟩ → TC⟨ I ⟩
cut (T-⊗-out l σs σE A0 P₀ P₁) = TC-⊗-out l σs σE A0 (λ c₀ → cut (P₀ c₀)) (λ c₁ → cut (P₁ c₁))
cut (T-⅋-inp l P) = TC-⅋-inp l (λ c₀ c₁ → cut (P c₀ c₁))
cut (T-end E) = TC-end E
cut (T-cut D σs A0 P₀ P₁) = {! TC-cut D σs A0 {!λ c₀ → ? !} {!!} !}
cut (T-split σs A1 P P₁) = {!!}

{-
-- no split version,
data TNS⟨_⟩ {δI}(I : Proto δI) : Set₁ where
 T-⊗-out :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ …]∈ I)
      (σs : Selections δI)
      (σE : Selection ([↦…]∈.δE l))
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → TNS⟨ I [/…] l /₀ σs ,[ E/ l Env./₀ σE , c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → TNS⟨ I [/…] l /₁ σs ,[ E/ l Env./₁ σE , c₁ ↦ S₁ ] ⟩)
   → TNS⟨ I ⟩

 T-⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → TNS⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → TNS⟨ I ⟩

 T-end : ∀ (E : Ended I) → TNS⟨ I ⟩

 T-cut :
    ∀ {S₀ S₁}
      (D : Dual S₀ S₁)
      (σs : Selections δI)
      (A0 : AtMost 0 σs)
      (P₀ : ∀ c₀ → TNS⟨ I /₀ σs ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → TNS⟨ I /₁ σs ,[ c₁ ↦ S₁ ] ⟩)
    → TNS⟨ I ⟩
-}


{-
data T⟨_⟩ {δs}(I : Proto δs) : Set₁ where
  ⊗ :
    ∀ {c S₀ S₁}
      (l  : [ c ↦ S₀ ⊗ S₁ ]∈ I)
      (σs : Selections δs)
      (P₀ : ∀ c₀ → T⟨ I / l /₀ σ ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I / l /₁ σ ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

  ⅋ :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → T⟨ I / l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

  end :
    Ended I
    → T⟨ I ⟩

  cut :
    ∀ {S₀ S₁}
      (σs : Selections δs)
      (P₀ : ∀ c₀ → T⟨ I /₀ σ ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I /₁ σ ,[ c₁ ↦ S₁ ] ⟩)
      (D : Dual S₀ S₁)
    → T⟨ I ⟩

{-
data T⟨_⟩ {δ} (E : Env δ) : Set₁ where
  ⊗ :
    ∀ {c S₀ S₁}
      (l  : c ↦ (S₀ ⊗ S₁) ∈ E)
      (σ  : Selection δ)
      (P₀ : ∀ c₀ → T⟨ (E Env./ l) /₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → T⟨ (E Env./ l) /₁ σ , c₁ ↦ S₁ ⟩)
    → T⟨ E ⟩

  ⅋ :
    ∀ {c S₀ S₁}
      (l : c ↦ (S₀ ⅋ S₁) ∈ E)
      (P : ∀ c₀ c₁ → T⟨ (E / l) , c₀ ↦ S₀ , c₁ ↦ S₁ ⟩)
    → T⟨ E ⟩

  end :
    Env.Ended E
    → T⟨ E ⟩

  cut :
    ∀ {S₀ S₁}
      (σ  : Selection δ)
      (P₀ : ∀ c₀ → T⟨ E /₀ σ , c₀ ↦ S₀ ⟩)
      (P₁ : ∀ c₁ → T⟨ E /₁ σ , c₁ ↦ S₁ ⟩)
      (D : Dual S₀ S₁)
    → T⟨ E ⟩

{-
data Env : Dom → Set₁ where
  ε     : Env ε
  _,_↦_ : ∀ {δ} (E : Env δ) c (S : Session) → Env (δ , c)
-}

{-

{-

{-
Dom = ℕ
Env : Dom → Set₁
Env n = Vec Session n

Layout : Dom → Set
Layout n = Vec 𝟚 n

projLayout : ∀ {n} (f : Session → 𝟚 → Session) (Δ : Env n) → Layout n → Env n
projLayout f = zipWith f

_/₀_ : ∀ {n} (Δ : Env n) → Layout n → Env n
_/₀_ = projLayout (λ S → [0: S 1: end ])

_/₁_ : ∀ {n} (Δ : Env n) → Layout n → Env n
_/₁_ = projLayout (λ S → [0: end 1: S ])

data ⟨_⟩ {n} (Δ : Env n) : Set₁ where
  ⊗ :
    ∀ {c S₀ S₁}
      (l  : Δ [ c ]= S₀ ⊗ S₁)
      (L  : Layout n)
      (P₀ : ⟨ Δ /₀ L [ c ]≔ S₀ ⟩)
      (P₁ : ⟨ Δ /₁ L [ c ]≔ S₁ ⟩)
    → ⟨ Δ ⟩
  ⅋ :
    ∀ {c S₀ S₁}
      (l : Δ [ c ]= S₀ ⅋ S₁)
      (P : Δ [ c ]=* (S₀ ∷ S₁ ∷ []))
    → ⟨ Δ ⟩
    -}

{-
data Layout : Env → Set where
  ε : Layout ε
  _,_↦_ : ∀ {σ} (L : Layout σ) c {S} (b : 𝟚) → Layout (σ , c ↦ S)

projLayout : (f : 𝟚 → Session → Session) (Δ : Env) → Layout Δ → Env
projLayout f ε ε = ε
projLayout f (Δ , .c ↦ S) (L , c ↦ b) = projLayout f Δ L , c ↦ f b S

_/₀_ : (Δ : Env) → Layout Δ → Env
_/₀_ = projLayout (λ b S → [0: S 1: end ] b)

_/₁_ : (Δ : Env) → Layout Δ → Env
_/₁_ = projLayout (λ b S → [0: end 1: S ] b)

data ⟨_⟩ (Δ : Env) : Set₁ where
{-
  ⅋-in :
    ∀ {c S T}
      (l : [ c ↦ (⅋ S T) ]∈ Δ )
      (P : ∀ d e → ⟨ Δ [ l ≔* · ,[ d ↦ S ] ,[ e ↦ T ] ] ⟩)
    → ⟨ Δ ⟩
-}
  ⊗-out :
    ∀ {c S T}
      (l : c ↦ ⊗ S T ∈ Δ)
      (L : Layout 
      (P : ∀ d → ⟨ Δ [ l ≔ S ] /₀ L ⟩)
      (Q : ∀ e → ⟨ Δ [ l ≔ T ] /₁ L ⟩)
    → ⟨ Δ ⟩

{-
  split :
    ∀ {Δ₀ Δ₁}
    → ZipP 1 Δ Δ₀ Δ₁ → ⟨ Δ₀ ⟩ → ⟨ Δ₁ ⟩ → ⟨ Δ ⟩

  end :
    EndedProto Δ
    → ⟨ Δ ⟩

  nu : ∀ {Δ' S T}
       → (l : []∈ Δ')
       → (∀ c d → ⟨ Δ' [ l ≔* (· ,[ c ↦ S ] ,[ d ↦ T ]) ]' ⟩)
       → Dual S T
       → Δ ≡ Δ' [ l ≔* · ]'
       → ⟨ Δ ⟩

{-
data ⟨_⟩ (Δ : Proto) : Set₁ where
  ⅋-in :
    ∀ {c S T}
      (l : [ c ↦ (⅋ S T) ]∈ Δ )
      (P : ∀ d e → ⟨ Δ [ l ≔* · ,[ d ↦ S ] ,[ e ↦ T ] ] ⟩)
    → ⟨ Δ ⟩

  ⊗-out :
    ∀ {c S T η}
      (l : [ η ]∈ Δ)
      (l' : c ↦ ⊗ S T ∈ η)
      (P : ∀ d e → ⟨ Δ [ l ≔* · ,[ η [ l' += ε , d ↦ S , e ↦ T ]η ] ] ⟩)
    → ⟨ Δ ⟩

  split :
    ∀ {Δ₀ Δ₁}
    → ZipP 1 Δ Δ₀ Δ₁ → ⟨ Δ₀ ⟩ → ⟨ Δ₁ ⟩ → ⟨ Δ ⟩

  end :
    EndedProto Δ
    → ⟨ Δ ⟩

  nu : ∀ {Δ' S T}
       → (l : []∈ Δ')
       → (∀ c d → ⟨ Δ' [ l ≔* (· ,[ c ↦ S ] ,[ d ↦ T ]) ]' ⟩)
       → Dual S T
       → Δ ≡ Δ' [ l ≔* · ]'
       → ⟨ Δ ⟩


{-
-- cut₁ : ∀ {Δ Δ' S}(l : S ∈ Δ)(l' : dual S ∈ Δ') → ⟨ Δ ⟩ → ⟨ Δ' ⟩ → ⟨ Δ [ l ≔ end ] ⅋ Δ' [ l' ≔ end ] ⟩
cut₁ : ∀ {Δ Δ' S}(l : S ∈ Δ)(l' : dual S ∈ Δ')
      → ⟨ Δ ⟩ → ⟨ Δ' ⟩ → ⟨ Δ [ l ≔ end ] ⅋ Δ' [ l' ≔ end ] ⟩
cut₁
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
-- -}
-- -}
