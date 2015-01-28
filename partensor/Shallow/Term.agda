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
open Proto   hiding () renaming (Selection to Selections)
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
          FG : E ∼ G
          FG = {!!}
          K = J / here ,[ G ]
          rPP : T⟨ K ⟩
          rPP = T-⊗-reorg here (there here) here (go (P c0 c1))
          e : K ≈ I
          e = ≈-trans (≈,[] {!!} {!∼,↦!}) (≈-sym (thmA (mk lI lE)))
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
