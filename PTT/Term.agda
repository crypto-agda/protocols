{-# OPTIONS --copatterns #-}
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J)
open import PTT.Dom
import PTT.Session as Session
import PTT.Map as Map
import PTT.Env as Env
import PTT.Proto as Proto
open Session hiding (Ended)
open Env     hiding (Ended)
open Proto
-- open import PTT.Equiv

module PTT.Term where

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
      (P : ∀ c₀ c₁ → ⟨ I [/…] l ,[ E/ l , c₀ ↦ « S₀ » , c₁ ↦ « S₁ » ] ⟩)
    → ⟨ I ⟩

  split :
      (σs : Selections δI)
      (A1 : AtMost 1 I σs)
      (P₀ : ⟨ I []/₀ σs ⟩)
      (P₁ : ⟨ I []/₁ σs ⟩)
    → ⟨ I ⟩

  nu :
    ∀ {S₀ S₁}
      (D : Dual S₀ S₁)
      (P : ∀ c₀ c₁ → ⟨ I ,[ ε , c₀ ↦ « S₀ » , c₁ ↦ « S₁ » ] ⟩)
    → ⟨ I ⟩


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
      (A0 : AtMost 0 I σs)
      (P₀ : ∀ c₀ → T⟨ I [/…] l []/₀ σs ,[ E/ l /₀ σE , c₀ ↦ « S₀ » ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I [/…] l []/₁ σs ,[ E/ l /₁ σE , c₁ ↦ « S₁ » ] ⟩)
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
      (A0 : AtMost 0 I σs)
      (P₀ : ∀ c₀ → T⟨ I []/₀ σs ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → T⟨ I []/₁ σs ,[ c₁ ↦ S₁ ] ⟩)
    → T⟨ I ⟩

 T-split :
      (σs : Selections δI)
      (A1 : AtMost 1 I σs)
      (P₀ : T⟨ I []/₀ σs ⟩)
      (P₁ : T⟨ I []/₁ σs ⟩)
    → T⟨ I ⟩


data TC'⟨_⟩ {δI}(I : Proto δI) : Set₁ where
 TC-⊗-out :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⊗ S₁ ]∈ I)
      (σs : Selections δI)
      (A0 : AtMost 0 (I / l) σs)
      (P₀ : ∀ c₀ → TC'⟨ I / l []/₀ σs ,[ c₀ ↦ S₀ ] ⟩)
      (P₁ : ∀ c₁ → TC'⟨ I / l []/₁ σs ,[ c₁ ↦ S₁ ] ⟩)
    → TC'⟨ I ⟩

 TC-⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → TC'⟨ I / l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → TC'⟨ I ⟩

 TC-?-inp :
    ∀ {c A S₁}
      (l : [ c ↦ act (recv {A} S₁) ]∈ I)
      (P : (m : A) → TC'⟨ I / l ,[ c ↦ S₁ m ] ⟩)
    → TC'⟨ I ⟩

 TC-!-out :
    ∀ {c A S₁}
      (l : [ c ↦ act (send {A} S₁) ]∈ I)
      (m : A)(P : TC'⟨ I / l ,[ c ↦ S₁ m ] ⟩)
    → TC'⟨ I ⟩

 TC-end : ∀ (E : Ended I) → TC'⟨ I ⟩

 TC-split :
      (σs : Selections δI)
      (A1 : AtMost 1 I σs)
      (P₀ : TC'⟨ I []/₀ σs ⟩)
      (P₁ : TC'⟨ I []/₁ σs ⟩)
    → TC'⟨ I ⟩
{-
 TC-mix : ∀ {δF δG}{F : Env δF}{G : Env δG}(lF : [ F ]∈ I)(lG : [ G ]∈ I)
     (lF/=lG : DiffDoms ([]∈.lΔ lF) ([]∈.lΔ lG))
     (P : TC'⟨ ((I Proto./ lF) /Ds []∈.lΔ lG),[ F ♦Env G ] ⟩)
     → TC'⟨ I ⟩
-}

{-

data S⟨_⟩ {δI}(I : Proto δI) : Set₁ where
 S-split :
      (σs : Selections δI)
      (A1 : AtMost 1 σs)
      (P₀ : S⟨ I []/₀ σs ⟩)
      (P₁ : S⟨ I []/₁ σs ⟩)
    → S⟨ I ⟩
 TC-⅋-inp :
    ∀ {c S₀ S₁}
      (l : [ c ↦ S₀ ⅋ S₁ ]∈ I)
      (P : ∀ c₀ c₁ → S⟨ I [/] l ,[ c₀ ↦ S₀ ] ,[ c₁ ↦ S₁ ] ⟩)
    → S⟨ I ⟩

 TC-?-inp :
    ∀ {c A S₁}
      (l : [ c ↦ act (recv {A} S₁) ]∈ I)
      (P : (m : A) → S⟨ I [/] l ,[ c ↦ S₁ m ] ⟩)
    → S⟨ I ⟩
 S-T : TC'⟨ I ⟩ → S⟨ I ⟩


{-
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
←      (σs : Selections δI)
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
