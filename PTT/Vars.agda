{-# OPTIONS --copatterns #-}
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP hiding ([_]; J) renaming (proof-irrelevance to UIP)
open import PTT.Dom as Dom hiding (∈♦₀)
import PTT.Session as Session
import PTT.Map as Map
import PTT.Env as Env
import PTT.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/[_]_; Ended)
open Proto hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com)
-- open import PTT.Equiv
open import PTT.Term

module PTT.Vars where


infixl 4 _♦Proto'_ -- _♦Env'_
abstract
  _♦Proto'_ : ∀ {δa δb}(A : Proto δa)(B : Proto δb) → Proto (δa ♦Doms δb)
  _♦Proto'_ = _♦Proto_

  lookup-[]∈♦'₀ : ∀ {δ δE δF}(E : Proto δE)(F : Proto δF)(l : [ δ ]∈D δE)
    → Proto.lookup (E ♦Proto' F) ([]∈♦₀ {δF = δF} l) ≡ Proto.lookup E l
  lookup-[]∈♦'₀ = lookup-[]∈♦₀

  lookup-[]∈♦'₁ : ∀ {δ δE δF}(E : Proto δE)(F : Proto δF)(l : [ δ ]∈D δF)
    → Proto.lookup (E ♦Proto' F) ([]∈♦₁ {δF = δF} l) ≡ Proto.lookup F l
  lookup-[]∈♦'₁ = lookup-[]∈♦₁

  /Ds-[]∈♦'₀ : ∀ {δ δI δK}{I : Proto δI}(l : [ δ ]∈D δI)(K : Proto δK)
     → (I /Ds l) ♦Proto' K ≡ (I ♦Proto' K) /Ds ([]∈♦₀ {δF = δK} l)
  /Ds-[]∈♦'₀ l = /Ds-[]∈♦₀ l

  [∈]♦₀ : ∀ {δ₀ δ₁ δE}{E : Env δE}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ E ]∈ I₀ → [ E ]∈ (I₀ ♦Proto' I₁)
  [∈]♦₀ {δ₁ = δ₁}{I₁ = F} ⟨ lΔ , ↦Δ ⟩ = ⟨ []∈♦₀ {δF = δ₁} lΔ , lookup-[]∈♦'₀ _ F lΔ ∙ ↦Δ ⟩

  [∈]♦₁ : ∀ {δ₀ δ₁ δE}{E : Env δE}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ E ]∈ I₁ → [ E ]∈ (I₀ ♦Proto' I₁)
  [∈]♦₁ {δ₁ = δ₁}{I₁ = F} ⟨ lΔ , ↦Δ ⟩ = ⟨ []∈♦₁ {δF = δ₁} lΔ , lookup-[]∈♦'₁ _ F lΔ ∙ ↦Δ ⟩

  ≔[∈]♦₀ : ∀ {δE δ₀ δ₁}{E : Env δE}{I₀ : Proto δ₀}{I₁ : Proto δ₁}{f : Env δE → Env δE}(l : [ E ]∈ I₀)
      → (I₀ ♦Proto' I₁) [ []∈.lΔ ([∈]♦₀ {I₁ = I₁} l) ≔ f ] ≡ I₀ [ []∈.lΔ l ≔ f ] ♦Proto' I₁
  ≔[∈]♦₀ {I₁ = I₁} ⟨ lΔ , ↦Δ ⟩ = ≔[]∈♦₀ lΔ I₁

  ≔[∈]♦₁ : ∀ {δE δ₀ δ₁}{E : Env δE}{I₀ : Proto δ₀}{I₁ : Proto δ₁}{f : Env δE → Env δE}(l : [ E ]∈ I₁)
      → (I₀ ♦Proto' I₁) [ []∈.lΔ ([∈]♦₁ {I₀ = I₀} l) ≔ f ] ≡ I₀ ♦Proto' I₁ [ []∈.lΔ l ≔ f ]
  ≔[∈]♦₁ {I₁ = I₁} ⟨ lΔ , ↦Δ ⟩ =  ≔[]∈♦₁ lΔ I₁



{-
abstract
  _♦Env'_ : ∀{δa δb}(A : Env δa)(B : Env δb) → Env (δa ♦Dom δb)
  _♦Env'_ = _♦Env_


postulate
  ♦E-cong₂ : ∀ {δE δE' δF δF'}{E : Env δE}{E' : Env δE'}{F : Env δF}{F' : Env δF'}
    → E ∼ E' → F ∼ F' → E ♦Env F ∼ E' ♦Env F'
-}
{-
data DifferentVarsDoms : ∀ {δI c d} → [ c ]∈D δI → Doms'.[ d ]∈ δI → Set where
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

data DifferentVars… {δI}{I : Proto δI}{c d A B} : (lA : [ c ↦ A …]∈ I)(lB : [ d ↦ B …]∈ I) → Set₁ where
  diff-ten : ∀ {δF δG}{F : Env δF}{G : Env δG}{lA : [ δF ]∈D δI}{lB : [ δG ]∈D δI}
    {↦A : Proto.lookup I lA ≡ F}{c↦ : c ↦ « A » ∈ F} {↦B : Proto.lookup I lB ≡ G}{d↦ : d ↦ « B » ∈ G}
    → DiffDoms lA lB → DifferentVars… (mk ⟨ lA , ↦A ⟩ c↦) (mk ⟨ lB , ↦B ⟩ d↦)
  diff-in-ten : ∀ {δF}{F : Env δF}{lF : [ δF ]∈D δI}{↦F : Proto.lookup I lF ≡ F}
     {c∈ : c ∈D δF}{↦c : Map.lookup F c∈ ≡ « A »}{d∈ : d ∈D δF}{↦d : Map.lookup F d∈ ≡ « B »}
    → DiffDom c∈ d∈
    → DifferentVars… (mk4 lF ↦F c∈ ↦c) (mk4 lF ↦F d∈ ↦d)

postulate
  -- DifferentVars… : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A …]∈' I → [ d ↦ B …]∈' I → Set
  Diff-sym… : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A …]∈ I}{l' : [ d ↦ B …]∈ I}
    → DifferentVars… l l' → DifferentVars… l' l

record DifferentVars {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I) : Set₁ where
  constructor mk
  field
    Diff… : DifferentVars… ([↦]∈.l… l) ([↦]∈.l… l')
open DifferentVars

module _ {X : Set}{c d : X}{A B} where
  DiffDom-Ended : ∀ {δE c d}{E : Env δE}(l : c ∈D δE)(l' : d ∈D δE)(df : DiffDom l l')
    → Env.lookup E l ≡ « A » → Env.lookup E l' ≡ « B »
    → Env.Ended (E [ l ]≔' end) → Env.Ended (E [ l' ]≔' end) → 𝟘
  DiffDom-Ended {E = E , ._ ↦ ._} .here .(there l) (h/t l) refl ↦B E/c E/d = snd E/d
  DiffDom-Ended {E = E , ._ ↦ ._} .(there l) .here (t/h l) ↦A refl E/c E/d = snd E/c
  DiffDom-Ended {E = E , c₂ ↦ v} ._ ._ (t/t df) ↦A ↦B E/c E/d = DiffDom-Ended _ _ df ↦A ↦B (fst E/c) (fst E/d)


module _ {δE δF}{f : Env δF → Env δF} where
  DiffDoms-lookup : ∀ {δI}(I : Proto δI){lE : [ δE ]∈D δI}{lF : [ δF ]∈D δI} → DiffDoms lE lF
    → Proto.lookup (I [ lF ≔ f ]) lE ≡ Proto.lookup I lE
  DiffDoms-lookup (I ,[ Δ ]) (h/t l) = refl
  DiffDoms-lookup (I ,[ Δ ]) (t/h l) = refl
  DiffDoms-lookup (I ,[ Δ ]) (t/t df) = DiffDoms-lookup I df


module _ {c d A B}{f : ∀ {δE} → Env δE → Env δE} where
  diff-lookup : ∀ {δI}{I : Proto δI}{l : [ c ↦ A ]∈ I}{l' : [ d ↦ B ]∈ I} → DifferentVars l l'
    → Proto.lookup (I [ [↦]∈.lΔ l' ≔ f ]) ([↦]∈.lΔ l) ≡ Proto.lookup I ([↦]∈.lΔ l)
  diff-lookup {I = I}{l = mk (mk ⟨ lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ lΔ₁ , ↦Δ₁ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} (mk (diff-ten x)) = DiffDoms-lookup I x
  diff-lookup {l = mk (mk ⟨ lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ .lΔ , .↦Δ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} (mk (diff-in-ten x)) = 𝟘-elim (DiffDom-Ended {c = c}{d = d}_ _ x ↦A ↦A₁ E/c E/c₁)

{- -- bug in coveragechecking
  diff-lookup {I = I ,[ Δ ]} {mk (mk ⟨ .here , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ .(there l) , ↦Δ₁ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} (mk (diff-ten (h/t l))) = refl
  diff-lookup {I = I ,[ Δ ]} {mk (mk ⟨ .(there l) , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ .here , ↦Δ₁ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} (mk (diff-ten (t/h l))) = refl
  diff-lookup {I = I ,[ Δ ]} {mk (mk ⟨ ._ , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ ._ , ↦Δ₁ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} (mk (diff-ten (t/t x))) = ?
  diff-lookup {l = mk (mk ⟨ lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ .lΔ , .↦Δ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} (mk (diff-in-ten x)) = {!!}
-}

{-
Diff-sym : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A ]∈' I}{l' : [ d ↦ B ]∈' I}
    → DifferentVars l l' → DifferentVars l' l
Diff… (Diff-sym df) = Diff-sym… (Diff… df)
-}

data SameVar? {δI}{I : Proto δI} : ∀ {c c' A A'} → [ c ↦ A …]∈ I → [ c' ↦ A' …]∈ I → Set₁ where
  same : ∀ {c A}{l : [ c ↦ A …]∈ I} → SameVar? l l
  diff : ∀ {c c' A B}{l : [ c ↦ A …]∈ I}{l' : [ c' ↦ B …]∈ I} → DifferentVars… l l' → SameVar? l l'

sameVar? : ∀ {δI}{I : Proto δI}{c c' A A'}(l : [ c ↦ A …]∈ I)(l' : [ c' ↦ A' …]∈ I) → SameVar? l l'
sameVar? (mk4 lΔ ↦Δ _ _) (mk4 lΔ₁ ↦Δ₁ _ _) with sameDoms? lΔ lΔ₁
sameVar? (mk4 lΔ ↦Δ _ _) (mk4 lΔ₁ ↦Δ₁ _ _) | inl x = diff (diff-ten x)
sameVar? (mk4 lΔ refl lA ↦A) (mk4 .lΔ ↦Δ₁ lA₁ ↦A₁) | inr ⟨ refl , refl ⟩
  with sameDom? lA lA₁
sameVar? (mk4 lΔ refl lA ↦A) (mk4 .lΔ refl lA₁ ↦A₁) | inr ⟨ refl , refl ⟩ | inl x
  = diff (diff-in-ten x)
sameVar? (mk4 lΔ refl lA ↦A) (mk4 .lΔ refl .lA ↦A₁) | inr ⟨ refl , refl ⟩ | inr ⟨ refl , refl ⟩
  with ! ↦A ∙ ↦A₁
sameVar? (mk4 lΔ refl lA ↦A) (mk4 .lΔ refl .lA ↦A₁) | inr ⟨ refl , refl ⟩ | inr ⟨ refl , refl ⟩ | refl
  rewrite UIP ↦A ↦A₁ = same

∈♦₀… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A …]∈ I₀ → [ c ↦ A …]∈ (I₀ ♦Proto' I₁)
∈♦₀… {I₁ = I₁} (mk lI lE) = mk ([∈]♦₀ {I₁ = I₁} lI) lE --mk {!!} {!!}

∈♦₀ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈ I₀ → [ c ↦ A ]∈ (I₀ ♦Proto' I₁)
∈♦₀ (mk l… E/c) = mk (∈♦₀… l…) E/c

∈♦₁… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A …]∈ I₁ → [ c ↦ A …]∈ (I₀ ♦Proto' I₁)
∈♦₁… {I₁ = I₁} (mk lI lE) = mk ([∈]♦₁ lI) lE --mk {!!} {!!}

∈♦₁ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈ I₁ → [ c ↦ A ]∈ (I₀ ♦Proto' I₁)
∈♦₁ (mk l… E/c) = mk (∈♦₁… l…) E/c


∈♦₀-compute[…] : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₀) →
          (I₀ ♦Proto' I₁) [/…] (∈♦₀… l) ≡ (I₀ [/…] l) ♦Proto' I₁
∈♦₀-compute[…] (mk lI lE) = ≔[∈]♦₀ lI

∈♦₀-compute[] : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈ I₀) →
          (I₀ ♦Proto' I₁) [/] (∈♦₀ l) ≡ (I₀ [/] l) ♦Proto' I₁
∈♦₀-compute[] (mk lI lE) = ∈♦₀-compute[…] lI

∈♦₁-compute[…] : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₁) →
          (I₀ ♦Proto' I₁) [/…] (∈♦₁… l) ≈ I₀ ♦Proto' (I₁ [/…] l)
∈♦₁-compute[…] (mk lI lE) = ≈-reflexive (≔[∈]♦₁ lI)

postulate
  ♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto' (B ♦Proto' C) ≈ (A ♦Proto' B) ♦Proto' C
  ♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto' B) ≈ (B ♦Proto' A)
  ♦-cong₂ : ∀ {δa δb δc δd}{A : Proto δa}{B : Proto δb}{C : Proto δc}{D : Proto δd}
          → A ≈ B → C ≈ D → A ♦Proto' C ≈ B ♦Proto' D
  ♦-com, : ∀ {δa δ δb}{A : Proto δa}{B : Proto δb}{E : Env δ} → (A ,[ E ]) ♦Proto' B ≈ (A ♦Proto' B),[ E ]
  ·♦ :  ∀ {δI}{I : Proto δI} → · ♦Proto' I ≈ I
  ∈♦₀-compute… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₀) →
          (I₀ ♦Proto' I₁) /… (∈♦₀… {I₁ = I₁} l) ≈ (I₀ /… l) ♦Proto' I₁
  ∈♦₁-compute… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₁) →
          (I₀ ♦Proto' I₁) /… (∈♦₁… l) ≈ I₀ ♦Proto' (I₁ /… l)

  /Ds-com : ∀ {δs δ δ'}{I : Proto δs}(l : [ δ ]∈D δs)(l' : [ δ' ]∈D δs)
    → I /Ds l /Ds l' ≈ I /Ds l' /Ds l

  {-
  /D≔-com : ∀ {δs δ δ'}{I : Proto δs}(l : [ δ ]∈D δs)(l' : [ δ' ]∈D δs)
    {f : Env δ → Env δ}{g : Env δ' → Env δ'} → {!!}
    → I Proto.[ l ≔ f ] Proto.[ l' ≔ g ] ≈ I Proto.[ l' ≔ g ] Proto.[ l ≔ f ]
  -}
postulate
  move…-lemma : ∀ {δI} {I : Proto δI} {c d A B δE} {E : Env δE}
                {lΔ : [ δE ]∈D δI} {↦Δ : Proto.lookup I lΔ ≡ E} {δE₁}
                {E₁ : Env δE₁} {lΔ₁ : [ δE₁ ]∈D δI}
                {↦Δ₁ : Proto.lookup I lΔ₁ ≡ E₁} {lE₁ : d ↦ « B » ∈ E₁}
                (lΔ₂ : [ δE ]∈D δI) (lE : c ↦ « A » ∈ E) →
              DifferentVars… (mk3 lΔ ↦Δ lE) (mk3 lΔ₁ ↦Δ₁ lE₁) →
              Proto.lookup (I Proto.[ lΔ₂ ≔ (λ E₂ → E₂ [ _↦_∈_.lA lE ]≔' end) ])
              lΔ₁
              ≡ E₁
  move[…]-lemma : ∀ {δI} {I : Proto δI} {c d A B δE} {E : Env δE}
                  {lΔ : [ δE ]∈D δI} {↦Δ : Proto.lookup I lΔ ≡ E} {δE₁}
                  {E₁ : Env δE₁} {lΔ₁ : [ δE₁ ]∈D δI}
                  {↦Δ₁ : Proto.lookup I lΔ₁ ≡ E₁} {lE₁ : d ↦ « B » ∈ E₁}
                  (lΔ₂ : [ δE ]∈D δI) (lE : c ↦ « A » ∈ E) →
                DifferentVars… (mk3 lΔ ↦Δ lE) (mk3 lΔ₁ ↦Δ₁ lE₁) →
                Proto.lookup (I Proto.[ lΔ₂ ≔ Map.map (λ _ → end) ]) lΔ₁ ≡ E₁


move… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I) → DifferentVars… l l'
          → [ d ↦ B …]∈ (I /… l)
move… (mk3 lΔ ↦Δ lE) (mk3 lΔ₁ ↦Δ₁ lE₁) l/=l' = mk3 lΔ₁ (move…-lemma lΔ lE l/=l') lE₁

move[…] : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I) → DifferentVars… l l'
          → [ d ↦ B …]∈ (I [/…] l)
move[…] (mk3 lΔ ↦Δ lE) (mk3 lΔ₁ ↦Δ₁ lE₁) l/=l' = mk3 lΔ₁ (move[…]-lemma lΔ lE l/=l' ) lE₁

move : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I) → DifferentVars l l'
          → [ d ↦ B ]∈ (I /… [↦]∈.l… l)
move (mk l… E/c) (mk l…₁ E/c₁) df = mk (move… l… l…₁ (Diff… df)) E/c₁

move[] : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I) → DifferentVars l l'
          → [ d ↦ B ]∈ (I [/…] [↦]∈.l… l)
move[] (mk l… E/c) (mk l…₁ E/c₁) (mk Diff…) = mk (move[…] l… l…₁ Diff…) E/c₁

move-compute… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I)(l/=l' : DifferentVars… l l')
    → (I /… l) /… move… l l' l/=l' ≈ (I /… l) /D[ [↦…]∈.lΔ l' >> [↦…]∈.lA l' ]
move-compute… l l' l/l' = ≈-refl

move-compute[…] : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I)(l/=l' : DifferentVars… l l')
    → (I [/…] l) /… move[…] l l' l/=l' ≈ (I [/…] l) /D[ [↦…]∈.lΔ l' >> [↦…]∈.lA l' ]
move-compute[…] l l' l/l' = ≈-refl

{-
∈♦₀ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈' I₀ → [ c ↦ A ]∈' (I₀ ♦Proto' I₁)
∈♦₀ (mk l… E/c) = mk (∈♦₀… l…) {!!}

∈♦₁ : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A ]∈' I₁ → [ c ↦ A ]∈' (I₀ ♦Proto' I₁)
∈♦₁ (mk l… E/c) = {!!}

∈♦₀-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈' I₀) →
          (I₀ ♦Proto' I₁) [/]' (∈♦₀ l) ≈ (I₀ [/]' l) ♦Proto' I₁
∈♦₀-compute = {!!}

∈♦₁-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈' I₁) →
          (I₀ ♦Proto' I₁) [/]' (∈♦₁ l) ≈ I₀ ♦Proto' (I₁ [/]' l)
∈♦₁-compute = {!!}

move : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈' I)(l' : [ d ↦ B ]∈' I) → DifferentVars l l'
          → [ d ↦ B ]∈' (I [/]' l)
move (mk l X) (mk l' Y) df = mk (move… l l' (Diff… df)) {!!}
-}
postulate
  Sel♦ : ∀ {δs}{I : Proto δs}(σ : Selections δs) → I []/₀ σ ♦Proto' I []/₁ σ ≈ I
  Sel¬ : ∀ (b : 𝟚){δs}{I : Proto δs}(σ : Selections δs) → I []/[ b ] σ []/[ not b ] σ ≈ ·

postulate
  select : ∀ {c δI δE}{I : Proto δI}(σ : Selections δI)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
    → Map.lookup (Proto.lookup I lΔ) lA
    ≡ Map.lookup (Proto.lookup (I []/[ (Proto.lookup σ lΔ) ‼ lA ] σ) lΔ) lA

postulate
  Selections♦'/same : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) []/[ b ] (Selections♦ b σ δK) ≈ (I []/[ b ] σ) ♦Proto' K

  Selections♦'/not : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) []/[ b ] (Selections♦ (not b) σ δK) ≈ I []/[ b ] σ

  Selections/red : ∀ {δI}{I : Proto δI}(b : 𝟚)(σs : Selections δI) → I []/[ b ] σs []/[ b ] σs ≈ I []/[ b ] σs

  /[]-/Ds : ∀ {δE δI}(b : 𝟚)(I : Proto δI)(σ : Selections δI)(l : [ δE ]∈D δI)
    → (I /Ds l) []/[ b ] σ ≈ (I []/[ b ] σ) /Ds l

[/]-/D[>>]≡ : ∀ {c δE δF δI}(I : Proto δI)(l : [ δE ]∈D δI)(l' : [ δF ]∈D δI)(lc : c ∈D δE)
    → (I /D[ l >> lc ]) /Ds l' ≡ (I /Ds l') /D[ l >> lc ]
[/]-/D[>>]≡ (I ,[ Δ ]) here here lc = ap (_,[_] I) (Ended-/* _ ≡-End End/D _ lc (Ended-/* _))
[/]-/D[>>]≡ (I ,[ Δ ]) (there l) here lc = refl
[/]-/D[>>]≡ (I ,[ Δ ]) here (there l') lc = refl
[/]-/D[>>]≡ (I ,[ Δ ]) (there l) (there l') lc = ap (flip _,[_] Δ) ([/]-/D[>>]≡ I l l' lc)

[/]-/D[>>] : ∀ {c δE δF δI}(I : Proto δI)(l : [ δE ]∈D δI)(l' : [ δF ]∈D δI)(lc : c ∈D δE)
    → (I /D[ l >> lc ]) /Ds l' ≈ (I /Ds l') /D[ l >> lc ]
[/]-/D[>>] I l l' lc = ≈-reflexive ([/]-/D[>>]≡ I l l' lc)

[≔]D-ext : ∀ {δI δE}(I : Proto δI)(l : [ δE ]∈D δI){f g : Env δE → Env δE}
  (PF : f (Proto.lookup I l) ∼ g (Proto.lookup I l))
  → I Proto.[ l ≔ f ] ≈ I Proto.[ l ≔ g ]
[≔]D-ext (I ,[ Δ ]) here pf = ≈,[] ≈-refl pf
[≔]D-ext (I ,[ Δ ]) (there l) pf = ≈,[] ([≔]D-ext I l pf) ∼-refl

[≔]D-ext≡ : ∀ {δI δE}(I : Proto δI)(l : [ δE ]∈D δI){f g : Env δE → Env δE}
  (PF : f (Proto.lookup I l) ≡ g (Proto.lookup I l))
  → I Proto.[ l ≔ f ] ≡ I Proto.[ l ≔ g ]
[≔]D-ext≡ (I ,[ Δ ]) here pf = ap (_,[_] I) pf
[≔]D-ext≡ (I ,[ Δ ]) (there l) pf = ap (flip _,[_] Δ) ([≔]D-ext≡ I l pf)

[≔]-ext : ∀ {δI δE}{E : Env δE}(I : Proto δI)(l : [ E ]∈ I){f g : Env δE → Env δE}(PF : f E ∼ g E)
  → I Proto.[ [_]∈_.lΔ l ≔ f ] ≈ I Proto.[ [_]∈_.lΔ l ≔ g ]
[≔]-ext I ⟨ lΔ , ↦Δ ⟩{f}{g} pf = [≔]D-ext I lΔ (∼-reflexive (ap f ↦Δ) ∼-∙ (pf ∼-∙ ∼-reflexive (! (ap g ↦Δ))))

[≔]-ext≡ : ∀ {δI δE}{E : Env δE}(I : Proto δI)(l : [ E ]∈ I){f g : Env δE → Env δE}(PF : f E ≡ g E)
  → I Proto.[ [_]∈_.lΔ l ≔ f ] ≡ I Proto.[ [_]∈_.lΔ l ≔ g ]
[≔]-ext≡ I ⟨ lΔ , ↦Δ ⟩{f}{g} pf = [≔]D-ext≡ I lΔ (ap f ↦Δ ∙ (pf ∙ ! (ap g ↦Δ)))

/…-uniq : ∀ {δI c A}{I : Proto δI}(l : [ c ↦ A ]∈ I) → I /… [↦]∈.l… l ≈ I [/] l
/…-uniq {I = I} (mk (mk ⟨ lΔ , refl ⟩ lE) E/c) = [≔]D-ext I lΔ (E/c ∼-End Ended-/* _)

/…-uniq≡ : ∀ {δI c A}{I : Proto δI}(l : [ c ↦ A ]∈ I) → I /… [↦]∈.l… l ≡ I [/] l
/…-uniq≡ {I = I} (mk (mk ⟨ lΔ , refl ⟩ lE) E/c) = [≔]D-ext≡ I lΔ (E/c ≡-End Ended-/* _)

{-
[≔]-ext (I ,[ Δ ]) heRe[] pf = ≈,[] ≈-refl pf
[≔]-ext (I ,[ Δ ]) (theRe[] lΔ) pf = ≈,[] ([≔]-ext I ⟨ lΔ R[]⟩ pf) ∼-refl
-}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
