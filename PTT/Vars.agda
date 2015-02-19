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
open Proto hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com ; ·♦ ; select ; ♦-cong₂ ; Sel♦)
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

  atMost♦' : ∀ {δI}(b : 𝟚)(σ : Selections δI){n}{I : Proto δI}{δK}(K : Proto δK) → AtMost n I σ
     → AtMost n (I ♦Proto' K) (Selections♦ b σ δK)
  atMost♦' = atMost♦

  ♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto' (B ♦Proto' C) ≈ (A ♦Proto' B) ♦Proto' C
  ♦-assoc {A = A}{B}{C} = Proto.♦-assoc {A = A}{B}{C}

  ♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto' B) ≈ (B ♦Proto' A)
  ♦-com {A = A}{B} = Proto.♦-com {A = A}{B}

  ♦-com, : ∀ {δa δ δb}{A : Proto δa}{B : Proto δb}{E : Env δ} → (A ,[ E ]) ♦Proto' B ≈ (A ♦Proto' B),[ E ]
  ♦-com, {A = A}{B} = Proto.♦-com, {A = A}{B}

  ·♦ :  ∀ {δI}{I : Proto δI} → · ♦Proto' I ≈ I
  ·♦ = Proto.·♦

  Selections♦'/same : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) []/[ b ] (Selections♦ b σ δK) ≈ (I []/[ b ] σ) ♦Proto' K
  Selections♦'/same {I = I}{K} = Selections♦/same {I = I}{K}

  Selections♦'/not : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) []/[ b ] (Selections♦ (not b) σ δK) ≈ I []/[ b ] σ
  Selections♦'/not {I = I}{K} = Selections♦/not {I = I}{K}

  select : ∀ {c δI δE}{I : Proto δI}(σ : Selections δI)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
    → Map.lookup (Proto.lookup I lΔ) lA
    ≡ Map.lookup (Proto.lookup (I []/[ (Proto.lookup σ lΔ) ‼ lA ] σ) lΔ) lA
  select = Proto.select

  ♦-cong₂ : ∀ {δa δb δc δd}{A : Proto δa}{B : Proto δb}{C : Proto δc}{D : Proto δd}
          → A ≈ B → C ≈ D → A ♦Proto' C ≈ B ♦Proto' D
  ♦-cong₂ = Proto.♦-cong₂

  Sel♦ : ∀ {δs}{I : Proto δs}{σ : Selections δs} → AtMost 0 I σ → I []/₀ σ ♦Proto' I []/₁ σ ≈ I
  Sel♦ = Proto.Sel♦



data DifferentVars… {δI}{I : Proto δI}{c d A B} : (lA : [ c ↦ A …]∈ I)(lB : [ d ↦ B …]∈ I) → Set₁ where
  diff-ten : ∀ {δF δG}{F : Env δF}{G : Env δG}{lA : [ δF ]∈D δI}{lB : [ δG ]∈D δI}
    {↦A : Proto.lookup I lA ≡ F}{c↦ : c ↦ « A » ∈ F} {↦B : Proto.lookup I lB ≡ G}{d↦ : d ↦ « B » ∈ G}
    → DiffDoms lA lB → DifferentVars… (mk ⟨ lA , ↦A ⟩ c↦) (mk ⟨ lB , ↦B ⟩ d↦)
  diff-in-ten : ∀ {δF}{F : Env δF}{lF : [ δF ]∈D δI}{↦F : Proto.lookup I lF ≡ F}
     {c∈ : c ∈D δF}{↦c : Map.lookup F c∈ ≡ « A »}{d∈ : d ∈D δF}{↦d : Map.lookup F d∈ ≡ « B »}
    → DiffDom c∈ d∈
    → DifferentVars… (mk4 lF ↦F c∈ ↦c) (mk4 lF ↦F d∈ ↦d)

DiffDoms-sym : ∀ {δE δF δI}{lE : [ δE ]∈D δI}{lF : [ δF ]∈D δI} → DiffDoms lE lF → DiffDoms lF lE
DiffDoms-sym (h/t l) = t/h l
DiffDoms-sym (t/h l) = h/t l
DiffDoms-sym (t/t x) = t/t (DiffDoms-sym x)

DiffDom-sym : ∀ {c d δE} {lA : c ∈D δE} {lA₁ : d ∈D δE} → DiffDom lA lA₁ → DiffDom lA₁ lA
DiffDom-sym (h/t l) = t/h l
DiffDom-sym (t/h l) = h/t l
DiffDom-sym (t/t x) = t/t (DiffDom-sym x)

  -- DifferentVars… : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A …]∈' I → [ d ↦ B …]∈' I → Set
Diff-sym… : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A …]∈ I}{l' : [ d ↦ B …]∈ I}
    → DifferentVars… l l' → DifferentVars… l' l
Diff-sym… {l = mk ⟨ lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩} {mk ⟨ lΔ₁ , ↦Δ₁ ⟩ ⟨ lA₁ , ↦A₁ ⟩} (diff-ten x) = diff-ten (DiffDoms-sym x)
Diff-sym… {l = mk ⟨ lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩} {mk ⟨ .lΔ , .↦Δ ⟩ ⟨ lA₁ , ↦A₁ ⟩} (diff-in-ten x) = diff-in-ten (DiffDom-sym x)

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


module _ {c d A B} where
  diff-lookup : ∀ {δI}{I : Proto δI}{l : [ c ↦ A ]∈ I}{l' : [ d ↦ B ]∈ I}(f : Env ([↦]∈.δE l') → Env ([↦]∈.δE l'))
    → DifferentVars l l' → Proto.lookup (I [ [↦]∈.lΔ l' ≔ f ]) ([↦]∈.lΔ l) ≡ Proto.lookup I ([↦]∈.lΔ l)
  diff-lookup {I = I}{l = mk (mk ⟨ lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ lΔ₁ , ↦Δ₁ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} f (mk (diff-ten x))
     = DiffDoms-lookup I x
  diff-lookup {l = mk (mk ⟨ lΔ , ↦Δ ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ .lΔ , .↦Δ ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} f (mk (diff-in-ten x))
     = 𝟘-elim (DiffDom-Ended {c = c}{d = d}_ _ x ↦A ↦A₁ E/c E/c₁)

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


∈♦₀-compute… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₀) →
          (I₀ ♦Proto' I₁) /… (∈♦₀… l) ≡ (I₀ /… l) ♦Proto' I₁
∈♦₀-compute… (mk lI lE) = ≔[∈]♦₀ lI

∈♦₀-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈ I₀) →
          (I₀ ♦Proto' I₁) / (∈♦₀ l) ≡ (I₀ / l) ♦Proto' I₁
∈♦₀-compute (mk lI lE) = ∈♦₀-compute… lI

∈♦₁-compute… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₁) →
          (I₀ ♦Proto' I₁) /… (∈♦₁… l) ≈ I₀ ♦Proto' (I₁ /… l)
∈♦₁-compute… (mk lI lE) = ≈-reflexive (≔[∈]♦₁ lI)

∈♦₁-compute : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A ]∈ I₁) →
          (I₀ ♦Proto' I₁) / (∈♦₁ l) ≈ I₀ ♦Proto' (I₁ / l)
∈♦₁-compute (mk lI lE) = ∈♦₁-compute… lI

move…-lemma : ∀ {δI c d A B}{I : Proto δI}{l : [ c ↦ A ]∈ I}{l' : [ d ↦ B ]∈ I}
  → DifferentVars l l'
  → Proto.lookup (I / l) ([↦]∈.lΔ l') ≡ [↦]∈.E l'
move…-lemma {I = I}{mk5 lΔ ↦Δ lA ↦A E/c} {mk5 lΔ₁ refl lA₁ ↦A₁ E/c₁} (mk (diff-ten x))
  = lookup-diff I lΔ lΔ₁ _ x
move…-lemma {I = I} {l = mk (mk ⟨ lΔ , refl ⟩ ⟨ lA , ↦A ⟩) E/c} {mk (mk ⟨ .lΔ , .refl ⟩ ⟨ lA₁ , ↦A₁ ⟩) E/c₁} (mk (diff-in-ten x))
  = 𝟘-elim (tr Session.Ended (E-lookup-diff (Proto.lookup I lΔ) x ∙ ↦A₁) (All∈D E/c lA₁))

{-
move…-lemma : ∀ {δI δE δE₁ c d A B}{I : Proto δI}{E : Env δE}{E₁ : Env δE₁}(lΔ : [ δE ]∈D δI)(lΔ₁ : [ δE₁ ]∈D δI)
     (lE : c ↦ « A » ∈ E)(lE₁ : d ↦ « B » ∈ E₁)
     (↦Δ : Proto.lookup I lΔ ≡ E)(↦Δ₁ : Proto.lookup I lΔ₁ ≡ E₁)
     (E/c : Env.Ended (E [ ↦∈.lA lE ]≔' end))
     (E/c : Env.Ended (E₁ [ ↦∈.lA lE₁ ]≔' end))
     (l/=l' : DifferentVars… (mk ⟨ lΔ , ↦Δ ⟩ lE) (mk ⟨ lΔ₁ , ↦Δ₁ ⟩ lE₁))
    → Proto.lookup (I [ lΔ ≔ (λ Δ → Δ [ ↦∈.lA lE ]≔' end) ]) lΔ₁ ≡ E₁
move…-lemma lΔ lΔ₁ lE lE₁ ↦Δ ↦Δ₁ E/c E/c₁ (diff-ten x) = {!!}
move…-lemma lΔ .lΔ ._ ._ ↦Δ .↦Δ E/c E/c₁ (diff-in-ten x) = {!!}
-}

{-
move… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I) → DifferentVars… l l'
          → [ d ↦ B …]∈ (I /… l)
move… (mk3 lΔ ↦Δ lE) (mk3 lΔ₁ ↦Δ₁ lE₁) l/=l' = mk3 lΔ₁ (move…-lemma lΔ lΔ₁ lE lE₁ ↦Δ ↦Δ₁ l/=l') lE₁
-}

move : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈ I)(l' : [ d ↦ B ]∈ I) → DifferentVars l l'
          → [ d ↦ B ]∈ (I / l)
move l (mk5 lΔ₁ ↦Δ₁ lA₁ ↦A₁ E/c₁) df = mk5 lΔ₁ (move…-lemma df) lA₁ ↦A₁ E/c₁
-- mk (move… l… l…₁ (Diff… df)) E/c₁

{-
move-compute… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I)(l/=l' : DifferentVars… l l')
    → (I /… l) /… move… l l' l/=l' ≈ (I /… l) /D[ [↦…]∈.lΔ l' >> [↦…]∈.lA l' ]
move-compute… l l' l/l' = ≈-refl
-}

[/]-/D[>>]≡ : ∀ {c δE δF δI}(I : Proto δI)(l : [ δE ]∈D δI)(l' : [ δF ]∈D δI)(lc : c ∈D δE)
    → (I /D[ l >> lc ]) /Ds l' ≡ (I /Ds l') /D[ l >> lc ]
[/]-/D[>>]≡ (I ,[ Δ ]) here here lc = ap (_,[_] I) (Ended-/* _ ≡-End End/D _ lc (Ended-/* _))
[/]-/D[>>]≡ (I ,[ Δ ]) (there l) here lc = refl
[/]-/D[>>]≡ (I ,[ Δ ]) here (there l') lc = refl
[/]-/D[>>]≡ (I ,[ Δ ]) (there l) (there l') lc = ap (flip _,[_] Δ) ([/]-/D[>>]≡ I l l' lc)

[/]-/D[>>] : ∀ {c δE δF δI}(I : Proto δI)(l : [ δE ]∈D δI)(l' : [ δF ]∈D δI)(lc : c ∈D δE)
    → (I /D[ l >> lc ]) /Ds l' ≈ (I /Ds l') /D[ l >> lc ]
[/]-/D[>>] I l l' lc = ≈-reflexive ([/]-/D[>>]≡ I l l' lc)


/D[>>]-/D[>>]≡ : ∀ {c d δE δF δI}(I : Proto δI)(l : [ δE ]∈D δI)(l' : [ δF ]∈D δI)(lc : c ∈D δE)(lc' : d ∈D δF)
    → (I /D[ l >> lc ]) /D[ l' >> lc' ] ≡ (I /D[ l' >> lc' ]) /D[ l >> lc ]
/D[>>]-/D[>>]≡ (I ,[ Δ ]) here here lc lc' rewrite ≔'-com {x = end} Δ lc lc' = refl
/D[>>]-/D[>>]≡ (I ,[ Δ ]) here (there l') lc lc' = refl
/D[>>]-/D[>>]≡ (I ,[ Δ ]) (there l) here lc lc' = refl
/D[>>]-/D[>>]≡ (I ,[ Δ ]) (there l) (there l') lc lc' = ap (flip _,[_] Δ) (/D[>>]-/D[>>]≡ I l l' lc lc')

/D[>>]-/D[>>] : ∀ {c d δE δF δI}(I : Proto δI)(l : [ δE ]∈D δI)(l' : [ δF ]∈D δI)(lc : c ∈D δE)(lc' : d ∈D δF)
    → (I /D[ l >> lc ]) /D[ l' >> lc' ] ≈ (I /D[ l' >> lc' ]) /D[ l >> lc ]
/D[>>]-/D[>>] I l l' lc lc' = ≈-reflexive (/D[>>]-/D[>>]≡ I l l' lc lc')

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


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
