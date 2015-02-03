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
open import partensor.Shallow.Dom as Dom
import partensor.Shallow.Session as Session
import partensor.Shallow.Map as Map
import partensor.Shallow.Env as Env
import partensor.Shallow.Proto as Proto
open Session hiding (Ended)
open Env     hiding (_/₀_; _/₁_; _/[_]_; Ended)
open Proto   hiding ()
open import partensor.Shallow.Equiv' hiding (♦-assoc ; ♦-com ; ♦-com, ; /Ds-com)
open import partensor.Shallow.Term

module partensor.Shallow.Vars where


infixl 4 _♦Proto'_
abstract
  _♦Proto'_ : ∀ {δa δb}(A : Proto δa)(B : Proto δb) → Proto (δa ♦Doms δb)
  _♦Proto'_ = _♦Proto_

  lookup-[]∈♦'₀ : ∀ {δ δE δF}(E : Proto δE)(F : Proto δF)(l : Doms'.[ δ ]∈ δE)
    → Proto.lookup (E ♦Proto' F) ([]∈♦₀ {δF = δF} l) ≡ Proto.lookup E l
  lookup-[]∈♦'₀ = lookup-[]∈♦₀

  /Ds-[]∈♦'₀ : ∀ {δ δI δK}{I : Proto δI}(l : Doms'.[ δ ]∈ δI)(K : Proto δK)
     → (I /Ds l) ♦Proto' K ≡ (I ♦Proto' K) /Ds ([]∈♦₀ {δF = δK} l)
  /Ds-[]∈♦'₀ l = /Ds-[]∈♦₀ l

[∈]♦₀ : ∀ {δ₀ δ₁ δE}{E : Env δE}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ E ]∈ I₀ → [ E ]∈ (I₀ ♦Proto' I₁)
[∈]♦₀ {δ₁ = δ₁}{I₁ = F}(mk lΔ ↦Δ) = mk ([]∈♦₀ {δF = δ₁} lΔ ) (lookup-[]∈♦'₀ _ F lΔ ∙ ↦Δ)

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

data DifferentVars… {δI}{I : Proto δI}{c d A B} : (lA : [ c ↦ A …]∈ I)(lB : [ d ↦ B …]∈ I) → Set₁ where
  diff-ten : ∀ {δF δG}{F : Env δF}{G : Env δG}{lA : Doms'.[ δF ]∈ δI}{lB : Doms'.[ δG ]∈ δI}
    {↦A : Proto.lookup I lA ≡ F}{c↦ : c ↦ A ∈ F} {↦B : Proto.lookup I lB ≡ G}{d↦ : d ↦ B ∈ G}
    → DiffDoms' lA lB → DifferentVars… (mk (mk lA ↦A) c↦) (mk (mk lB ↦B) d↦)
  diff-in-ten : ∀ {δF}{F : Env δF}{lF : Doms'.[ δF ]∈ δI}{↦F : Proto.lookup I lF ≡ F}
     {c∈ : c Dom'.∈ δF}{↦c : Map.lookup F c∈ ≡ A}{d∈ : d Dom'.∈ δF}{↦d : Map.lookup F d∈ ≡ B}
    → DiffDom' c∈ d∈
    → DifferentVars… (mk (mk lF ↦F) (mk c∈ ↦c)) (mk (mk lF ↦F) (mk d∈ ↦d))

postulate
  -- DifferentVars… : ∀ {δI}{I : Proto δI}{c d A B} → [ c ↦ A …]∈' I → [ d ↦ B …]∈' I → Set
  Diff-sym… : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A …]∈ I}{l' : [ d ↦ B …]∈ I}
    → DifferentVars… l l' → DifferentVars… l' l

{-
record DifferentVars {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A ]∈' I)(l' : [ d ↦ B ]∈' I) : Set where
  constructor mk
  field
    Diff… : DifferentVars… ([↦]∈'.l… l) ([↦]∈'.l… l')
open DifferentVars

Diff-sym : ∀ {δI}{I : Proto δI}{c d A B}{l : [ c ↦ A ]∈' I}{l' : [ d ↦ B ]∈' I}
    → DifferentVars l l' → DifferentVars l' l
Diff… (Diff-sym df) = Diff-sym… (Diff… df)
-}

data SameVar? {δI}{I : Proto δI} : ∀ {c c' A A'} → [ c ↦ A …]∈ I → [ c' ↦ A' …]∈ I → Set₁ where
  same : ∀ {c A}{l : [ c ↦ A …]∈ I} → SameVar? l l
  diff : ∀ {c c' A B}{l : [ c ↦ A …]∈ I}{l' : [ c' ↦ B …]∈ I} → DifferentVars… l l' → SameVar? l l'

sameVar? : ∀ {δI}{I : Proto δI}{c c' A A'}(l : [ c ↦ A …]∈ I)(l' : [ c' ↦ A' …]∈ I) → SameVar? l l'
sameVar? (mk (mk lΔ ↦Δ) lE) (mk (mk lΔ₁ ↦Δ₁) lE₁) with sameDoms? lΔ lΔ₁
sameVar? (mk (mk lΔ ↦Δ) lE) (mk (mk lΔ₁ ↦Δ₁) lE₁) | inj₁ x = diff (diff-ten x)
sameVar? (mk (mk lΔ refl) (mk lA ↦A)) (mk (mk .lΔ ↦Δ₁) (mk lA₁ ↦A₁)) | inj₂ ⟨ refl , refl ⟩
  with sameDom? lA lA₁
sameVar? (mk (mk lΔ refl) (mk lA ↦A)) (mk (mk .lΔ refl) (mk lA₁ ↦A₁)) | inj₂ ⟨ refl , refl ⟩ | inj₁ x
  = diff (diff-in-ten x)
sameVar? (mk (mk lΔ refl) (mk lA refl)) (mk (mk .lΔ refl) (mk .lA refl)) | inj₂ ⟨ refl , refl ⟩ | inj₂ ⟨ refl , refl ⟩ = same


∈♦₀… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A …]∈ I₀ → [ c ↦ A …]∈ (I₀ ♦Proto' I₁)
∈♦₀… {I₁ = I₁} (mk lI lE) = mk ([∈]♦₀ {I₁ = I₁} lI) lE --mk {!!} {!!}

postulate
  TC-conv : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
    → I ≈ J → TC'⟨ I ⟩ → TC'⟨ J ⟩

  ♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto' (B ♦Proto' C) ≈ (A ♦Proto' B) ♦Proto' C
  ♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto' B) ≈ (B ♦Proto' A)
  ♦-cong₂ : ∀ {δa δb δc δd}{A : Proto δa}{B : Proto δb}{C : Proto δc}{D : Proto δd}
          → A ≈ B → C ≈ D → A ♦Proto' C ≈ B ♦Proto' D
  ♦-com, : ∀ {δa δ δb}{A : Proto δa}{B : Proto δb}{E : Env δ} → (A ,[ E ]) ♦Proto' B ≈ (A ♦Proto' B),[ E ]
  ∈♦₁… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁} → [ c ↦ A …]∈ I₁ → [ c ↦ A …]∈ (I₀ ♦Proto' I₁)
  ∈♦₀-compute… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₀) →
          (I₀ ♦Proto' I₁) /… (∈♦₀… {I₁ = I₁} l) ≈ (I₀ /… l) ♦Proto' I₁
  ∈♦₀-compute[…] : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₀) →
          (I₀ ♦Proto' I₁) [/…] (∈♦₀… {I₁ = I₁}l) ≈ (I₀ [/…] l) ♦Proto' I₁
  ∈♦₁-compute… : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₁) →
          (I₀ ♦Proto' I₁) /… (∈♦₁… l) ≈ I₀ ♦Proto' (I₁ /… l)
  ∈♦₁-compute[…] : ∀ {δ₀ δ₁ c A}{I₀ : Proto δ₀}{I₁ : Proto δ₁}(l : [ c ↦ A …]∈ I₁) →
          (I₀ ♦Proto' I₁) [/…] (∈♦₁… l) ≈ I₀ ♦Proto' (I₁ [/…] l)

  /Ds-com : ∀ {δs δ δ'}{I : Proto δs}(l : Doms'.[ δ ]∈ δs)(l' : Doms'.[ δ' ]∈ δs)
    → I /Ds l /Ds l' ≈ I /Ds l' /Ds l

  {-
  /D≔-com : ∀ {δs δ δ'}{I : Proto δs}(l : Doms'.[ δ ]∈ δs)(l' : Doms'.[ δ' ]∈ δs)
    {f : Env δ → Env δ}{g : Env δ' → Env δ'} → {!!}
    → I Proto.[ l ≔ f ] Proto.[ l' ≔ g ] ≈ I Proto.[ l' ≔ g ] Proto.[ l ≔ f ]
  -}
postulate
  move…-lemma : ∀ {δI} {I : Proto δI} {c d A B δE} {E : Env δE}
                {lΔ : Doms'.[ δE ]∈ δI} {↦Δ : Proto.lookup I lΔ ≡ E} {δE₁}
                {E₁ : Env δE₁} {lΔ₁ : Doms'.[ δE₁ ]∈ δI}
                {↦Δ₁ : Proto.lookup I lΔ₁ ≡ E₁} {lE₁ : d ↦ B ∈ E₁}
                (lΔ₂ : Doms'.[ δE ]∈ δI) (lE : c ↦ A ∈ E) →
              DifferentVars… (mk (mk lΔ ↦Δ) lE) (mk (mk lΔ₁ ↦Δ₁) lE₁) →
              Proto.lookup (I Proto.[ lΔ₂ ≔ (λ E₂ → E₂ [ _↦_∈_.lA lE ]≔' end) ])
              lΔ₁
              ≡ E₁
  move[…]-lemma : ∀ {δI} {I : Proto δI} {c d A B δE} {E : Env δE}
                  {lΔ : Doms'.[ δE ]∈ δI} {↦Δ : Proto.lookup I lΔ ≡ E} {δE₁}
                  {E₁ : Env δE₁} {lΔ₁ : Doms'.[ δE₁ ]∈ δI}
                  {↦Δ₁ : Proto.lookup I lΔ₁ ≡ E₁} {lE₁ : d ↦ B ∈ E₁}
                  (lΔ₂ : Doms'.[ δE ]∈ δI) (lE : c ↦ A ∈ E) →
                DifferentVars… (mk (mk lΔ ↦Δ) lE) (mk (mk lΔ₁ ↦Δ₁) lE₁) →
                Proto.lookup (I Proto.[ lΔ₂ ≔ Map.map (λ _ → end) ]) lΔ₁ ≡ E₁


move… : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I) → DifferentVars… l l'
          → [ d ↦ B …]∈ (I /… l)
move… (mk (mk lΔ ↦Δ) lE) (mk (mk lΔ₁ ↦Δ₁) lE₁) l/=l' = mk (mk lΔ₁ (move…-lemma lΔ lE l/=l')) lE₁

move[…] : ∀ {δI}{I : Proto δI}{c d A B}(l : [ c ↦ A …]∈ I)(l' : [ d ↦ B …]∈ I) → DifferentVars… l l'
          → [ d ↦ B …]∈ (I [/…] l)
move[…] (mk (mk lΔ ↦Δ) lE) (mk (mk lΔ₁ ↦Δ₁) lE₁) l/=l' = mk (mk lΔ₁ (move[…]-lemma lΔ lE l/=l' )) lE₁ -- mk {!!} {!!}

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
  End/₀ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₀ σ)
  End/₁ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./₁ σ)
  End/[b] : ∀ {δ}{E : Env δ}(b : 𝟚)(σ : Selection δ) → Env.Ended E → Env.Ended (E Env./[ b ] σ)
  Sel♦ : ∀ {δs}{I : Proto δs}(σ : Selections δs) → I /₀ σ ♦Proto' I /₁ σ ≈ I

postulate
  select : ∀ {c δI δE}{I : Proto δI}(σ : Selections δI)(lΔ : Doms'.[ δE ]∈ δI)(lA : c Dom'.∈ δE)
    → Map.lookup (Proto.lookup I lΔ) lA
    ≡ Map.lookup (Proto.lookup (I /[ Map.lookup (Proto.lookup σ lΔ) lA ] σ) lΔ) lA

eselect-com : ∀ {c δE}(E : Env δE)(σ : Selection δE)(lA : c Dom'.∈ δE)
  → let b = not (Map.lookup σ lA)
  in E Env./[ b ] σ ∼ (E Env.[ lA ]≔' end) Env./[ b ] σ
eselect-com (E , c ↦ v) (σ , .c ↦ 1₂) here = ∼-refl
eselect-com (E , c ↦ v) (σ , .c ↦ 0₂) here = ∼-refl
eselect-com (E , c₁ ↦ v) (σ , .c₁ ↦ v₁) (there lA) = ∼,↦ (eselect-com E σ lA)

select-com : ∀ {c δI δE}{I : Proto δI}(σ : Selections δI)(lΔ : Doms'.[ δE ]∈ δI)(lA : c Dom'.∈ δE)
    → let b = not (Map.lookup (Proto.lookup σ lΔ) lA)
    in I /[ b ] σ ≈ (I /D[ lΔ >> lA ]) /[ b ] σ
select-com {I = I ,[ Δ ]} (σ ,[ Δ₁ ]) Doms'.here lA = ≈,[] ≈-refl (eselect-com Δ Δ₁ lA)
select-com {I = I ,[ Δ ]} (σ ,[ Δ₁ ]) (Doms'.there lΔ) lA = ≈,[] (select-com σ lΔ lA) ∼-refl

module _ {δI}(b : 𝟚)(σ : Selections δI) where
  Selections♦ : ∀ δK → Selections (δI ♦Doms δK)
  Selections♦ · = σ
  Selections♦ (δK ,[ x ]) = Selections♦ δK ,[ constMap x b ]

  atMost♦ : ∀ {n} δK → AtMost n σ → AtMost n (Selections♦ δK)
  atMost♦ · A = A
  atMost♦ (δK ,[ x ]) A = atMost♦ δK A ,[ (₀₁ b (pureAll x (λ _ → refl))) ]

Selection/[]same : ∀ {δ}(Δ : Env δ)(b : 𝟚)
  → Δ Env./[ b ] (constMap δ b) ∼ Δ
Selection/[]same ε b = ∼-refl
Selection/[]same (Δ , c ↦ v) 1₂ = ∼,↦ (Selection/[]same Δ 1₂)
Selection/[]same (Δ , c ↦ v) 0₂ = ∼,↦ (Selection/[]same Δ 0₂)

Selections♦/same : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto K) /[ b ] (Selections♦ b σ δK) ≈ (I /[ b ] σ) ♦Proto K
Selections♦/same {K = ·} b σ = ≈-refl
Selections♦/same {K = K ,[ Δ ]} b σ = ≈,[] (Selections♦/same {K = K} b σ ) (Selection/[]same Δ b)

Selection/[]not : ∀ {δ}(Δ : Env δ)(b : 𝟚)
  → Env.Ended (Δ Env./[ b ] (constMap δ (not b)))
Selection/[]not ε b = _
Selection/[]not (Δ , c ↦ v) 1₂ = ⟨ (Selection/[]not Δ 1₂) , _ ⟩
Selection/[]not (Δ , c ↦ v) 0₂ = ⟨ (Selection/[]not Δ 0₂) , _ ⟩

Selections♦/not : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto K) /[ b ] (Selections♦ (not b) σ δK) ≈ I /[ b ] σ
Selections♦/not {K = ·} b σ = ≈-refl
Selections♦/not {K = K ,[ Δ ]} b σ = ≈-trans (≈,[end] (Selection/[]not Δ b)) (Selections♦/not {K = K}b σ)

postulate
  Selections♦'/same : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) /[ b ] (Selections♦ b σ δK) ≈ (I /[ b ] σ) ♦Proto' K

  Selections♦'/not : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
    → (I ♦Proto' K) /[ b ] (Selections♦ (not b) σ δK) ≈ I /[ b ] σ

  /[]-/Ds : ∀ {δE δI}(b : 𝟚)(I : Proto δI)(σ : Selections δI)(l : Doms'.[ δE ]∈ δI)
    → (I /Ds l) /[ b ] σ ≈ (I /[ b ] σ) /Ds l

-- Really clever proof yay!
[]≔end/[] : ∀ {c δE}(E : Env δE)(l : c Dom'.∈ δE)(b : 𝟚)(σ : Selection δE)
  → (E [ l ]≔' end) Env./[ b ] σ ∼ (E Env./[ b ] σ) [ l ]≔' end
[]≔end/[] (E , c ↦ v) here 1₂ (σ , .c ↦ 1₂) = ∼-refl
[]≔end/[] (E , c ↦ v) here 1₂ (σ , .c ↦ 0₂) = ∼-refl
[]≔end/[] (E , c ↦ v) here 0₂ (σ , .c ↦ 1₂) = ∼-refl
[]≔end/[] (E , c ↦ v) here 0₂ (σ , .c ↦ 0₂) = ∼-refl
[]≔end/[] (E , c₁ ↦ v) (there l) b (σ , .c₁ ↦ v₁) = ∼,↦ ([]≔end/[] E l b σ)

/[]-/D[>>] : ∀ {c δE δI}(b : 𝟚)(I : Proto δI)(σ : Selections δI)(l : Doms'.[ δE ]∈ δI)(l' : c Dom'.∈ δE)
    → (I /D[ l >> l' ]) /[ b ] σ ≈ (I /[ b ] σ) /D[ l >> l' ]
/[]-/D[>>] b (I ,[ Δ ]) (σ ,[ Δ₁ ]) Doms'.here l' = ≈,[] ≈-refl ([]≔end/[] Δ l' b Δ₁)
/[]-/D[>>] b (I ,[ Δ ]) (σ ,[ Δ₁ ]) (Doms'.there l) l' = ≈,[] (/[]-/D[>>] b I σ l l') ∼-refl


/*-End : ∀ {δE}(E : Env δE) → Env.Ended (E /*)
/*-End E = mapAll (λ _ → _) E

End≔end : ∀ {c δE}(E : Env δE)(l : c Dom'.∈ δE) → Env.Ended E → Env.Ended (E [ l ]≔' end)
End≔end (E , c ↦ v) here EE = ⟨ (fst EE) , _ ⟩
End≔end (E , c₁ ↦ v) (there l) EE = ⟨ (End≔end E l (fst EE)) , (snd EE) ⟩

[/]-/D[>>] : ∀ {c δE δF δI}(I : Proto δI)(l : Doms'.[ δE ]∈ δI)(l' : Doms'.[ δF ]∈ δI)(lc : c Dom'.∈ δE)
    → (I /D[ l >> lc ]) /Ds l' ≈ (I /Ds l') /D[ l >> lc ]
[/]-/D[>>] (I ,[ Δ ]) Doms'.here Doms'.here lc = ≈,[] ≈-refl (/*-End _ ∼-End End≔end _ lc (/*-End Δ))
[/]-/D[>>] (I ,[ Δ ]) (Doms'.there l) Doms'.here lc = ≈-refl
[/]-/D[>>] (I ,[ Δ ]) Doms'.here (Doms'.there l') lc = ≈-refl
[/]-/D[>>] (I ,[ Δ ]) (Doms'.there l) (Doms'.there l') lc = ≈,[] ([/]-/D[>>] I l l' lc) ∼-refl


/Ds-/[] : ∀ {δE δI}(b : 𝟚)(I : Proto δI)(lΔ : Doms'.[ δE ]∈ δI)(σ : Selections δI)
  → Env.Ended (Proto.lookup I lΔ Env./[ b ] Proto.lookup σ lΔ)
  → (I /Ds lΔ) /[ b ] σ ≈ I /[ b ] σ
/Ds-/[] b (I ,[ Δ ]) Doms'.here (σ ,[ Δ₁ ]) En = ≈,[] ≈-refl (End/[b] b Δ₁ (/*-End Δ) ∼-End En)
/Ds-/[] b (I ,[ Δ ]) (Doms'.there lΔ) (σ ,[ Δ₁ ]) En = ≈,[] (/Ds-/[] b I lΔ σ En) ∼-refl

-- Really clever proof yay!
SEnd// :(b : 𝟚)(S : Session)(σ : 𝟚) → Session.Ended (Env.selectProj (not b) (Env.selectProj b S σ) σ)
SEnd// 1₂ S 1₂ = 0₁
SEnd// 1₂ S 0₂ = 0₁
SEnd// 0₂ S 1₂ = 0₁
SEnd// 0₂ S 0₂ = 0₁

End// : ∀ {δE}(b : 𝟚)(E : Env δE)(σ : Selection δE) → Env.Ended ((E Env./[ b ] σ) Env./[ not b ] σ)
End// b ε ε = _
End// b (E , c ↦ v) (σ , .c ↦ v₁) = ⟨ (End// b E σ) , SEnd// b v v₁ ⟩

[≔]-ext : ∀ {δI δE}{E : Env δE}(I : Proto δI)(l : [ E ]∈ I){f g : Env δE → Env δE}(PF : f E ∼ g E)
  → I Proto.[ [_]∈_.lΔ l ≔ f ] ≈ I Proto.[ [_]∈_.lΔ l ≔ g ]
[≔]-ext (I ,[ Δ ]) (mk Doms'.here refl) pf = ≈,[] ≈-refl pf
[≔]-ext (I ,[ Δ ]) (mk (Doms'.there lΔ) ↦Δ) pf = ≈,[] ([≔]-ext I (mk lΔ ↦Δ) pf) ∼-refl
