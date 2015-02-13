{-# OPTIONS --copattern #-}
open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Nat
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP

open import PTT.Dom
open import PTT.Session as Session hiding (Ended)
import PTT.Map as Map
open Map using (Map; ε; _,_↦_; _↦_∈_; SelectionAll≡)
open import PTT.Env as Env hiding (Ended; All; lookup; pure; zipWith)

module PTT.Proto where

Sel = Env.Selection

infixl 3 _,[_]

data Doms  : Set where
  · : Doms
  _,[_] : Doms → Dom → Doms

infix 3 [_]∈D_
data [_]∈D_ (δ : Dom) : Doms → Set where
  here  : ∀ {δs} → [ δ ]∈D δs ,[ δ ]
  there : ∀ {δs δ'} → [ δ ]∈D δs → [ δ ]∈D δs ,[ δ' ]

pattern hereDs = [_]∈D_.here
pattern thereDs p = [_]∈D_.there p

data DiffDoms : ∀ {δ δ' δs} → [ δ ]∈D δs → [ δ' ]∈D δs → Set where
  h/t : ∀ {δ δ' δs}(l : [ δ' ]∈D δs) → DiffDoms (here {δ}{δs}) (there l)
  t/h : ∀ {δ δ' δs}(l : [ δ' ]∈D δs) → DiffDoms (there l) (here {δ}{δs})
  t/t : ∀ {δ δ' δj δs}{l : [ δ ]∈D δs}{l' : [ δ' ]∈D δs} → DiffDoms l l'
    → DiffDoms {δs = δs ,[ δj ]} (there l) (there l')

sameDoms? : ∀ {δ δ' δs}(l : [ δ ]∈D δs)(l' : [ δ' ]∈D δs)
  → DiffDoms l l' ⊎ (∃ λ (δ'=δ : δ' ≡ δ) → l ≡ tr (λ δ → [ δ ]∈D δs) δ'=δ l')
sameDoms? here here = inr ⟨ refl , refl ⟩
sameDoms? here (there l') = inl (h/t l')
sameDoms? (there l) here = inl (t/h l)
sameDoms? (there l) (there l') with sameDoms? l l'
sameDoms? (there l) (there l') | inl x = inl (t/t x)
sameDoms? (there l) (there .l) | inr ⟨ refl , refl ⟩ = inr ⟨ refl , refl ⟩

data Maps {a}(A : Set a) : Doms → Set a where
  · : Maps A ·
  _,[_] : ∀ {δs δ}(I : Maps A δs)(Δ : Map A δ) → Maps A (δs ,[ δ ])

lookup : ∀ {a δs δ}{A : Set a} → Maps A δs → [ δ ]∈D δs → Map A δ
lookup (M ,[ Δ ]) here = Δ
lookup (M ,[ Δ ]) (there l) = lookup M l

pure : ∀ {a}{A : Set a}(δs : Doms)(f : URI → A) → Maps A δs
pure ·           f = ·
pure (δs ,[ δ ]) f = pure δs f ,[ Map.pure δ f ]

constMaps : ∀ {a}{A : Set a}(δs : Doms)(v : A) → Maps A δs
constMaps δs v = pure δs (const v)


_[_≔_] : ∀ {a}{A : Set a}{δ δs}(I : Maps A δs)(l : [ δ ]∈D δs) → (Map A δ → Map A δ) → Maps A δs
· [ () ≔ f ]
(I ,[ Δ ]) [ here ≔ f ] = I ,[ f Δ ]
(I ,[ Δ ]) [ there l ≔ f ] = I [ l ≔ f ] ,[ Δ ]

_[_>>_]≔_ : ∀ {a}{A : Set a}{c δ δs}(I : Maps A δs)(l : [ δ ]∈D δs)(l' : c ∈D δ) → A → Maps A δs
I [ lΔ >> lA ]≔ v = I [ lΔ ≔ (λ Δ → Δ Env.[ lA ]≔' v) ]

lookup-diff : ∀ {a}{A : Set a}{δ δ' δs}(M : Maps A δs)(l : [ δ ]∈D δs)(l' : [ δ' ]∈D δs)(f : Map A δ → Map A δ)
  → DiffDoms l l'
  → lookup (M [ l ≔ f ]) l' ≡ lookup M l'
lookup-diff (M ,[ Δ ]) .here .(there l) f (h/t l) = refl
lookup-diff (M ,[ Δ ]) .(there l) .here f (t/h l) = refl
lookup-diff (M ,[ Δ ]) ._ ._ f (t/t diff) = lookup-diff M _ _ f diff

Proto      = Maps MSession
Selections = Maps 𝟚

sel₀ : (δs : Doms) → Selections δs
sel₁ : (δs : Doms) → Selections δs
sel₀ δs = constMaps δs 0₂
sel₁ δs = constMaps δs 1₂

infix 5 _,[_↦_?] _,[_↦end] _,[_↦_]
_,[_↦_?] : ∀{a}{A : Set a}{δs}(I : Maps A δs)(c : URI)(v : A) → Maps A (δs ,[ ε , c ↦* ])
I ,[ c ↦ v ?] = I ,[ (ε , c ↦ v) ]

_,[_↦_] : ∀{δs}(I : Proto δs)(c : URI)(v : Session) → Proto (δs ,[ ε , c ↦* ])
I ,[ c ↦ v ] = I ,[ c ↦ « v » ?]

_,[_↦end] : ∀{δs}(I : Proto δs)(c : URI) → Proto (δs ,[ ε , c ↦* ])
I ,[ c ↦end] = I ,[ c ↦ end ?]

zipWith : ∀ {δs}(f : ∀ {δ} → Env δ → Sel δ → Env δ) → Proto δs → Selections δs → Proto δs
zipWith f · · = ·
zipWith f (I ,[ Δ ]) (σs ,[ σ ]) = zipWith f I σs ,[ f Δ σ ]

lookup/zipWith : ∀ {δs δE}(f : ∀ {δ} → Env δ → Sel δ → Env δ)(I : Proto δs)(σ : Selections δs)
  (l : [ δE ]∈D δs) → lookup (zipWith f I σ) l ≡ f (lookup I l) (lookup σ l)
lookup/zipWith f (I ,[ Δ ]) (σ ,[ Δ₁ ]) here = refl
lookup/zipWith f (I ,[ Δ ]) (σ ,[ Δ₁ ]) (there l) = lookup/zipWith f I σ l

-- module SelProj = Env.With-end {_} {MSession} end
{-
module SelProj where
    _/₀_ : ∀ {δ} → Env δ → Sel δ → Env δ
    I /₀ ₀ = I
    I /₀ ₁ = Env.map (λ _ → end) I
    I /₀ ₘ σ = I Env./₀ σ

    _/₁_ : ∀ {δ} → Env δ → Sel δ → Env δ
    I /₁ ₀ = Env.map (λ _ → end) I
    I /₁ ₁ = I
    I /₁ ₘ σ = I Env./₁ σ
-}

infixl 6 _[]/[_]_

abstract
    _[]/[_]_ : ∀ {δs}(I : Proto δs)(b : 𝟚)(σs : Selections δs) → Proto δs
    I []/[ b ] σs = zipWith (λ E σ → E /[ b ] σ) I σs

module _ {δs}(I : Proto δs)(σs : Selections δs) where
    infixl 6 _[]/₀_ _[]/₁_
    _[]/₀_ : Proto δs
    _[]/₀_ = I []/[ 0₂ ] σs
    _[]/₁_ : Proto δs
    _[]/₁_ = I []/[ 1₂ ] σs

{-
data SelAtMost (n : ℕ){δ : Dom} : Sel δ → ℕ → Set where
  ₀ : SelAtMost n ₀ n
  ₁ : SelAtMost n ₁ n
  ₘ : ∀ {σ} → SelAtMost n (ₘ σ) (suc n)
-}
data SelAtMost (n : ℕ){δ : Dom}(σ : Sel δ) : ℕ → Set where
  ₀₁ : ∀ b → SelectionAll≡ b σ → SelAtMost n σ n
  ₘ : {-TODO insert relevant negation of SelectionAll≡ b.
        e.g. σ [ c₀ ]= 0₂ and σ [ c₁ ]= 1₂ -}
      SelAtMost n σ (suc n)

data AtMost : ℕ → ∀ {δs} → Selections δs → Set where
  · : ∀ {n} → AtMost n ·
  _,[_] : ∀ {n m δ δs}{I σ} → AtMost n {δs} I → SelAtMost n {δ} σ m → AtMost m (I ,[ σ ])

{-
data ZipP : ℕ → Proto → Proto → Proto → Set₁ where
  · : ∀ {n} → ZipP n · · ·
  _,[_]₀ : ∀ {n}{Δ₀ Δ₁ Δ}(Z : ZipP n Δ Δ₀ Δ₁){δ}(η : Env δ)
           → ZipP n (Δ ,[ η ]) (Δ₀ ,[ η ]) (Δ₁ ,[ ε ])
  _,[_]₁ : ∀ {n}{Δ₀ Δ₁ Δ}(Z : ZipP n Δ Δ₀ Δ₁){δ}(η : Env δ)
           → ZipP n (Δ ,[ η ]) (Δ₀ ,[ ε ]) (Δ₁ ,[ η ])
  _,[_]ₘ : ∀ {n}{Δ₀ Δ₁ Δ}{δ}{η₀ η₁ η : Env δ}
             (Z : ZipP n Δ Δ₀ Δ₁)(Zη : Zip η η₀ η₁)
           → ZipP (suc n) (Δ ,[ η ]) (Δ₀ ,[ η₀ ]) (Δ₁ ,[ η₁ ])

_,[_↦_] : Proto → URI → Session → Proto
Δ ,[ d ↦ P ] = Δ ,[ (ε , d ↦ P) ]
-}

infixr 4 _♦Doms_
_♦Doms_ : Doms → Doms → Doms
Δ ♦Doms · = Δ
Δ ♦Doms (Δ' ,[ η ]) = (Δ ♦Doms Δ') ,[ η ]

infixr 4 _♦Proto_
_♦Proto_ : ∀ {δs δs'} → Proto δs → Proto δs' → Proto (δs ♦Doms δs')
Δ ♦Proto · = Δ
Δ ♦Proto (Δ' ,[ η ]) = (Δ ♦Proto Δ') ,[ η ]

infix 3 [_]∈_

record [_]∈_ {a}{A : Set a}{δ}(Δ : Map A δ){δs}(M : Maps A δs) : Set a where
  constructor ⟨_,_⟩
  field
    lΔ : [ δ ]∈D δs
    ↦Δ : lookup M lΔ ≡ Δ
module []∈ = [_]∈_

pattern ⟨_R[]⟩ l  = ⟨ l         , refl ⟩
pattern heRe[]    = ⟨ hereDs    , refl ⟩
pattern theRe[] p = ⟨ thereDs p , refl ⟩

[]∈♦₀ : ∀ {δ δE δF} → [ δ ]∈D δE → [ δ ]∈D (δE ♦Doms δF)
[]∈♦₀ {δF = ·} l = l
[]∈♦₀ {δF = δF ,[ x ]} l = there ([]∈♦₀ {δF = δF} l)

[]∈♦₁ : ∀ {δ δE δF} → [ δ ]∈D δF → [ δ ]∈D (δE ♦Doms δF)
[]∈♦₁ here = here
[]∈♦₁ (there l) = there ([]∈♦₁ l)

lookup-[]∈♦₀ : ∀ {δ δE δF}(E : Proto δE)(F : Proto δF)(l : [ δ ]∈D δE)
  → lookup (E ♦Proto F) ([]∈♦₀ {δF = δF} l) ≡ lookup E l
lookup-[]∈♦₀ E · l = refl
lookup-[]∈♦₀ E (F ,[ Δ ]) l = lookup-[]∈♦₀ E F l

lookup-[]∈♦₁ : ∀ {δ δE δF}(E : Proto δE)(F : Proto δF)(l : [ δ ]∈D δF)
  → lookup (E ♦Proto F) ([]∈♦₁ {δF = δF} l) ≡ lookup F l
lookup-[]∈♦₁ E (F ,[ Δ ]) here = refl
lookup-[]∈♦₁ E (F ,[ Δ ]) (there l) = lookup-[]∈♦₁ E F l

[]∈♦₀-diff : ∀ {δ δ' δE δF}{l : [ δ ]∈D δE}{l' : [ δ' ]∈D δE} → DiffDoms l l'
  → DiffDoms ([]∈♦₀ {δF = δF} l) ([]∈♦₀ {δF = δF} l')
[]∈♦₀-diff {δF = ·} diff = diff
[]∈♦₀-diff {δF = δF ,[ x ]} diff = t/t ([]∈♦₀-diff {δF = δF} diff)

module _ {δ₀ δE}{I₀ : Proto δ₀}{f : Env δE → Env δE}(l : [ δE ]∈D δ₀)where
  ≔[]∈♦₀ : ∀ {δ₁}(I₁ : Proto δ₁) → (I₀ ♦Proto I₁) [ []∈♦₀ {δF = δ₁} l ≔ f ] ≡ I₀ [ l ≔ f ] ♦Proto I₁
  ≔[]∈♦₀ · = refl
  ≔[]∈♦₀ (I₁ ,[ Δ ]) rewrite ≔[]∈♦₀ I₁ = refl

module _ {δ₀ δE}{I₀ : Proto δ₀}{f : Env δE → Env δE} where
  ≔[]∈♦₁ : ∀ {δ₁}(l : [ δE ]∈D δ₁)(I₁ : Proto δ₁)
    → (I₀ ♦Proto I₁) [ []∈♦₁ {δE = δ₀} l ≔ f ] ≡ I₀ ♦Proto I₁ [ l ≔ f ]
  ≔[]∈♦₁ here (I₁ ,[ Δ ])= refl
  ≔[]∈♦₁ (there l) (I₁ ,[ Δ ]) rewrite ≔[]∈♦₁ l I₁ = refl

infix 0 [_↦_…]∈_ [_↦_]∈_
record [_↦_…]∈_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  constructor mk
  field
    {δE} : Dom
    {E}  : Env δE
    lI   : [ E ]∈ I
    lE   : c Env.↦ « S » ∈ E
  open [_]∈_ lI public
  open Env._↦_∈_ lE public
  E/ : Env δE
  E/ = E Env./' lE
module [↦…]∈ = [_↦_…]∈_
open [↦…]∈ using (E/) public

pattern mk3 a b c = [↦…]∈.mk [_]∈_.⟨ a , b ⟩ c
pattern mk4 a b c d = mk3 a b Env._↦_∈_.⟨ c , d ⟩

-- here…' : ∀ {δJ}{J : Proto δJ}{c S} → [ c ↦ S …]∈ J ,[ c ↦ S ]
pattern here…' = [↦…]∈.mk heRe[] Env.heRe

there…' : ∀ {δE δJ}{E : Env δE}{J : Proto δJ}{c S} →
            [ c ↦ S …]∈ J → [ c ↦ S …]∈ J ,[ E ]
there…' (mk ⟨ l , X ⟩ l') = mk ⟨ there l , X ⟩ l'

unthere…' : ∀ {δE δJ}{J : Proto δJ}{c S}
              {E : Env δE}(EE : Env.Ended E)
            → [ c ↦ S …]∈ J ,[ E ] → [ c ↦ S …]∈ J
unthere…' EE (mk heRe[] lE) = 𝟘-elim (Ended-↦∈ lE EE)
unthere…' EE (mk (theRe[] lΔ) lE) = mk ⟨ lΔ R[]⟩ lE

∼-cancel-unthere… : ∀ {δI}{I : Proto δI}
        {δE}{E : Env δE}(EE : Env.Ended E)
        {c S}(l : [ c ↦ S …]∈ I ,[ E ])
        → [_↦_…]∈_.E l ∼ [_↦_…]∈_.E (unthere…' EE l)
∼-cancel-unthere… EE (mk heRe[] lE) = 𝟘-elim (Ended-↦∈ lE EE)
∼-cancel-unthere… EE (mk (theRe[] lΔ) lE) = ∼-refl

record [_↦_]∈_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  constructor mk
  field
    l…  : [ c ↦ S …]∈ I
  open [↦…]∈ l…
  field
    E/c : Env.Ended (E Env./' lE)
  open [↦…]∈ l… public
module [↦]∈ = [_↦_]∈_

pattern mk5 a b c d e = mk (mk4 a b c d) e
-- here[]' : ∀ {δJ}{J : Proto δJ}{c S} → [ c ↦ S ]∈ J ,[ c ↦ S ]
pattern here[]' = mk here…' _

there[]' : ∀ {δE δJ}{E : Env δE}{J : Proto δJ}{c S} →
            [ c ↦ S ]∈ J → [ c ↦ S ]∈ J ,[ E ]
there[]' (mk l l') = mk (there…' l) l'

infixl 6 _/Ds_
_/Ds_ : ∀ {δ δs}(I : Proto δs)(l : [ δ ]∈D δs) → Proto δs
I /Ds l = I [ l ≔ _/* ]

_/D[_>>_] : ∀ {c δ δs}(I : Proto δs)(l : [ δ ]∈D δs)(l' : c ∈D δ) → Proto δs
I /D[ l >> l' ] = I [ l >> l' ]≔ end

_/_ : ∀ {δ δs}(I : Proto δs){E : Env δ}(l : [ E ]∈ I) → Proto δs
I / l = I /Ds [_]∈_.lΔ l

_[/]_ : ∀ {δs}(I : Proto δs){c S}(l : [ c ↦ S ]∈ I) → Proto δs
I [/] l = I /Ds lΔ
  where open [↦]∈ l

-- nuke everything in the tensor group c is found in
_[/…]_ : ∀ {δs}(I : Proto δs){c S}(l : [ c ↦ S …]∈ I) → Proto δs
I [/…] l = I /Ds lΔ
  where open [↦…]∈ l

-- nuke only one guy
_/…_ : ∀ {δs}(I : Proto δs){c S}(l : [ c ↦ S …]∈ I) → Proto δs
I /… l = I /D[ lΔ >> lA ]
  where open [↦…]∈ l

All : (Pred : ∀ {δ} → Env δ → Set) → ∀ {δs} → Proto δs → Set
All Pred · = 𝟙
All Pred (Δ ,[ E ]) = All Pred Δ × Pred E

All[]∈D : ∀ {Pred : ∀ {δ} → Env δ → Set}{δ δs}{I : Proto δs}
          (l : [ δ ]∈D δs) → All Pred I → Pred (lookup I l)
All[]∈D {I = I ,[ Δ ]} here      X = snd X
All[]∈D {I = I ,[ Δ ]} (there l) X = All[]∈D l (fst X)

All[]∈ : ∀ {Pred : ∀ {δ} → Env δ → Set}{δs δ}{I : Proto δs}{E : Env δ}(l : [ E ]∈ I) → All Pred I → Pred E
All[]∈ ⟨ l R[]⟩ = All[]∈D l

Ended : ∀ {δs} → Proto δs → Set
Ended = All Env.Ended

module _ {a}{A : Set a}{v : A} where
  constMap≡ : ∀ {δ}(E F : Env δ) → Map.map (const v) E ≡ Map.map (const v) F
  constMap≡ ε ε = refl
  constMap≡ (E , c ↦ v₁) (F , .c ↦ v₂) rewrite constMap≡ E F = refl

/Ds>>-red : ∀ {c δ δs x}(I : Proto δs)(lΔ : [ δ ]∈D δs)(lA : c ∈D δ)
  → I [ lΔ >> lA ]≔ x /Ds lΔ ≡ I /Ds lΔ
/Ds>>-red (I ,[ Δ ]) here lA = ap (_,[_] I) (constMap≡ _ _)
/Ds>>-red (I ,[ Δ ]) (there lΔ) lA = ap (λ X → X ,[ Δ ]) (/Ds>>-red I lΔ lA)

D[>>][>>]-red : ∀ {c δ δs x y}(I : Proto δs)(lΔ : [ δ ]∈D δs)(lA : c ∈D δ)
  → (I [ lΔ >> lA ]≔ y) [ lΔ >> lA ]≔ x ≡ I [ lΔ >> lA ]≔ x
D[>>][>>]-red (I ,[ Δ ]) here lA = ap (_,[_] I) (Map.[]≔-red Δ lA)
D[>>][>>]-red (I ,[ Δ ]) (there lΔ) lA = ap₂ _,[_] (D[>>][>>]-red I lΔ lA) refl

module _ {δ δI}{I : Proto δI}(l : [ δ ]∈D δI) where
  /Ds-[]∈♦₀ : ∀ {δK}(K : Proto δK)
     → (I /Ds l) ♦Proto K ≡ (I ♦Proto K) /Ds ([]∈♦₀ {δF = δK} l)
  /Ds-[]∈♦₀ · = refl
  /Ds-[]∈♦₀ (K ,[ Δ ]) rewrite /Ds-[]∈♦₀ K = refl

lookup/D[>>] : ∀ {δI δE c v}(I : Proto δI)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
  → lookup (I [ lΔ >> lA ]≔ v) lΔ ≡ lookup I lΔ Env.[ lA ]≔' v
lookup/D[>>] (I ,[ Δ ]) here lA = refl
lookup/D[>>] (I ,[ Δ ]) (there lΔ) lA = lookup/D[>>] I lΔ lA

D[>>]≔-lookup : ∀ {δI δE c}(I : Proto δI)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
  → I [ lΔ >> lA ]≔ (Env.lookup (lookup I lΔ) lA) ≡ I
D[>>]≔-lookup (I ,[ Δ ]) here lA rewrite Env.[]≔-lookup Δ lA = refl
D[>>]≔-lookup (I ,[ Δ ]) (there lΔ) lA rewrite D[>>]≔-lookup I lΔ lA = refl

infix 0 _⊆s_
record _⊆s_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor mk
  field
    un-⊆s : ∀ {c S} (l : [ c ↦ S …]∈ I)
            → Σ ([ c ↦ S …]∈ J) λ l' → [↦…]∈.E l ∼ [↦…]∈.E l'
open _⊆s_ public

⊆s-there : ∀ {δE δJ}{E : Env δE}{J : Proto δJ} → J ⊆s J ,[ E ]
un-⊆s ⊆s-there l = ⟨ there…' l , ∼-refl ⟩

⊆s-refl : ∀ {δI}{I : Proto δI} → I ⊆s I
un-⊆s ⊆s-refl l = ⟨ l , ∼-refl ⟩

⊆s-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
           → I ⊆s J → J ⊆s K → I ⊆s K
un-⊆s (⊆s-trans (mk p) (mk q)) l =
  let p' = p l
      q' = q (fst p')
  in ⟨ fst q' , snd p' ∼-∙ snd q' ⟩

⊆,[] : ∀ {δF₀ δF₁ δI δJ}{F₀ : Env δF₀}{F₁ : Env δF₁}{I : Proto δI}{J : Proto δJ}
       → I ⊆s J → F₀ ∼ F₁ → I ,[ F₀ ] ⊆s J ,[ F₁ ]
un-⊆s (⊆,[] I⊆J F₀F₁) (mk heRe[] lE)
  =  ⟨ (mk heRe[] (un-⊆ (get-⊆ F₀F₁) id lE)) , F₀F₁ ⟩
un-⊆s (⊆,[] I⊆J F₀F₁) (mk (theRe[] lΔ) lE)
  = ×map there…' id (un-⊆s I⊆J (mk ⟨ lΔ R[]⟩ lE))

⊆,[end] : ∀ {δE δI}{E : Env δE}{I : Proto δI}(EE : Env.Ended E)
        → I ,[ E ] ⊆s I
un-⊆s (⊆,[end] EE) l = ⟨ unthere…' EE l , ∼-cancel-unthere… EE l ⟩

infix 0 _≈_
record _≈_ {δI δJ}(I : Proto δI)(J : Proto δJ) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆s : I ⊆s J
    get-⊇s : J ⊆s I

≈-refl : ∀ {δI}{I : Proto δI} → I ≈ I
≈-refl = ⟨ ⊆s-refl , ⊆s-refl ⟩

≈-reflexive : ∀ {δI}{I J : Proto δI} → I ≡ J → I ≈ J
≈-reflexive refl = ≈-refl

≈-sym : ∀ {δI δJ}{I : Proto δI}{J : Proto δJ}
        → I ≈ J → J ≈ I
≈-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

≈-!_ = ≈-sym

≈-trans : ∀ {δI δJ δK}{I : Proto δI}{J : Proto δJ}{K : Proto δK}
          → I ≈ J → J ≈ K → I ≈ K
≈-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ ⊆s-trans p r , ⊆s-trans s q ⟩

infixr 8 _≈-∙_
_≈-∙_ = ≈-trans

≈,[] : ∀ {δE δF δI δJ}{E : Env δE}{F : Env δF}{I : Proto δI}{J : Proto δJ}
       → I ≈ J → E ∼ F → I ,[ E ] ≈ J ,[ F ]
≈,[] ⟨ I⊆J , J⊆I ⟩ E∼F = ⟨ ⊆,[] I⊆J E∼F , ⊆,[] J⊆I (∼-sym E∼F) ⟩

≈,[end] : ∀ {δE δI}{E : Env δE}{I : Proto δI}(EE : Env.Ended E)
        → I ,[ E ] ≈ I
≈,[end] EE = ⟨ ⊆,[end] EE , ⊆s-there ⟩

⊆,[swap] : ∀ {δE c d A B}{E : Env δE} → E , c ↦ A , d ↦ B ⊆ E , d ↦ B , c ↦ A
un-⊆ ⊆,[swap] NES heRe = theRe here
un-⊆ ⊆,[swap] NES (theRe here) = heRe
un-⊆ ⊆,[swap] NES (theRe (there lA)) = theRe (there lA)

∼,[swap] : ∀ {δE c d A B}{E : Env δE} → E , c ↦ A , d ↦ B ∼ E , d ↦ B , c ↦ A
get-⊆ ∼,[swap] = ⊆,[swap]
get-⊇ ∼,[swap] = ⊆,[swap]

⊆s,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ⊆s I ,[ F ] ,[ E ]
un-⊆s ⊆s,[swap] (mk heRe[] lE) = ⟨ mk (theRe[] here) lE , ∼-refl ⟩
un-⊆s ⊆s,[swap] (mk (theRe[] here) lE) = ⟨ mk heRe[] lE , ∼-refl ⟩
un-⊆s ⊆s,[swap] (mk (theRe[] (there l)) lE) = ⟨ mk (theRe[] (there l)) lE , ∼-refl ⟩

≈,[swap] : ∀ {δE δF δI}{I : Proto δI}{E : Env δE}{F : Env δF} → I ,[ E ] ,[ F ] ≈ I ,[ F ] ,[ E ]
_≈_.get-⊆s ≈,[swap] = ⊆s,[swap]
_≈_.get-⊇s ≈,[swap] = ⊆s,[swap]

♦-assoc : ∀ {δa δb δc}{A : Proto δa}{B : Proto δb}{C : Proto δc} → A ♦Proto (B ♦Proto C) ≈ (A ♦Proto B) ♦Proto C
♦-assoc {C = ·} = ≈-refl
♦-assoc {C = C ,[ Δ ]} = ≈,[] (♦-assoc {C = C}) ∼-refl

♦-com, : ∀ {δa δ δb}{A : Proto δa}{B : Proto δb}{E : Env δ} → (A ,[ E ]) ♦Proto B ≈ (A ♦Proto B),[ E ]
♦-com, {B = ·} = ≈-refl
♦-com, {B = B ,[ Δ ]} = ≈,[] (♦-com, {B = B}) ∼-refl ≈-∙ ≈,[swap]

♦-com· : ∀ {δa}{A : Proto δa} → · ♦Proto A ≈ A
♦-com· {A = ·} = ≈-refl
♦-com· {A = A ,[ Δ ]} = ≈,[] ♦-com· ∼-refl

♦-com : ∀ {δa δb}{A : Proto δa}{B : Proto δb} → (A ♦Proto B) ≈ (B ♦Proto A)
♦-com {A = ·} = ♦-com·
♦-com {A = A ,[ Δ ]}{B} = ♦-com, {B = B} ≈-∙ (≈,[] (♦-com {A = A}) ∼-refl)

/Ds-com : ∀ {δs δ δ'}{I : Proto δs}(l : [ δ ]∈D δs)(l' : [ δ' ]∈D δs)
    → I /Ds l /Ds l' ≈ I /Ds l' /Ds l
/Ds-com here here = ≈-refl
/Ds-com {I = I ,[ Δ ]} here      (there l') = ≈-refl
/Ds-com {I = I ,[ Δ ]} (there l) here       = ≈-refl
/Ds-com {I = I ,[ Δ ]} (there l) (there l') = ≈,[] (/Ds-com {I = I} l l') ∼-refl

∼-/D,↦lookup : ∀ {c δE}{E : Env δE}(l : c ∈D δE)
                 → E ∼ E /D l , c ↦ E ‼ l
∼-/D,↦lookup {E = _ , _ ↦ _} here      = ∼,↦ (∼-! ∼,↦end)
∼-/D,↦lookup {E = _ , _ ↦ _} (there l) = ∼,↦ (∼-/D,↦lookup l) ∼-∙ ∼,[swap]

≈-/…,[…] : ∀ {δI}{I : Proto δI}{c S}(l : [ c ↦ S …]∈ I)
       → I ≈ (I [/…] l ,[ E/ l , c ↦ « S » ])
≈-/…,[…] {I = I ,[ Δ ]} (mk heRe[] ⟨ lA , eq ⟩) rewrite ! eq = ≈,[] (≈-! (≈,[end] (mapAll _ _))) (∼-/D,↦lookup lA)
≈-/…,[…] {I = I ,[ Δ ]} (mk (theRe[] lΔ) lE) = ≈,[] (≈-/…,[…] {I = I} (mk ⟨ lΔ R[]⟩ lE)) ∼-refl ≈-∙ ≈,[swap]

module _ {δI}(b : 𝟚)(σ : Selections δI) where
  Selections♦ : ∀ δK → Selections (δI ♦Doms δK)
  Selections♦ · = σ
  Selections♦ (δK ,[ x ]) = Selections♦ δK ,[ constMap x b ]

  atMost♦ : ∀ {n} δK → AtMost n σ → AtMost n (Selections♦ δK)
  atMost♦ · A = A
  atMost♦ (δK ,[ x ]) A = atMost♦ δK A ,[ (₀₁ b (pureAll x (λ _ → refl))) ]

abstract
    Selections♦/same : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
        → (I ♦Proto K) []/[ b ] (Selections♦ b σ δK) ≈ (I []/[ b ] σ) ♦Proto K
    Selections♦/same {K = ·} b σ = ≈-refl
    Selections♦/same {K = K ,[ Δ ]} b σ = ≈,[] (Selections♦/same {K = K} b σ ) (Selection/[]same Δ b)

    Selections♦/not : ∀ {δI}{δK}{I : Proto δI}{K : Proto δK}(b : 𝟚)(σ : Selections δI)
        → (I ♦Proto K) []/[ b ] (Selections♦ (not b) σ δK) ≈ I []/[ b ] σ
    Selections♦/not {K = ·} b σ = ≈-refl
    Selections♦/not {K = K ,[ Δ ]} b σ = ≈-trans (≈,[end] (Selection/[]not Δ b)) (Selections♦/not {K = K}b σ)

    /[]-/D[>>] : ∀ {c δE δI}(b : 𝟚)(I : Proto δI)(σ : Selections δI)(l : [ δE ]∈D δI)(l' : c ∈D δE)
        → (I /D[ l >> l' ]) []/[ b ] σ ≈ (I []/[ b ] σ) /D[ l >> l' ]
    /[]-/D[>>] b (I ,[ Δ ]) (σ ,[ Δ₁ ]) here l' = ≈,[] ≈-refl (/D/[] Δ l' b Δ₁)
    /[]-/D[>>] b (I ,[ Δ ]) (σ ,[ Δ₁ ]) (there l) l' = ≈,[] (/[]-/D[>>] b I σ l l') ∼-refl

    /Ds-/[] : ∀ {δE δI}(b : 𝟚)(I : Proto δI)(lΔ : [ δE ]∈D δI)(σ : Selections δI)
      → Env.Ended (lookup I lΔ /[ b ] lookup σ lΔ)
      → (I /Ds lΔ) []/[ b ] σ ≈ I []/[ b ] σ
    /Ds-/[] b (I ,[ Δ ]) here (σ ,[ Δ₁ ]) En = ≈,[] ≈-refl (End/[ b ] Δ₁ (/*-End Δ) ∼-End En)
    /Ds-/[] b (I ,[ Δ ]) (there lΔ) (σ ,[ Δ₁ ]) En = ≈,[] (/Ds-/[] b I lΔ σ En) ∼-refl

    select-com : ∀ {c δI δE}{I : Proto δI}(σ : Selections δI)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
        → let b = not (lookup σ lΔ ‼ lA)
        in I []/[ b ] σ ≈ (I /D[ lΔ >> lA ]) []/[ b ] σ
    select-com {I = I ,[ Δ ]} (σ ,[ Δ₁ ]) here lA = ≈,[] ≈-refl (∼-select-com Δ Δ₁ lA)
    select-com {I = I ,[ Δ ]} (σ ,[ Δ₁ ]) (there lΔ) lA = ≈,[] (select-com σ lΔ lA) ∼-refl
-- -}
-- -}
-- -}
-- -}
