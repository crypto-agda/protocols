open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Nat.Base
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP

open import partensor.Shallow.Dom
open import partensor.Shallow.Session as Session hiding (Ended)
import partensor.Shallow.Map as Map
open Map using (Map; ε; _,_↦_; _↦_∈_; SelectionAll≡)
open import partensor.Shallow.Env as Env using (Env; _/*; Ended-↦∈)

module partensor.Shallow.Proto where

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

module SelProj = Env.With-end {_} {MSession} end
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

infixl 6 _/[_]_

_/[_]_ : ∀ {δs}(I : Proto δs)(b : 𝟚)(σs : Selections δs) → Proto δs
I /[ b ] σs = zipWith (λ E σ → E SelProj./[ b ] σ) I σs

module _ {δs}(I : Proto δs)(σs : Selections δs) where
        infixl 6 _/₀_ _/₁_
        _/₀_ : Proto δs
        _/₀_ = I /[ 0₂ ] σs --zipWith SelProj._/₀_ I σs
        _/₁_ : Proto δs
        _/₁_ = I /[ 1₂ ] σs --zipWith SelProj._/₁_ I σs

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

lookup-[]∈♦₀ : ∀ {δ δE δF}(E : Proto δE)(F : Proto δF)(l : [ δ ]∈D δE)
  → lookup (E ♦Proto F) ([]∈♦₀ {δF = δF} l) ≡ lookup E l
lookup-[]∈♦₀ E · l = refl
lookup-[]∈♦₀ E (F ,[ Δ ]) l = lookup-[]∈♦₀ E F l

[]∈♦₀-diff : ∀ {δ δ' δE δF}{l : [ δ ]∈D δE}{l' : [ δ' ]∈D δE} → DiffDoms l l'
  → DiffDoms ([]∈♦₀ {δF = δF} l) ([]∈♦₀ {δF = δF} l')
[]∈♦₀-diff {δF = ·} diff = diff
[]∈♦₀-diff {δF = δF ,[ x ]} diff = t/t ([]∈♦₀-diff {δF = δF} diff)

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

record [_↦_]∈_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  constructor mk
  field
    l…  : [ c ↦ S …]∈ I
  open [↦…]∈ l…
  field
    E/c : Env.Ended (E Env./' lE)
  open [↦…]∈ l… public
module [↦]∈ = [_↦_]∈_

-- here[]' : ∀ {δJ}{J : Proto δJ}{c S} → [ c ↦ S ]∈ J ,[ c ↦ S ]
pattern here[]' = mk here…' _

there[]' : ∀ {δE δJ}{E : Env δE}{J : Proto δJ}{c S} →
            [ c ↦ S ]∈ J → [ c ↦ S ]∈ J ,[ E ]
there[]' (mk l l') = mk (there…' l) l'

infixl 6 _/Ds_
_/Ds_ : ∀ {δ δs}(I : Proto δs)(l : [ δ ]∈D δs) → Proto δs
I /Ds l = I [ l ≔ _/* ]

_/D[_>>_] : ∀ {c δ δs}(I : Proto δs)(l : [ δ ]∈D δs)(l' : c ∈D δ) → Proto δs
I /D[ l >> l' ] = I [ l ≔ (λ E → E Env.[ l' ]≔' end) ]

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

/Ds>>-red : ∀ {c δ δs}(I : Proto δs)(lΔ : [ δ ]∈D δs)(lA : c ∈D δ)
  → I /D[ lΔ >> lA ] /Ds lΔ ≡ I /Ds lΔ
/Ds>>-red (I ,[ Δ ]) here lA = ap (_,[_] I) (constMap≡ _ _)
/Ds>>-red (I ,[ Δ ]) (there lΔ) lA = ap (λ X → X ,[ Δ ]) (/Ds>>-red I lΔ lA)

module _ {δ δI}{I : Proto δI}(l : [ δ ]∈D δI) where
  /Ds-[]∈♦₀ : ∀ {δK}(K : Proto δK)
     → (I /Ds l) ♦Proto K ≡ (I ♦Proto K) /Ds ([]∈♦₀ {δF = δK} l)
  /Ds-[]∈♦₀ · = refl
  /Ds-[]∈♦₀ (K ,[ Δ ]) rewrite /Ds-[]∈♦₀ K = refl

lookup/D[>>] : ∀ {δI δE c}(I : Proto δI)(lΔ : [ δE ]∈D δI)(lA : c ∈D δE)
  → lookup (I /D[ lΔ >> lA ]) lΔ ≡ lookup I lΔ Env.[ lA ]≔' end
lookup/D[>>] (I ,[ Δ ]) here lA = refl
lookup/D[>>] (I ,[ Δ ]) (there lΔ) lA = lookup/D[>>] I lΔ lA
-- -}
-- -}
-- -}
-- -}
