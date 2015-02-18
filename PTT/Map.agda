open import Function
open import Data.One
open import Data.Two
open import Data.Product using (_×_) renaming (proj₁ to fst; proj₂ to snd; _,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open import PTT.Dom

module PTT.Map where

infixl 4 _,_↦_

{-
data Map {a} (A : Set a) : Set a where
  ε : Map A
  _,_↦_ : (E : Map A) (c : URI) (v : A) → Map A

data MapDom {a} {A : Set a} : (M : Map A) (δ : Dom) → Set a where
  ε     : MapDom ε ε
  _,_↦_ : ∀ {M δ} (MD : MapDom M δ) (c : URI) (v : A) → MapDom (M , c ↦ v) (δ , c)

data _↦_∈_ {a}{A : Set a}(d : URI)(S : A) : Map A → Set₁ where
  here  : ∀ {M} → d ↦ S ∈ (M , d ↦ S)
  there : ∀ {M : Map A} {d' S'}
          → d ↦ S ∈ M
          → d ↦ S ∈ (M , d' ↦ S')
-}

data Map {a} (A : Set a) : Dom → Set a where
  ε     : Map A ε
  _,_↦_ : ∀ {δ} (E : Map A δ) c (v : A) → Map A (δ , c ↦*)

infix 7 _‼_
_‼_ : ∀ {a}{A : Set a}{c δ} → Map A δ → c ∈D δ → A
_‼_ (M , c ↦ v) here = v
_‼_ (M , c₁ ↦ v) (there l) = _‼_ M l

lookup = _‼_

-- middle-ground between above and: Map A δ ≈ ∀ {c} → c ∈ δ → A
record _↦_∈_ {a}{A : Set a}(d : URI)(S : A){δ}(M : Map A δ) : Set a where
  constructor ⟨_,_⟩
  field
    lA : d ∈D δ
    ↦A : M ‼ lA ≡ S
module ↦∈ = _↦_∈_

pattern ⟨_R⟩ p  = ⟨ p       , refl ⟩
pattern heRe    = ⟨ here    R⟩
pattern theRe p = ⟨ there p R⟩

there' : ∀ {a}{A : Set a}{d S δ} {M : Map A δ} {d' S'}
          → d ↦ S ∈ M
          → d ↦ S ∈ (M , d' ↦ S')
there' l = ⟨ there (↦∈.lA l) , ↦∈.↦A l ⟩

module _ {a}{A : Set a}{d} where

  infix 5 _[_]≔'_
  _[_]≔'_ : ∀ {δ} (M : Map A δ) → d ∈D δ → A → Map A δ
  (M , .d ↦ _) [ here    ]≔' v' = M , d ↦ v'
  (M , c ↦  v) [ there l ]≔' v' = M [ l ]≔' v' , c ↦ v

module _ {a} {A : Set a} where
    All : ∀ {δ}(Pred : URI → A → Set) → Map A δ → Set
    All Pred ε = 𝟙
    All Pred (M , d ↦ p) = All Pred M × Pred d p

    All∈D : ∀ {δ}{Pred : URI → A → Set}{c}{M : Map A δ} → All Pred M → (l : c ∈D δ) → Pred c (M ‼ l)
    All∈D {M = M , ._ ↦ _} all here = snd all
    All∈D {M = M ,  _ ↦ _} all (there lA) = All∈D (fst all) lA

    All∈' : ∀ {δ}{Pred : URI → A → Set}{c x}{M : Map A δ} → All Pred M → c ↦ x ∈ M → Pred c x
    All∈' all ⟨ p R⟩ = All∈D all p

infixr 6 _♦Map_
_♦Map_ : ∀ {a}{A : Set a}{D₀ D₁} → Map A D₀ → Map A D₁ → Map A (D₀ ♦Dom D₁)
M ♦Map ε = M
M ♦Map (M' , d ↦ P) = (M ♦Map M') , d ↦ P

pure : ∀ {a}{A : Set a}(δ : Dom)(f : URI → A) → Map A δ
pure ε          f = ε
pure (δ , c ↦*) f = pure δ f , c ↦ f c

constMap : ∀ {a}{A : Set a}(δ : Dom)(v : A) → Map A δ
constMap δ v = pure δ (const v)

pureAll : ∀ {a}{A : Set a}{P : URI → A → Set}{f : URI → A}
            (δ : Dom) (PF : ∀ c → P c (f c)) → All P (pure δ f)
pureAll ε PF = _
pureAll (δ , c ↦*) PF = ⟨ pureAll δ PF , PF c ⟩

map : ∀ {a b} {A : Set a} {B : Set b} {δ}
        (f : A → B) (m : Map A δ) → Map B δ
map f ε = ε
map f (m , c ↦ v) = map f m , c ↦ f v

mapAll : ∀ {a b δ}{A : Set a}{B : Set b}{P : URI → B → Set}{f : A → B}
  (PF : ∀ {c} x → P c (f x))(M : Map A δ) → All P (map f M)
mapAll PF ε = _
mapAll PF (M , c ↦ v) = ⟨ mapAll PF M , PF v ⟩

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {δ}
            (f : A → B → C) (mA : Map A δ) (mB : Map B δ) → Map C δ
zipWith f ε ε = ε
zipWith f (mA , c ↦ v₀) (mB , .c ↦ v₁) = zipWith f mA mB , c ↦ f v₀ v₁

Selection : Dom → Set
Selection = Map 𝟚

SelectionAll≡ : 𝟚 → ∀ {δ} → Selection δ → Set
SelectionAll≡ b = All λ _ → _≡_ b

lookup-∈♦₀ : ∀ {a}{A : Set a}{c δE δF}(E : Map A δE)(F : Map A δF)(l : c ∈D δE)
  → (E ♦Map F) ‼ ∈♦₀ {F = δF} l ≡ E ‼ l
lookup-∈♦₀ E ε l = refl
lookup-∈♦₀ E (F , c₁ ↦ v) l = lookup-∈♦₀ E F l

[∈♦₀]≔' : ∀ {a}{A : Set a}{c δE δF}(E : Map A δE)(F : Map A δF)(lA : c ∈D δE)(v : A)
  → (E ♦Map F) [ ∈♦₀ {F = δF} lA ]≔' v ≡ (E [ lA ]≔' v) ♦Map F
[∈♦₀]≔' E ε l v = refl
[∈♦₀]≔' E (F , c₁ ↦ v) l v₁ rewrite [∈♦₀]≔' E F l v₁ = refl

[]≔-lookup : ∀ {a}{A : Set a}{c δE}(E : Map A δE)(l : c ∈D δE)
  → E [ l ]≔' E ‼ l ≡ E
[]≔-lookup (E , c ↦ v) here = refl
[]≔-lookup (E , c₁ ↦ v) (there l) rewrite []≔-lookup E l = refl

lookup-[]≔ : ∀ {a}{A : Set a}{c δE x}(E : Map A δE)(l : c ∈D δE)
  → (E [ l ]≔' x) ‼ l ≡ x
lookup-[]≔ (E , c ↦ v) here = refl
lookup-[]≔ (E , c₁ ↦ v) (there l) = lookup-[]≔ E l

module _ {a}{A : Set a}{x : A} where
  ≔'-com : ∀ {c d δE}(E : Map A δE)(lA : c ∈D δE)(lB : d ∈D δE)
    → (E [ lA ]≔' x) [ lB ]≔' x ≡ (E [ lB ]≔' x) [ lA ]≔' x
  ≔'-com (E , d ↦ v) here here = refl
  ≔'-com (E , c ↦ v) here (there lB) = refl
  ≔'-com (E , d ↦ v) (there lA) here = refl
  ≔'-com (E , c₁ ↦ v) (there lA) (there lB) rewrite ≔'-com E lA lB = refl


module _ {a}{A : Set a}{x y : A} where
  ≔'≔' : ∀ {d δE}(E : Map A δE)(lA : d ∈D δE)
    → (E [ lA ]≔' x) [ lA ]≔' y ≡ E [ lA ]≔' y
  ≔'≔' (E , c ↦ v) here = refl
  ≔'≔' (E , c ↦ v) (there lA) rewrite ≔'≔' E lA = refl

  []≔-red : ∀ {c δE}(E : Map A δE)(l : c ∈D δE)
    → (E [ l ]≔' y) [ l ]≔' x ≡ E [ l ]≔' x
  []≔-red (E , c ↦ v) here = refl
  []≔-red (E , c₁ ↦ v) (there l) rewrite []≔-red E l = refl
-- -}
-- -}
-- -}
-- -}
-- -}
