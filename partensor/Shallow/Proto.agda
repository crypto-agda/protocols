open import Function
open import Data.Product hiding (zip)
                         renaming (_,_ to ⟨_,_⟩; proj₁ to fst; proj₂ to snd;
                                   map to ×map)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import partensor.Shallow.Dom
open import partensor.Shallow.Session as Session hiding (Ended)
import partensor.Shallow.Map as Map
open Map using (Map; ε; _,_↦_; _↦_∈_; _↦_∈'_; SelectionAll≡)
open import partensor.Shallow.Env as Env using (Env; _/*; here; there)

module partensor.Shallow.Proto where


Sel = Env.Selection
{-
data Sel (δ : Dom) : Set where
  ₀ ₁ : Sel δ
  ₘ : Env.Selection δ → Sel δ
-}

infixl 3 _,[_]

data Doms  : Set where
  · : Doms
  _,[_] : Doms → Dom → Doms

module Doms' where
    infix 3 [_]∈_
    data [_]∈_ (δ : Dom) : Doms → Set where
      here  : ∀ {δs} → [ δ ]∈ δs ,[ δ ]
      there : ∀ {δs δ'} → [ δ ]∈ δs → [ δ ]∈ δs ,[ δ' ]
open Doms' using (here; there)

data Maps {a}(A : Set a) : Doms → Set a where
  · : Maps A ·
  _,[_] : ∀ {δs δ}(I : Maps A δs)(Δ : Map A δ) → Maps A (δs ,[ δ ])

lookup : ∀ {a δs δ}{A : Set a} → Maps A δs → Doms'.[ δ ]∈ δs → Map A δ
lookup (M ,[ Δ ]) here = Δ
lookup (M ,[ Δ ]) (there l) = lookup M l

pure : ∀ {a}{A : Set a}(δs : Doms)(f : URI → A) → Maps A δs
pure ·           f = ·
pure (δs ,[ δ ]) f = pure δs f ,[ Map.pure δ f ]

constMaps : ∀ {a}{A : Set a}(δs : Doms)(v : A) → Maps A δs
constMaps δs v = pure δs (const v)



Proto      = Maps Session
Selections = Maps 𝟚

sel₀ : (δs : Doms) → Selections δs
sel₁ : (δs : Doms) → Selections δs
sel₀ δs = constMaps δs 0₂
sel₁ δs = constMaps δs 1₂

infix 5 _,[_↦_]
_,[_↦_] : ∀{a}{A : Set a}{δs}(I : Maps A δs)(c : URI)(v : A) → Maps A (δs ,[ ε , c ↦* ])
I ,[ c ↦ v ] = I ,[ (ε , c ↦ v) ]

zipWith : ∀ {δs}(f : ∀ {δ} → Env δ → Sel δ → Env δ) → Proto δs → Selections δs → Proto δs
zipWith f · · = ·
zipWith f (I ,[ Δ ]) (σs ,[ σ ]) = zipWith f I σs ,[ f Δ σ ]

lookup/zipWith : ∀ {δs δE}(f : ∀ {δ} → Env δ → Sel δ → Env δ)(I : Proto δs)(σ : Selections δs)
  (l : Doms'.[ δE ]∈ δs) → lookup (zipWith f I σ) l ≡ f (lookup I l) (lookup σ l)
lookup/zipWith f (I ,[ Δ ]) (σ ,[ Δ₁ ]) here = refl
lookup/zipWith f (I ,[ Δ ]) (σ ,[ Δ₁ ]) (there l) = lookup/zipWith f I σ l

module SelProj = Env.With-end {_} {Session} end
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

{-
data Point : ∀ {δs} → Proto δs → Set₁ where
  here  : ∀ {δs I}   → Point {δs} I
  there : ∀ {δs I δ}{Δ : Env δ} → Point {δs} I → Point (I ,[ Δ ])
-}

infix 3 [_]∈_ [_]∈'_
data [_]∈_ {a}{A : Set a}{δ}(Δ : Map A δ) : ∀ {δs} → Maps A δs → Set a where
  here  : ∀ {δs}{I : Maps A δs} → [ Δ ]∈ I ,[ Δ ]
  there : ∀ {δs δ}{I : Maps A δs}{Δ' : Map A δ} → [ Δ ]∈ I → [ Δ ]∈ I ,[ Δ' ]

record [_]∈'_ {a}{A : Set a}{δ}(Δ : Map A δ){δs}(M : Maps A δs) : Set a where
  constructor mk
  field
    lΔ : Doms'.[ δ ]∈ δs
    ↦Δ : lookup M lΔ ≡ Δ


{-
data Mode : Set where
  ended :
  open  : 

record [_,_↦_]∈_ (m : Mode){δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  field
    δE  : Dom
    E   : Env δE
    lM  : [ E ]∈ I
    lE  : c Env.↦ S ∈ E
    E/c : Env.Ended (E Env./ lE)
module [↦]∈ = [_↦_]∈_

record [_↦_…]∈_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  field
-}

infix 0 [_↦_…]∈_ [_↦_]∈_
record [_↦_…]∈_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  constructor mk
  field
    {δE} : Dom
    {E}  : Env δE
    lI   : [ E ]∈ I
    lE   : c Env.↦ S ∈ E
  E/ : Env δE
  E/ = E Env./ lE
module [↦…]∈ = [_↦_…]∈_
open [↦…]∈ using (E/) public

infix 0 [_↦_…]∈'_ [_↦_]∈'_
record [_↦_…]∈'_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  constructor mk
  field
    {δE} : Dom
    {E}  : Env δE
    lI   : [ E ]∈' I
    lE   : c Env.↦ S ∈' E
  open [_]∈'_ lI public
  open Env._↦_∈'_ lE public
  E/' : Env δE
  E/' = E Env./' lE
module [↦…]∈' = [_↦_…]∈'_
open [↦…]∈' using (E/') public

here… : ∀ {δJ}{J : Proto δJ}{c S} →
          [ c ↦ S …]∈ J ,[ c ↦ S ]
here… = mk here here

here…' : ∀ {δJ}{J : Proto δJ}{c S} →
          [ c ↦ S …]∈' J ,[ c ↦ S ]
here…' = mk (mk here refl) (Map.mk here refl)

there… : ∀ {δE δJ}{E : Env δE}{J : Proto δJ}{c S} →
            [ c ↦ S …]∈ J → [ c ↦ S …]∈ J ,[ E ]
there… (mk l l') = mk (there l) l'

there…' : ∀ {δE δJ}{E : Env δE}{J : Proto δJ}{c S} →
            [ c ↦ S …]∈' J → [ c ↦ S …]∈' J ,[ E ]
there…' (mk (mk l X) l') = mk (mk (there l) X) l'

not-there : ∀ {δE c S}{E : Env δE}
              (NES : ¬(Session.Ended S))
              (EE : Env.Ended E)
            → ¬(c ↦ S ∈ E)
not-there NES EE here = NES (snd EE)
not-there NES EE (there l) = not-there NES (fst EE) l

not-there' : ∀ {δE c S}{E : Env δE}
              (NES : ¬(Session.Ended S))
              (EE : Env.Ended E)
            → ¬(c ↦ S ∈' E)
not-there' {E = E , ._ ↦ ._} NES EE (Map.mk here refl) = NES (snd EE)
not-there' {E = E , c₁ ↦ v} NES EE (Map.mk (there lA) ↦A) = not-there' NES (fst EE) (Map.mk lA ↦A)

unthere… : ∀ {δE δJ}{J : Proto δJ}{c S}(NES : ¬(Session.Ended S))
             {E : Env δE}(EE : Env.Ended E) →
           [ c ↦ S …]∈ J ,[ E ] → [ c ↦ S …]∈ J
unthere… NES EE (mk here lE) = 𝟘-elim (not-there NES EE lE)
unthere… NES EE (mk (there lI) lE) = mk lI lE

unthere…' : ∀ {δE δJ}{J : Proto δJ}{c S}(NES : ¬(Session.Ended S))
             {E : Env δE}(EE : Env.Ended E) →
           [ c ↦ S …]∈' J ,[ E ] → [ c ↦ S …]∈' J
unthere…' NES EE (mk (mk here refl) lE) = 𝟘-elim (not-there' NES EE lE)
unthere…' NES EE (mk (mk (there lΔ) ↦Δ) lE) = mk (mk lΔ ↦Δ) lE

record [_↦_]∈_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  constructor mk
  field
    l…  : [ c ↦ S …]∈ I
  open [↦…]∈ l…
  field
    E/c : Env.Ended (E Env./ lE)
  open [↦…]∈ l… public
module [↦]∈ = [_↦_]∈_

record [_↦_]∈'_ {δs}(c : URI)(S : Session)(I : Proto δs) : Set₁ where
  constructor mk
  field
    l…  : [ c ↦ S …]∈' I
  open [↦…]∈' l…
  field
    E/c : Env.Ended (E Env./' lE)
  open [↦…]∈' l… public
module [↦]∈' = [_↦_]∈'_

here[] : ∀ {δJ}{J : Proto δJ}{c S} →
         [ c ↦ S ]∈ J ,[ c ↦ S ]
here[] = mk here… _

here[]' : ∀ {δJ}{J : Proto δJ}{c S} →
         [ c ↦ S ]∈' J ,[ c ↦ S ]
here[]' = mk here…' _

there[] : ∀ {δE δJ}{E : Env δE}{J : Proto δJ}{c S} →
            [ c ↦ S ]∈ J → [ c ↦ S ]∈ J ,[ E ]
there[] (mk l l') = mk (there… l) l'

there[]' : ∀ {δE δJ}{E : Env δE}{J : Proto δJ}{c S} →
            [ c ↦ S ]∈' J → [ c ↦ S ]∈' J ,[ E ]
there[]' (mk l l') = mk (there…' l) l'

{-
module DomsFun where
  insert : (δs : Doms){P : Proto δs} → Point P → Doms → Doms
  insert δs here δs' = δs' ♦Doms δs
  insert (δs ,[ η ]) (there l) δs' = insert δs l δs' ,[ η ]

  _[_≔*_] : ∀ (δs : Doms){I : Proto δs}{δ}{η : Env δ} → [ η ]∈ I → Doms → Doms
  (δs ,[ _ ]) [ here ≔* δs' ] = δs' ♦Doms δs
  (δs ,[ η ]) [ there l ≔* δs' ] = δs [ l ≔* δs' ] ,[ η ]

insert : ∀{δs δs'}(P : Proto δs)(p : Point P) → Proto δs' → Proto (DomsFun.insert δs p δs')
insert Δ           here     Δ' = Δ' ♦Proto Δ
insert (Δ ,[ η ]) (there l) Δ' = insert Δ l Δ' ,[ η ]

_[_≔*_] : ∀{δ δs δs'}{η : Env δ}(P : Proto δs)(l : [ η ]∈ P) → Proto δs' → Proto (δs DomsFun.[ l ≔* δs' ])
(Δ ,[ _ ]) [ here    ≔* Δ' ] =  Δ' ♦Proto Δ
(Δ ,[ η ]) [ there l ≔* Δ' ] = Δ [ l ≔* Δ' ] ,[ η ]

_/_ : ∀ {δ δs}{η : Env δ}(I : Proto δs) → (l : [ η ]∈ I) → Proto (δs DomsFun.[ l ≔* · ])
Δ / l = Δ [ l ≔* · ]
-}

{-
infixl 6 _/_
_/_ : ∀ {δ δs}{Δ : Env δ}(I : Proto δs) → (l : [ Δ ]∈ I) → Proto δs
(I ,[ Δ ]) / here    = I ,[ Δ /* ]
(I ,[ Δ ]) / there l = I / l ,[ Δ ]
-}

forget : ∀ {δ δs}{Δ : Env δ}{I : Proto δs}(l : [ Δ ]∈ I) → Doms'.[ δ ]∈ δs
forget here = here
forget (there l) = there (forget l)

infixl 6 _/Ds_
_/Ds_ : ∀ {δ δs}(I : Proto δs)(l : Doms'.[ δ ]∈ δs) → Proto δs
(I ,[ Δ ]) /Ds here    = I ,[ Δ /* ]
(I ,[ Δ ]) /Ds there l = I /Ds l ,[ Δ ]

_/_ : ∀ {δ δs}(I : Proto δs){E : Env δ}(l : [ E ]∈ I) → Proto δs
I / l = I /Ds forget l

_/'_ : ∀ {δ δs}(I : Proto δs){E : Env δ}(l : [ E ]∈' I) → Proto δs
I /' l = I /Ds [_]∈'_.lΔ l

_[/]_ : ∀ {δs}(I : Proto δs){c S}(l : [ c ↦ S ]∈ I) → Proto δs
I [/] l = I / lI
  where open [↦]∈ l

_[/]'_ : ∀ {δs}(I : Proto δs){c S}(l : [ c ↦ S ]∈' I) → Proto δs
I [/]' l = I /Ds lΔ
  where open [↦]∈' l

-- nuke everything in the tensor group c is found in
_[/…]_ : ∀ {δs}(I : Proto δs){c S}(l : [ c ↦ S …]∈ I) → Proto δs
I [/…] l = I / lI
  where open [↦…]∈ l

-- nuke everything in the tensor group c is found in
_[/…]'_ : ∀ {δs}(I : Proto δs){c S}(l : [ c ↦ S …]∈' I) → Proto δs
I [/…]' l = I /Ds lΔ
  where open [↦…]∈' l

All : (Pred : ∀ {δ} → Env δ → Set) → ∀ {δs} → Proto δs → Set
All Pred · = 𝟙
All Pred (Δ ,[ E ]) = All Pred Δ × Pred E

All∈ : ∀ {Pred : ∀ {δ} → Env δ → Set}{δs δ}{I : Proto δs}{E : Env δ} → All Pred I → [ E ]∈ I → Pred E
All∈ ⟨ APE , PE ⟩ here = PE
All∈ ⟨ APE , PE ⟩ (there l) = All∈ APE l

All∈' : ∀ {Pred : ∀ {δ} → Env δ → Set}{δs δ}{I : Proto δs}{E : Env δ} → All Pred I → [ E ]∈' I → Pred E
All∈' {I = I ,[ Δ ]} X (mk here refl) = snd X
All∈' {I = I ,[ Δ ]} X (mk (there lΔ) ↦Δ) = All∈' (fst X) (mk lΔ ↦Δ)

Ended : ∀ {δs} → Proto δs → Set
Ended = All Env.Ended
-- -}
-- -}
-- -}
-- -}
