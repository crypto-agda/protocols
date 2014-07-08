module _ where

-- open import Level.NP

-- open import Function.NP
id : ∀ {a} {A : Set a} (x : A) → A
id x = x

infixr 9 _∘_
_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

infixr 0 _$_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

_$′_ : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → (A → B)
f $′ x = f x

-- open import Data.One
record 𝟙 : Set₀ where
  constructor <>
open 𝟙

data Bool : Set where
  true false : Bool

[true:_,false:_] : ∀ {c} {C : Bool → Set c} →
        C true → C false →
        ((x : Bool) → C x)
[true: f ,false: g ] true  = f
[true: f ,false: g ] false = g

data LR : Set where L R : LR

[L:_,R:_] : ∀ {c}{C : LR → Set c} →
  C L → C R → (x : LR) → C x
[L: f ,R: g ] L = f
[L: f ,R: g ] R = g

-- open import Data.Product.NP
record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

-- open import Data.Sum.NP
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

[inl:_,inr:_] : ∀ {c} {A B : Set} {C : A ⊎ B → Set c} →
        ((x : A) → C (inl x)) → ((x : B) → C (inr x)) →
        ((x : A ⊎ B) → C x)
[inl: f ,inr: g ] (inl x) = f x
[inl: f ,inr: g ] (inr y) = g y

-- open import Data.List using (List; []; _∷_)
infixr 5 _∷_

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

[_] : ∀ {a}{A : Set a} → A → List A
[ x ] = x ∷ []

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

module _ {A : Set} (_≤_ : A → A → Bool) where

    merge-sort-list : (l₀ l₁ : List A) → List A
    merge-sort-list [] l₁ = l₁
    merge-sort-list l₀ [] = l₀
    merge-sort-list (x₀ ∷ l₀) (x₁ ∷ l₁) with x₀ ≤ x₁
    ... | true  = x₀ ∷ merge-sort-list l₀ (x₁ ∷ l₁)
    ... | false = x₁ ∷ merge-sort-list (x₀ ∷ l₀) l₁

-- open import Relation.Binary.PropositionalEquality
data _≡_ {a}{A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

ap : ∀{a b}{A : Set a}{B : Set b} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
ap f refl = refl

sym : ∀{a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : ∀{a p}{A : Set a}(P : A → Set p){x y : A} → x ≡ y → P x → P y
subst P refl px = px

postulate
  String : Set
  Char   : Set

{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR   Char #-}

data Error (A : Set) : Set where
  succeed : A → Error A
  fail    : (err : String) → Error A

[succeed:_,fail:_] : ∀ {c} {A : Set} {C : Error A → Set c} →
        ((x : A) → C (succeed x)) → ((x : String) → C (fail x)) →
        ((x : Error A) → C x)
[succeed: f ,fail: g ] (succeed x) = f x
[succeed: f ,fail: g ] (fail y) = g y

mapE : {A B : Set} → (A → B) → Error A → Error B
mapE f (fail err) = fail err
mapE f (succeed x) = succeed (f x)

data All {A : Set} (P : A → Set) : Error A → Set where
  fail    : ∀ s → All P (fail s)
  succeed : ∀ {x} → P x → All P (succeed x)

record _≃?_ (A B : Set) : Set where
  field
    serialize : A → B
    parse     : B → Error A
    linv      : ∀ x → All (_≡_ x ∘ serialize) (parse x)
    rinv      : ∀ x → parse (serialize x) ≡ succeed x
open _≃?_ {{...}} public

{-
open import Category.Profunctor

Prism : (S T A B : Set) → Set₁
Prism S T A B = ∀ {_↝_}{{_ : Choice {₀} _↝_}} → (A ↝ B) → (S ↝ T)

Prism' : (S A : Set) → Set₁
Prism' S A = Prism S S A A

module _ {S T A B : Set} where
    prism : (B → T) → (S → T ⊎ A) → Prism S T A B
    prism bt sta = dimap sta [inl: id ,inr: bt ] ∘ right
      where open Choice {{...}}
-}

Prism : (S T A B : Set) → Set
Prism S T A B = (B → T) × (S → T ⊎ A)

Prism' : (S A : Set) → Set
Prism' S A = Prism S S A A

module _ {S T A B : Set} where
    prism : (B → T) → (S → T ⊎ A) → Prism S T A B
    prism = _,_

    -- This is particular case of lens' _#_
    _#_ : Prism S T A B → B → T
    _#_ = fst

    -- This is particular case of lens' review
    review = _#_

    -- _^._ : Prism S T A B → S → ...

module _ {S A : Set} where
    prism' : (A → S) → (S → S ⊎ A) → Prism' S A
    prism' = prism

module _ {a b}{A : Set a}{B : A → Set b} where
  case_of_ : (x : A) → ((y : A) → B y) → B x
  case x of f = f x

module _ {a b}{A : Set a}{B : Set b} where
  case_of′_ : A → (A → B) → B
  case_of′_ = case_of_

… : {A : Set}{{x : A}} → A
… {{x}} = x
