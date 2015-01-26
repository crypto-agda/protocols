open import Data.One
open import Data.Two
open import Data.Product using (_×_)
open import partensor.Shallow.Dom

module partensor.Shallow.Map where

infixl 4 _,_↦_

data Map {a} (A : Set a) : Dom → Set a where
  ε     : Map A ε
  _,_↦_ : ∀ {δ} (E : Map A δ) c (v : A) → Map A (δ , c)

data _↦_∈_ {a}{A : Set a}(d : URI)(S : A) : ∀ {δ} → Map A δ → Set₁ where
  here  : ∀ {δ} {M : Map A δ} → d ↦ S ∈ (M , d ↦ S)
  there : ∀ {δ} {M : Map A δ} {d' S'}
          → d ↦ S ∈ M
          → d ↦ S ∈ (M , d' ↦ S')

module _ {a}{A : Set a}{d v} where
  _[_]≔_ : ∀ {δ} (M : Map A δ) → d ↦ v ∈ M → A → Map A δ
  ._ [ here  {M = M}         ]≔ v' = M , d ↦ v'
  ._ [ there {d' = d'}{S'} l ]≔ v' = _ [ l ]≔ v' , d' ↦ S'

All : ∀ {a}{A : Set a}{δ}(Pred : URI → A → Set) → Map A δ → Set
All Pred ε = 𝟙
All Pred (M , d ↦ p) = All Pred M × Pred d p

infixr 4 _♦Map_
_♦Map_ : ∀ {a}{A : Set a}{D₀ D₁} → Map A D₀ → Map A D₁ → Map A (D₀ ♦Dom D₁)
M ♦Map ε = M
M ♦Map (M' , d ↦ P) = (M ♦Map M') , d ↦ P

map : ∀ {a b} {A : Set a} {B : Set b} {δ}
        (f : A → B) (m : Map A δ) → Map B δ
map f ε = ε
map f (m , c ↦ v) = map f m , c ↦ f v

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {δ}
            (f : A → B → C) (mA : Map A δ) (mB : Map B δ) → Map C δ
zipWith f ε ε = ε
zipWith f (mA , c ↦ v₀) (mB , .c ↦ v₁) = zipWith f mA mB , c ↦ f v₀ v₁

Selection : Dom → Set
Selection = Map 𝟚

module With-end {a}{A : Set a}(end : A) where
    T = Map A

    module _ {δ}(Δ : T δ)(σ : Selection δ) where
        _/₀_ : T δ
        _/₀_ = zipWith (λ v → [0: v 1: end ]) Δ σ

        _/₁_ : T δ
        _/₁_ = zipWith (λ v → [0: end 1: v ]) Δ σ

    data Zip : ∀ {δ} → T δ → T δ → T δ → Set₁ where
      ε : Zip ε ε ε
      _,_↦₀_ : ∀ {δ Δ₀ Δ₁} {Δ : T δ}(Z : Zip Δ Δ₀ Δ₁) d S → Zip (Δ , d ↦ S) (Δ₀ , d ↦ S)   (Δ₁ , d ↦ end)
      _,_↦₁_ : ∀ {δ Δ₀ Δ₁} {Δ : T δ}(Z : Zip Δ Δ₀ Δ₁) d S → Zip (Δ , d ↦ S) (Δ₀ , d ↦ end) (Δ₁ , d ↦ S)

    [_is_⋎_] : ∀ {δ} → T δ → T δ → T δ → Set₁
    [_is_⋎_] = Zip
