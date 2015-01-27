open import Data.Product
open import Data.Zero
open import Data.One
open import Data.Nat

open import partensor.Shallow.Dom
open import partensor.Shallow.Session hiding (Ended)
open import partensor.Shallow.Env as Env using (Env)

module partensor.Shallow.Proto where

data Sel (δ : Dom) : Set where
  ₀ ₁ : Sel δ
  ₘ : Env.Selection δ → Sel δ

infixl 4 _,[_]

data Doms  : Set where
  · : Doms
  _,[_] : Doms → Dom → Doms

data Proto : Doms → Set₁ where
  · : Proto ·
  _,[_] : ∀ {δs δ}(I : Proto δs)(Δ : Env δ) → Proto (δs ,[ δ ])

data Selection : Doms → Set where
  · : Selection ·
  _,[_] : ∀ {δs δ}(I : Selection δs)(σ : Sel δ) → Selection (δs ,[ δ ])

zipWith : ∀ {δs} (f : ∀ {δ} → Env δ → Sel δ → Env δ) → Proto δs → Selection δs → Proto δs
zipWith f · · = ·
zipWith f (I ,[ Δ ]) (σs ,[ σ ]) = zipWith f I σs ,[ f Δ σ ]

module SelProj where
    _/₀_ : ∀ {δ} → Env δ → Sel δ → Env δ
    I /₀ ₀ = I
    I /₀ ₁ = Env.map (λ _ → end) I
    I /₀ ₘ σ = I Env./₀ σ

    _/₁_ : ∀ {δ} → Env δ → Sel δ → Env δ
    I /₁ ₀ = Env.map (λ _ → end) I
    I /₁ ₁ = I
    I /₁ ₘ σ = I Env./₁ σ

module _ {δs} (I : Proto δs) (σs : Selection δs) where
        _/₀_ : Proto δs
        _/₀_ = zipWith SelProj._/₀_ I σs
        _/₁_ : Proto δs
        _/₁_ = zipWith SelProj._/₁_ I σs

data SelAtMost (n : ℕ){δ : Dom} : Sel δ → ℕ → Set where
  ₀ : SelAtMost n ₀ n
  ₁ : SelAtMost n ₁ n
  ₘ : ∀ {σ} → SelAtMost n (ₘ σ) (suc n)

data AtMost : ℕ → ∀ {δs} → Selection δs → Set where
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

data Point : ∀ {δs} → Proto δs → Set₁ where
  here  : ∀ {δs I}   → Point {δs} I
  there : ∀ {δs I δ} {Δ : Env δ} → Point {δs} I → Point (I ,[ Δ ])

infix 4 [_]∈_

data [_]∈_ {δ} (η : Env δ) : ∀ {δs} → Proto δs → Set₁ where
  here  : ∀ {δs}{I : Proto δs}   → [ η ]∈ I ,[ η ]
  there : ∀ {δs δ}{I : Proto δs} {Δ : Env δ} → [ η ]∈ I → [ η ]∈ I ,[ Δ ]

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

All : (Pred : ∀ {δ} → Env δ → Set) → ∀ {δs} → Proto δs → Set
All Pred · = 𝟙
All Pred (Δ ,[ E ]) = All Pred Δ × Pred E

Ended : ∀ {δs} → Proto δs → Set
Ended = All Env.Ended

[_↦_]∈_ : ∀{δs}(d : URI)(S : Session) → Proto δs → Set₁
[ d ↦ S ]∈ P = [ Env.ε Env., d ↦ S ]∈ P
-- -}
-- -}
-- -}
-- -}
