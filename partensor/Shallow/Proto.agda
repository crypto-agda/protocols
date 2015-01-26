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

data AtMost : ℕ → ∀ {δs} → Selection δs → Set where
  

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
-}

{-
_,[_↦_] : Proto → URI → Session → Proto
Δ ,[ d ↦ P ] = Δ ,[ (ε , d ↦ P) ]

infixr 4 _♦Proto_
_♦Proto_ : Proto → Proto → Proto
Δ ♦Proto · = Δ
Δ ♦Proto (Δ' ,[ η ]) = (Δ ♦Proto Δ') ,[ η ]

data Point : Proto → Set₁ where
  here  : ∀ {I}   → Point I
  there : ∀ {I δ} {Δ : Env δ} → Point I → Point (I ,[ Δ ])

insert : ∀(P : Proto) → Point P → Proto → Proto
insert Δ           here     Δ' = Δ' ♦Proto Δ
insert (Δ ,[ η ]) (there l) Δ' = insert Δ l Δ' ,[ η ]

data [_]∈_ {δ} (η : Env δ) : Proto → Set₁ where
  here  : ∀ {I}   → [ η ]∈ I ,[ η ]
  there : ∀ {I δ} {Δ : Env δ} → [ η ]∈ I → [ η ]∈ I ,[ Δ ]

_[_≔*_] : ∀{δ}{η : Env δ}(P : Proto) → [ η ]∈ P → Proto → Proto
(Δ ,[ _ ]) [ here    ≔* Δ' ] = Δ' ♦Proto Δ
(Δ ,[ η ]) [ there l ≔* Δ' ] = Δ [ l ≔* Δ' ] ,[ η ]

All : (Pred : ∀ {δ} → Env δ → Set) → Proto → Set
All Pred · = 𝟙
All Pred (Δ ,[ E ]) = All Pred Δ × Pred E

Ended : Proto → Set
Ended = All Env.Ended

{-
[_↦_]∈_ : (d : URI)(S : Session) → Proto → Set₁
[ d ↦ S ]∈ P = [ (ε , d ↦ S) ]∈ P
-- -}
-- -}
-- -}
-- -}
