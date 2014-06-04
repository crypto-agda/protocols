{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP using (Σ; _×_; _,_)
open import Data.One using (𝟙)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; ap; coe; coe!)
open import Function.Extensionality
open import HoTT
open import Data.ShapePolymorphism
open Equivalences
open import Type

module Control.Protocol.InOut where

data InOut : ★ where
  In Out : InOut

dualᴵᴼ : InOut → InOut
dualᴵᴼ In  = Out
dualᴵᴼ Out = In

dualᴵᴼ-involutive : ∀ io → dualᴵᴼ (dualᴵᴼ io) ≡ io
dualᴵᴼ-involutive In = refl
dualᴵᴼ-involutive Out = refl

dualᴵᴼ-equiv : Is-equiv dualᴵᴼ
dualᴵᴼ-equiv = self-inv-is-equiv _ dualᴵᴼ-involutive

dualᴵᴼ-inj : ∀ {x y} → dualᴵᴼ x ≡ dualᴵᴼ y → x ≡ y
dualᴵᴼ-inj = Is-equiv.injective dualᴵᴼ-equiv

⟦_⟧ᴵᴼ : InOut → ∀{ℓ}(M : ★_ ℓ)(P : M → ★_ ℓ) → ★_ ℓ
⟦_⟧ᴵᴼ In  = Π
⟦_⟧ᴵᴼ Out = Σ
