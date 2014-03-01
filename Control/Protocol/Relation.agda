{-# OPTIONS --without-K #-}
open import Type
open import Function.NP
open import Data.Product.NP renaming (proj₁ to fst; proj₂ to snd) using (Σ;_,_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Control.Protocol.Core

module Control.Protocol.Relation where

ℛ⟦_⟧ : ∀{ℓ}(P : Proto_ ℓ) (p q : ⟦ P ⟧) → ★_ ℓ
ℛ⟦ end    ⟧ p q = End
ℛ⟦ recv P ⟧ p q = ∀ m → ℛ⟦ P m ⟧ (p m) (q m)
ℛ⟦ send P ⟧ p q = Σ (fst p ≡ fst q) λ e → ℛ⟦ P (fst q) ⟧ (subst (⟦_⟧ ∘ P) e (snd p)) (snd q)

ℛ⟦_⟧-refl : ∀ {ℓ}(P : Proto_ ℓ) → Reflexive ℛ⟦ P ⟧
ℛ⟦ end    ⟧-refl     = end
ℛ⟦ recv P ⟧-refl     = λ m → ℛ⟦ P m ⟧-refl
ℛ⟦ send P ⟧-refl {x} = refl , ℛ⟦ P (fst x) ⟧-refl

ℛ⟦_⟧-sym : ∀ {ℓ}(P : Proto_ ℓ) → Symmetric ℛ⟦ P ⟧
ℛ⟦ end    ⟧-sym p          = end
ℛ⟦ recv P ⟧-sym p          = λ m → ℛ⟦ P m ⟧-sym (p m)
ℛ⟦ send P ⟧-sym (refl , q) = refl , ℛ⟦ P _ ⟧-sym q    -- TODO HoTT

ℛ⟦_⟧-trans : ∀ {ℓ}(P : Proto_ ℓ) → Transitive ℛ⟦ P ⟧
ℛ⟦ end    ⟧-trans p          q          = end
ℛ⟦ recv P ⟧-trans p          q          = λ m → ℛ⟦ P m ⟧-trans (p m) (q m)
ℛ⟦ send P ⟧-trans (refl , p) (refl , q) = refl , ℛ⟦ P _ ⟧-trans p q    -- TODO HoTT
