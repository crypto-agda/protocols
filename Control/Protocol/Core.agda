{-# OPTIONS --without-K #-}
open import Universe.NP
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP using (Σ; _×_; _,_)
open import Data.Zero using (𝟘)
open import Data.One using (𝟙)
open import Data.Two using (𝟚; 0₂; 1₂)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; ap; coe; coe!; tr)
open import Function.Extensionality
open import HoTT
open import Data.ShapePolymorphism
open import Control.Protocol.InOut
open import Control.Protocol.End public
open Equivalences
import Control.Protocol.Universal

module Control.Protocol.Core where

module _ {ℓ} where
    open Control.Protocol.Universal {ₛ ℓ} {ℓ} (universe id) public

    data Proto☐ : Proto → ★_(ₛ (ₛ ℓ)) where
      end☐ : Proto☐ end
      com☐ : ∀ io {M P} (P☐ : ∀ (m : ☐ M) → Proto☐ (P m)) → Proto☐ (com io P)

    recv☐ : {M : ★_ ℓ}(P : ..(_ : M) → Proto) → Proto
    recv☐ P = recv (λ { [ m ] → P m })

    send☐ : {M : ★_ ℓ}(P : ..(_ : M) → Proto) → Proto
    send☐ P = send (λ { [ m ] → P m })

Proto_ : (ℓ : Level) → ★_(ₛ (ₛ ℓ))
Proto_ ℓ = (Proto) {ℓ}

Proto₀ = Proto_ ₀
Proto₁ = Proto_ ₁

✓ᴾ : 𝟚 → Proto
✓ᴾ 0₂ = send′ 𝟘 end
✓ᴾ 1₂ = end

module _ {io₀ io₁}(io= : io₀ ≡ io₁)
         {M₀ M₁ : ★}(M≃ : M₀ ≃ M₁)
         {P₀ : M₀ → Proto}{P₁ : M₁ → Proto}
         (P= : ∀ m₀ → P₀ m₀ ≡ P₁ (–> M≃ m₀))
         {{_ : UA}} {{_ : FunExt}}
         where
    com≃ : com io₀ P₀ ≡ com io₁ P₁
    com≃ = com=' io= (ua M≃) λ m → P= m ∙ ap P₁ (! coe-β M≃ m)
      where
        com=' : ∀ {io₀ io₁}(io= : io₀ ≡ io₁)
                  {M₀ M₁ : ★}(M= : M₀ ≡ M₁)
                  {P₀ P₁}(P= : (m₀ : M₀) → P₀ m₀ ≡ P₁ (coe M= m₀))
                → com io₀ P₀ ≡ com io₁ P₁
        com=' refl refl P= = ap (com _) (λ= P=)

send≃ = com≃ {Out} refl
recv≃ = com≃ {In} refl

module _ {ℓ} io {M N : ★_ ℓ}(P : M × N → Proto) where
    com₂ : Proto
    com₂ = com io λ m → com io λ n → P (m , n)

-- -}
-- -}
-- -}
-- -}
-- -}
