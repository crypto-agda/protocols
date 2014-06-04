{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP using (Σ; _×_; _,_)
open import Data.One using (𝟙)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; ap; coe; coe!; tr)
open import Function.Extensionality
open import HoTT
open import Data.ShapePolymorphism
open Equivalences
open import Type

open import Control.Protocol.InOut
open import Control.Protocol.End
import Control.Protocol.Core as C
open C using (end;com)

module Control.Protocol.Alternate where

data Proto : InOut → ★₁ where
  end : ∀ {io} → Proto io
  com : (io : InOut){M : ★₀}(P : M → Proto (dualᴵᴼ io)) → Proto io

pattern recv P = com In  P
pattern send P = com Out P

module _ {{_ : FunExt}} where
    com= : ∀ io {M₀ M₁}(M= : M₀ ≡ M₁)
             {P₀ P₁}(P= : ∀ m₀ → P₀ m₀ ≡ P₁ (coe M= m₀))
           → Proto.com io P₀ ≡ com io P₁
    com= io refl P= = ap (com _) (λ= P=)

    module _ io
             {M₀ M₁}(M≃ : M₀ ≃ M₁)
             {P₀ P₁}
             (P= : ∀ m₀ → P₀ m₀ ≡ P₁ (–> M≃ m₀))
             {{_ : UA}} where
        com≃ : com io P₀ ≡ com io P₁
        com≃ = com= io (ua M≃) λ m → P= m ∙ ap P₁ (! coe-β M≃ m)

    send= = com= Out
    send≃ = com≃ Out
    recv= = com= In
    recv≃ = com≃ In
 
    com=′ : ∀ io {M}{P₀ P₁ : M → Proto _}(P= : ∀ m → P₀ m ≡ P₁ m) → com io P₀ ≡ com io P₁
    com=′ io = com= io refl

    send=′ : ∀ {M}{P₀ P₁ : M → Proto _}(P= : ∀ m → P₀ m ≡ P₁ m) → send P₀ ≡ send P₁
    send=′ = send= refl

    recv=′ : ∀ {M}{P₀ P₁ : M → Proto _}(P= : ∀ m → P₀ m ≡ P₁ m) → recv P₀ ≡ recv P₁
    recv=′ = recv= refl

P⟦_⟧ : ∀ {io} → Proto io → C.Proto
P⟦ end      ⟧ = end
P⟦ com io P ⟧ = com io λ m → P⟦ P m ⟧

⟦_⟧ : ∀ {io} → Proto io → ★
⟦ P ⟧ = C.⟦ P⟦ P ⟧ ⟧

dual : ∀ {io} → Proto io → Proto (dualᴵᴼ io)
dual end        = end
dual (com io P) = com (dualᴵᴼ io) λ m → dual (P m)

module _ {io}(P : Proto io) where
    ⟦_⊥⟧ : ★
    ⟦_⊥⟧ = ⟦ dual P ⟧

    Log : ★
    Log = C.⟦ C.source-of P⟦ P ⟧ ⟧

module _ {{_ : FunExt}} where
    P⟦_⊥⟧ : ∀ {io}(P : Proto io) → C.dual P⟦ P ⟧ ≡ P⟦ dual P ⟧
    P⟦ end      ⊥⟧ = refl
    P⟦ com io P ⊥⟧ = C.com= refl refl λ m → P⟦ P m ⊥⟧

    telecom : ∀ {io} (P : Proto io) → ⟦ P ⟧ → ⟦ P ⊥⟧ → Log P
    telecom P t u = C.telecom P⟦ P ⟧ t (tr C.⟦_⟧ (! P⟦ P ⊥⟧) u)

send′ : ★ → Proto In → Proto Out
send′ M P = send λ (_ : M) → P

recv′ : ★ → Proto Out → Proto In
recv′ M P = recv λ (_ : M) → P

module _ {{_ : FunExt}} where
    dual-involutive : ∀ {io} (P : Proto io) → tr Proto (dualᴵᴼ-involutive io) (dual (dual P)) ≡ P
    dual-involutive {In}  end      = refl
    dual-involutive {Out} end      = refl
    dual-involutive       (send P) = com=′ _ λ m → dual-involutive (P m)
    dual-involutive       (recv P) = com=′ _ λ m → dual-involutive (P m)

    {-
    dual-equiv : Is-equiv dual
    dual-equiv = self-inv-is-equiv dual-involutive

    dual-inj : ∀ {P Q} → dual P ≡ dual Q → P ≡ Q
    dual-inj = Is-equiv.injective dual-equiv
    -}
-- -}
-- -}
-- -}
-- -}
