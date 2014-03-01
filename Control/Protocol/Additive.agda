{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Data.Product.NP renaming (proj₁ to fst; proj₂ to snd) using (_×_; _,_)
open import Data.Zero using (𝟘)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_]) hiding ([_,_]′)
open import Data.One using (𝟙)
open import Data.LR
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; ap)
open import Function.Extensionality
open import HoTT
open Equivalences

open import Control.Protocol

module Control.Protocol.Additive where

module send/recv-𝟘 (P : 𝟘 → Proto){{_ : FunExt}}{{_ : UA}} where
    P⊤ : Proto
    P⊤ = recvE 𝟘 P

    P0 : Proto
    P0 = sendE 𝟘 P

    P0-empty : ⟦ P0 ⟧ ≡ 𝟘
    P0-empty = ua (equiv fst (λ()) (λ()) (λ { (() , _) }))

    P⊤-uniq : ⟦ P⊤ ⟧ ≡ 𝟙
    P⊤-uniq = Π𝟘-uniq _

open send/recv-𝟘 (λ _ → end) public

_⊕_ : (l r : Proto) → Proto
l ⊕ r = send [L: l R: r ]

_&_ : (l r : Proto) → Proto
l & r = recv [L: l R: r ]

module _ {{_ : FunExt}} {P Q} where
    dual-⊕ : dual (P ⊕ Q) ≡ dual P & dual Q
    dual-⊕ = recv=′ [L: refl R: refl ]

    dual-& : dual (P & Q) ≡ dual P ⊕ dual Q
    dual-& = send=′ [L: refl R: refl ]

module _ {{_ : FunExt}}{{_ : UA}} P Q where
    &-comm : P & Q ≡ Q & P
    &-comm = recv≃ LR!-equiv [L: refl R: refl ]

    ⊕-comm : P ⊕ Q ≡ Q ⊕ P
    ⊕-comm = send≃ LR!-equiv [L: refl R: refl ]

    -- additive mix (left-biased)
    amixL : ⟦ P & Q ⟧ → ⟦ P ⊕ Q ⟧
    amixL pq = (`L , pq `L)

    amixR : ⟦ P & Q ⟧ → ⟦ P ⊕ Q ⟧
    amixR pq = (`R , pq `R)

module _ {P Q R S}(f : ⟦ P ⟧ → ⟦ Q ⟧)(g : ⟦ R ⟧ → ⟦ S ⟧) where
    ⊕-map : ⟦ P ⊕ R ⟧ → ⟦ Q ⊕ S ⟧
    ⊕-map (`L , pr) = `L , f pr
    ⊕-map (`R , pr) = `R , g pr

    &-map : ⟦ P & R ⟧ → ⟦ Q & S ⟧
    &-map p `L = f (p `L)
    &-map p `R = g (p `R)

module _ {P Q} where
    ⊕→⊎ : ⟦ P ⊕ Q ⟧ → ⟦ P ⟧ ⊎ ⟦ Q ⟧
    ⊕→⊎ (`L , p) = inl p
    ⊕→⊎ (`R , q) = inr q

    ⊎→⊕ : ⟦ P ⟧ ⊎ ⟦ Q ⟧ → ⟦ P ⊕ Q ⟧
    ⊎→⊕ = [inl: _,_ `L ,inr: _,_ `R ]

    ⊕≃⊎ : ⟦ P ⊕ Q ⟧ ≃ (⟦ P ⟧ ⊎ ⟦ Q ⟧)
    ⊕≃⊎ = equiv ⊕→⊎ ⊎→⊕ [inl: (λ _ → refl) ,inr: (λ _ → refl) ] ⊎→⊕→⊎
      where
        ⊎→⊕→⊎ : ∀ x → ⊎→⊕ (⊕→⊎ x) ≡ x
        ⊎→⊕→⊎ (`L , _) = refl
        ⊎→⊕→⊎ (`R , _) = refl

    ⊕≡⊎ : {{_ : UA}} → ⟦ P ⊕ Q ⟧ ≡ (⟦ P ⟧ ⊎ ⟦ Q ⟧)
    ⊕≡⊎ = ua ⊕≃⊎

    &→× : ⟦ P & Q ⟧ → ⟦ P ⟧ × ⟦ Q ⟧
    &→× p = p `L , p `R

    ×→& : ⟦ P ⟧ × ⟦ Q ⟧ → ⟦ P & Q ⟧
    ×→& (p , q) `L = p
    ×→& (p , q) `R = q

    &→×→& : ∀ x → &→× (×→& x) ≡ x
    &→×→& (p , q) = refl

    module _ {{_ : FunExt}} where
        ×→&→× : ∀ x → ×→& (&→× x) ≡ x
        ×→&→× p = λ= λ { `L → refl ; `R → refl }

        &≃× : ⟦ P & Q ⟧ ≃ (⟦ P ⟧ × ⟦ Q ⟧)
        &≃× = &→× , record { linv = ×→& ; is-linv = ×→&→× ; rinv = ×→& ; is-rinv = &→×→& }

        &≡× : {{_ : UA}} → ⟦ P & Q ⟧ ≡ (⟦ P ⟧ × ⟦ Q ⟧)
        &≡× = ua &≃×

module _ P {{_ : FunExt}}{{_ : UA}} where
    P⊤-& : ⟦ P⊤ & P ⟧ ≡ ⟦ P ⟧
    P⊤-& = &≡× ∙ ap (flip _×_ ⟦ P ⟧) P⊤-uniq ∙ Σ𝟙-snd

    P0-⊕ : ⟦ P0 ⊕ P ⟧ ≡ ⟦ P ⟧
    P0-⊕ = ⊕≡⊎ ∙ ap (flip _⊎_ ⟦ P ⟧) Σ𝟘-fst ∙ ⊎-comm ∙ ! ⊎𝟘-inl

module _ P Q R {{_ : FunExt}}{{_ : UA}} where
    &-assoc : ⟦ P & (Q & R) ⟧ ≡ ⟦ (P & Q) & R ⟧
    &-assoc = &≡× ∙ (ap (_×_ ⟦ P ⟧) &≡× ∙ ×-assoc ∙ ap (flip _×_ ⟦ R ⟧) (! &≡×)) ∙ ! &≡×

    ⊕-assoc : ⟦ P ⊕ (Q ⊕ R) ⟧ ≡ ⟦ (P ⊕ Q) ⊕ R ⟧
    ⊕-assoc = ⊕≡⊎ ∙ (ap (_⊎_ ⟦ P ⟧) ⊕≡⊎ ∙ ⊎-assoc ∙ ap (flip _⊎_ ⟦ R ⟧) (! ⊕≡⊎)) ∙ ! ⊕≡⊎
