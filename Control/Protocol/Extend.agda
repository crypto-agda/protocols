open import Type
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_]) hiding ([_,_]′)
open import Function
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality

open import Control.Protocol

module Control.Protocol.Extend where

module _ {A : ★} (Aᴾ : A → Proto) where

    extend-send : Proto → Proto
    extend-send end      = end
    extend-send (send P) = send [inl: (λ m → extend-send (P m)) ,inr: Aᴾ ]
    extend-send (recv P) = recv λ m → extend-send (P m)

    extend-recv : Proto → Proto
    extend-recv end      = end
    extend-recv (recv P) = recv [inl: (λ m → extend-recv (P m)) ,inr: Aᴾ ]
    extend-recv (send P) = send λ m → extend-recv (P m)

module _ {A : ★} (Aᴾ : A → Proto){{_ : FunExt}} where

    dual-extend-send : ∀ P → dual (extend-send Aᴾ P) ≡ extend-recv (dual ∘ Aᴾ) (dual P)
    dual-extend-send end      = refl
    dual-extend-send (recv P) = send=′ λ m → dual-extend-send (P m)
    dual-extend-send (send P) = recv=′ [inl: (λ m → dual-extend-send (P m))
                                       ,inr: (λ x → refl) ]
