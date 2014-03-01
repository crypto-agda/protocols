{-# OPTIONS --without-K #-}
open import Function.NP
open import Data.Product.NP using (Σ; _×_; _,_; first)
open import Data.Two hiding (_≟_)
open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _∙_; refl; ap)
open import Function.Extensionality
open import HoTT
open Equivalences

open import Control.Protocol.Core

module Control.Protocol.Sequence where

_>>=_ : (P : Proto) → (Log P → Proto) → Proto
end     >>= Q = Q _
com q P >>= Q = com q λ m → P m >>= λ ms → Q (m , ms)

_>>_ : Proto → Proto → Proto
P >> Q = P >>= λ _ → Q

replicateᴾ : ℕ → Proto → Proto
replicateᴾ 0       P = end
replicateᴾ (suc n) P = P >> replicateᴾ n P

++Log : ∀ (P : Proto){Q : Log P → Proto} (xs : Log P) → Log (Q xs) → Log (P >>= Q)
++Log end       _        ys = ys
++Log (com q P) (x , xs) ys = x , ++Log (P x) xs ys

module _ {{_ : FunExt}} where
    >>=-right-unit : ∀ P → (P >> end) ≡ P
    >>=-right-unit end       = refl
    >>=-right-unit (com q P) = com= refl refl λ m → >>=-right-unit (P m)

    >>=-assoc : ∀ (P : Proto)(Q : Log P → Proto)(R : Log (P >>= Q) → Proto)
                → P >>= (λ x → Q x >>= (λ y → R (++Log P x y))) ≡ ((P >>= Q) >>= R)
    >>=-assoc end       Q R = refl
    >>=-assoc (com q P) Q R = com= refl refl λ m → >>=-assoc (P m) (λ ms → Q (m , ms)) (λ ms → R (m , ms))

    ap->>= : ∀ P {Q₀ Q₁} → (∀ {log} → ⟦ Q₀ log ⟧ ≡ ⟦ Q₁ log ⟧) → ⟦ P >>= Q₀ ⟧ ≡ ⟦ P >>= Q₁ ⟧
    ap->>= end      Q= = Q=
    ap->>= (send P) Q= = Σ=′ _ λ m → ap->>= (P m) Q=
    ap->>= (recv P) Q= = Π=′ _ λ m → ap->>= (P m) Q=

    dual->> : ∀ P Q → dual (P >> Q) ≡ dual P >> dual Q
    dual->> end        Q = refl
    dual->> (com io P) Q = com= refl refl λ m → dual->> (P m) Q

    {- My coe-ap-fu is lacking...
    dual->>= : ∀ P (Q : Log P → Proto) → dual (P >>= Q) ≡ dual P >>= (dual ∘ Q ∘ coe (dual-Log P))
    dual->>= end Q = refl
    dual->>= (com io P) Q = com= refl refl λ m → dual->>= (P m) (Q ∘ _,_ m) ∙ ap (_>>=_ (dual (P m))) (λ= λ ms → ap (λ x → dual (Q x)) (pair= {!!} {!!}))
    -}

    dual-replicateᴾ : ∀ n P → dual (replicateᴾ n P) ≡ replicateᴾ n (dual P)
    dual-replicateᴾ zero    P = refl
    dual-replicateᴾ (suc n) P = dual->> P (replicateᴾ n P) ∙ ap (_>>_ (dual P)) (dual-replicateᴾ n P)

{- An incremental telecom function which makes processes communicate
   during a matching initial protocol. -}
>>=-telecom : (P : Proto){Q : Log P → Proto}{R : Log P → Proto}
            → ⟦ P >>= Q  ⟧
            → ⟦ P >>= R ⊥⟧
            → Σ (Log P) (λ t → ⟦ Q t ⟧ × ⟦ R t ⊥⟧)
>>=-telecom end      p0       p1       = _ , p0 , p1
>>=-telecom (send P) (m , p0) p1       = first (_,_ m) (>>=-telecom (P m) p0 (p1 m))
>>=-telecom (recv P) p0       (m , p1) = first (_,_ m) (>>=-telecom (P m) (p0 m) p1)

>>-telecom : (P : Proto){Q R : Proto}
           → ⟦ P >> Q  ⟧
           → ⟦ P >> R ⊥⟧
           → Log P × ⟦ Q ⟧ × ⟦ R ⊥⟧
>>-telecom P p q = >>=-telecom P p q
