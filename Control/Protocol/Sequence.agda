{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Type.Identities
open import Data.Product.NP using (Σ; _×_; _,_; first)
open import Data.Two hiding (_≟_)
open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; _∙_; refl; ap; coe; coe!; !_; tr)
open import Function.Extensionality
open import HoTT
open Equivalences

open import Control.Protocol.Core

module Control.Protocol.Sequence where

infixl 1 _>>=_ _>>_

_>>=_ : (P : Proto) → (Log P → Proto) → Proto
end     >>= Q = Q _
com q P >>= Q = com q λ m → P m >>= λ ms → Q (m , ms)

_>>_ : Proto → Proto → Proto
P >> Q = P >>= λ _ → Q

>>=-fst : ∀ P {Q} → ⟦ P >>= Q ⟧ → ⟦ P ⟧
>>=-fst end q = end
>>=-fst (recv P) pq = λ m → >>=-fst (P m) (pq m)
>>=-fst (send P) (m , pq) = m , >>=-fst (P m) pq

>>=-snd : ∀ P {Q}(pq : ⟦ P >>= Q ⟧)(p : ⟦ P ⊥⟧) → ⟦ Q (telecom P (>>=-fst P pq) p) ⟧
>>=-snd end      q        end     = q
>>=-snd (recv P) pq       (m , p) = >>=-snd (P m) (pq m) p
>>=-snd (send P) (m , pq) p       = >>=-snd (P m) pq (p m)

[_]_>>>=_ : ∀ P {Q} → ⟦ P ⟧ → ((log : Log P) → ⟦ Q log ⟧) → ⟦ P >>= Q ⟧
[ end    ] p       >>>= q = q _
[ recv P ] p       >>>= q = λ m → [ P m ] p m >>>= λ log → q (m , log)
[ send P ] (m , p) >>>= q = m , [ P m ] p >>>= λ log → q (m , log)

[_]_>>>_ : ∀ P {Q} → ⟦ P ⟧ → ⟦ Q ⟧ → ⟦ P >> Q ⟧
[ P ] p >>> q = [ P ] p >>>= λ _ → q

module _ {{_ : FunExt}} where
    >>=-fst-inv : ∀ P {Q}(p : ⟦ P ⟧)(q : ((log : Log P) → ⟦ Q log ⟧)) → >>=-fst P {Q} ([ P ] p >>>= q) ≡ p
    >>=-fst-inv end      end     q = refl
    >>=-fst-inv (recv P) p       q = λ= λ m → >>=-fst-inv (P m) (p m) λ log → q (m , log)
    >>=-fst-inv (send P) (m , p) q = snd= (>>=-fst-inv (P m) p λ log → q (m , log))

    {-
    >>=-snd-inv : ∀ P {Q}(p : ⟦ P ⟧)(q : ((log : Log P) → ⟦ Q log ⟧))(p' : ⟦ P ⊥⟧)
                  → tr (λ x → ⟦ Q (telecom P x p') ⟧) (>>=-fst-inv P p q)
                       (>>=-snd P {Q} ([ P ] p >>>= q) p') ≡ q (telecom P p p')
    >>=-snd-inv end          end     q p' = refl
    >>=-snd-inv (recv P) {Q} p       q (m , p') = {!ap (flip _$_ (>>=-snd (P m) ([ P m ] p m >>>= (λ log → q (m , log))) p'))
                                                     {!(tr-λ= (λ z → ⟦ Q (m , telecom (P m) z p') ⟧)
                                                               {!(λ m → >>=-fst-inv (P m) (p m) (q ∘ _,_ m))!})!}
                                                !} ∙ >>=-snd-inv (P m) {Q ∘ _,_ m} (p m) (λ log → q (m , log)) p'
    >>=-snd-inv (send P) {Q} (m , p) q p' = tr-snd= (λ { (m , p) → ⟦ Q (m , telecom (P m) p (p' m)) ⟧ })
                                                    (>>=-fst-inv (P m) p (q ∘ _,_ m))
                                                    (>>=-snd (P m) {Q ∘ _,_ m} ([ P m ] p >>>= (q ∘ _,_ m)) (p' m))
                                          ∙ >>=-snd-inv (P m) {Q ∘ _,_ m} p (λ log → q (m , log)) (p' m)
    -}

    {- hmmm...
    >>=-uniq : ∀ P {Q} (pq : ⟦ P >>= Q ⟧)(p' : ⟦ P ⊥⟧) → pq ≡ [ P ] (>>=-fst P {Q} pq) >>>= (λ log → {!>>=-snd P {Q} pq p'!})
    >>=-uniq = {!!}
    -}

replicateᴾ : ℕ → Proto → Proto
replicateᴾ 0       P = end
replicateᴾ (suc n) P = P >> replicateᴾ n P

replicate-proc : ∀ n P → ⟦ P ⟧ → ⟦ replicateᴾ n P ⟧
replicate-proc zero    P p = end
replicate-proc (suc n) P p = [ P ] p >>> replicate-proc n P p

module _ {{_ : FunExt}}{{_ : UA}} where
  Log->>=-Σ : ∀ (P : Proto){Q} → Log (P >>= Q) ≡ Σ (Log P) (Log ∘ Q)
  Log->>=-Σ end       = ! (×= End-uniq refl ∙ 𝟙×-snd)
  Log->>=-Σ (com _ P) = Σ=′ _ (λ m → Log->>=-Σ (P m)) ∙ Σ-assoc

  Log->>-× : ∀ (P : Proto){Q} → Log (P >> Q) ≡ (Log P × Log Q)
  Log->>-× P = Log->>=-Σ P

  ++Log' : ∀ (P : Proto){Q : Log P → Proto} (xs : Log P) → Log (Q xs) → Log (P >>= Q)
  ++Log' P p q = coe! (Log->>=-Σ P) (p , q)

-- Same as ++Log' but computes better
++Log : ∀ (P : Proto){Q : Log P → Proto} (xs : Log P) → Log (Q xs) → Log (P >>= Q)
++Log end       _        ys = ys
++Log (com q P) (x , xs) ys = x , ++Log (P x) xs ys

module _ {{_ : FunExt}}{{_ : UA}} where

module _ {{_ : FunExt}} where
    >>-right-unit : ∀ P → (P >> end) ≡ P
    >>-right-unit end       = refl
    >>-right-unit (com q P) = com= refl refl λ m → >>-right-unit (P m)

    >>=-assoc : ∀ (P : Proto)(Q : Log P → Proto)(R : Log (P >>= Q) → Proto)
                → (P >>= (λ x → Q x >>= (λ y → R (++Log P x y)))) ≡ ((P >>= Q) >>= R)
    >>=-assoc end       Q R = refl
    >>=-assoc (com q P) Q R = com= refl refl λ m → >>=-assoc (P m) (λ ms → Q (m , ms)) (λ ms → R (m , ms))

    ap->>= : ∀ P {Q₀ Q₁} → (∀ {log} → ⟦ Q₀ log ⟧ ≡ ⟦ Q₁ log ⟧) → ⟦ P >>= Q₀ ⟧ ≡ ⟦ P >>= Q₁ ⟧
    ap->>= end      Q= = Q=
    ap->>= (send P) Q= = Σ=′ _ λ m → ap->>= (P m) Q=
    ap->>= (recv P) Q= = Π=′ _ λ m → ap->>= (P m) Q=

    dual->> : ∀ P Q → dual (P >> Q) ≡ (dual P >> dual Q)
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

    {-
    module _ {{_ : UA}} where
        >>>-right-unit : ∀ P (p : ⟦ P ⟧) → tr ⟦_⟧ (>>-right-unit P) ([ P ] p >>> end) ≡ p
        >>>-right-unit end      p = refl
        >>>-right-unit (recv P) p = {!!} ∙ λ= λ m →  >>>-right-unit (P m) (p m)
        >>>-right-unit (send P) (m , p) = {!!} ∙ pair= refl (>>>-right-unit (P m) p)
    -}

{- An incremental telecom function which makes processes communicate
   during a matching initial protocol. -}
>>=-telecom : (P : Proto){Q : Log P → Proto}{R : Log P → Proto}
            → ⟦ P >>= Q  ⟧
            → ⟦ P >>= R ⊥⟧
            → Σ (Log P) (λ t → ⟦ Q t ⟧ × ⟦ R t ⊥⟧)
>>=-telecom end      p0       p1       = _ , p0 , p1
>>=-telecom (send P) (m , p0) p1       = first (_,_ m) (>>=-telecom (P m) p0 (p1 m))
>>=-telecom (recv P) p0       (m , p1) = first (_,_ m) (>>=-telecom (P m) (p0 m) p1)

module _ (P : Proto){Q R : Proto} where
    >>-telecom : ⟦ P >> Q  ⟧
               → ⟦ P >> R ⊥⟧
               → Log P × ⟦ Q ⟧ × ⟦ R ⊥⟧
    >>-telecom = >>=-telecom P
-- -}
-- -}
-- -}
-- -}
