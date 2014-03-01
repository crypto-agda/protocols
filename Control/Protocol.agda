{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP using (Σ; _×_; _,_) renaming (proj₁ to fst)
open import Data.One using (𝟙)
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; ap; coe; coe!)
open import Function.Extensionality
open import HoTT
open import Data.ShapePolymorphism
open Equivalences

module Control.Protocol where

data InOut : ★ where
  In Out : InOut

dualᴵᴼ : InOut → InOut
dualᴵᴼ In  = Out
dualᴵᴼ Out = In

dualᴵᴼ-involutive : ∀ io → dualᴵᴼ (dualᴵᴼ io) ≡ io
dualᴵᴼ-involutive In = refl
dualᴵᴼ-involutive Out = refl

dualᴵᴼ-equiv : Is-equiv dualᴵᴼ
dualᴵᴼ-equiv = self-inv-is-equiv dualᴵᴼ-involutive

dualᴵᴼ-inj : ∀ {x y} → dualᴵᴼ x ≡ dualᴵᴼ y → x ≡ y
dualᴵᴼ-inj = Is-equiv.injective dualᴵᴼ-equiv

{-
module UniversalProtocols ℓ {U : ★_(ₛ ℓ)}(U⟦_⟧ : U → ★_ ℓ) where
-}
module _ ℓ where
  U = ★_ ℓ
  U⟦_⟧ = id
  data Proto_ : ★_(ₛ ℓ) where
    end : Proto_
    com : (io : InOut){M : U}(P : U⟦ M ⟧ → Proto_) → Proto_
{-
module U★ ℓ = UniversalProtocols ℓ {★_ ℓ} id
open U★
-}

Proto : ★₁
Proto = Proto_ ₀
Proto₀ = Proto
Proto₁ = Proto_ ₁

pattern recv P = com In  P
pattern send P = com Out P

module _ {{_ : FunExt}} where
    com= : ∀ {io₀ io₁}(io= : io₀ ≡ io₁)
             {M₀ M₁}(M= : M₀ ≡ M₁)
             {P₀ : M₀ → Proto}{P₁ : M₁ → Proto}(P= : ∀ m₀ → P₀ m₀ ≡ P₁ (coe M= m₀))
           → com io₀ P₀ ≡ com io₁ P₁
    com= refl refl P= = ap (com _) (λ= P=)

    module _ {io₀ io₁}(io= : io₀ ≡ io₁)
             {M₀ M₁}(M≃ : M₀ ≃ M₁)
             {P₀ : M₀ → Proto}{P₁ : M₁ → Proto}
             (P= : ∀ m₀ → P₀ m₀ ≡ P₁ (–> M≃ m₀))
             {{_ : UA}} where
        com≃ : com io₀ P₀ ≡ com io₁ P₁
        com≃ = com= io= (ua M≃) λ m → P= m ∙ ap P₁ (! coe-β M≃ m)

    module _ io {M N}(P : M × N → Proto)
             where
        com₂ : Proto
        com₂ = com io λ m → com io λ n → P (m , n)

    {- Proving this would be awesome...
    module _ io
             {M₀ M₁ N₀ N₁ : ★}
             (M×N≃ : (M₀ × N₀) ≃ (M₁ × N₁))
             {P₀ : M₀ × N₀ → Proto}{P₁ : M₁ × N₁ → Proto}
             (P= : ∀ m,n₀ → P₀ m,n₀ ≡ P₁ (–> M×N≃ m,n₀))
             {{_ : UA}} where
        com₂≃ : com₂ io P₀ ≡ com₂ io P₁
        com₂≃ = {!com=!}
    -}

    send= = com= {Out} refl
    send≃ = com≃ {Out} refl
    recv= = com= {In} refl
    recv≃ = com≃ {In} refl

    com=′ : ∀ io {M}{P₀ P₁ : M → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → com io P₀ ≡ com io P₁
    com=′ io = com= refl refl

    send=′ : ∀ {M}{P₀ P₁ : M → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → send P₀ ≡ send P₁
    send=′ = send= refl

    recv=′ : ∀ {M}{P₀ P₁ : M → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → recv P₀ ≡ recv P₁
    recv=′ = recv= refl

pattern recvE M P = com In  {M} P
pattern sendE M P = com Out {M} P

recv☐ : {M : ★}(P : ..(_ : M) → Proto) → Proto
recv☐ P = recv (λ { [ m ] → P m })

send☐ : {M : ★}(P : ..(_ : M) → Proto) → Proto
send☐ P = send (λ { [ m ] → P m })

{-
dual : Proto → Proto
dual end      = end
dual (send P) = recv λ m → dual (P m)
dual (recv P) = send λ m → dual (P m)
-}

dual : Proto → Proto
dual end        = end
dual (com io P) = com (dualᴵᴼ io) λ m → dual (P m)

source-of : Proto → Proto
source-of end       = end
source-of (com _ P) = send λ m → source-of (P m)

sink-of : Proto → Proto
sink-of = dual ∘ source-of

data IsSource : Proto → ★₁ where
  end   : IsSource end
  send' : ∀ {M P} (PT : (m : M) → IsSource (P m)) → IsSource (send P)

data IsSink : Proto → ★₁ where
  end   : IsSink end
  recv' : ∀ {M P} (PT : (m : M) → IsSink (P m)) → IsSink (recv P)

data Proto☐ : Proto → ★₁ where
  end : Proto☐ end
  com : ∀ io {M P} (P☐ : ∀ (m : ☐ M) → Proto☐ (P m)) → Proto☐ (com io P)

record End_ ℓ : ★_ ℓ where
  constructor end

End : ∀ {ℓ} → ★_ ℓ
End = End_ _

End-equiv : End ≃ 𝟙
End-equiv = equiv {₀} _ _ (λ _ → refl) (λ _ → refl)

End-uniq : {{_ : UA}} → End ≡ 𝟙
End-uniq = ua End-equiv

⟦_⟧ᴵᴼ : InOut → ∀{ℓ}(M : ★_ ℓ)(P : M → ★_ ℓ) → ★_ ℓ
⟦_⟧ᴵᴼ In  = Π
⟦_⟧ᴵᴼ Out = Σ

⟦_⟧ : ∀ {ℓ} → Proto_ ℓ → ★_ ℓ
⟦ end      ⟧ = End
⟦ com io P ⟧ = ⟦ io ⟧ᴵᴼ _ λ m → ⟦ P m ⟧

⟦_⊥⟧ : Proto → ★
⟦ P ⊥⟧ = ⟦ dual P ⟧

Log : Proto → ★
Log P = ⟦ source-of P ⟧

Sink : Proto → ★
Sink P = ⟦ sink-of P ⟧

sink : ∀ P → Sink P
sink end         = _
sink (com _ P) x = sink (P x)

telecom : ∀ P → ⟦ P ⟧ → ⟦ P ⊥⟧ → Log P
telecom end      _       _       = _
telecom (recv P) p       (m , q) = m , telecom (P m) (p m) q
telecom (send P) (m , p) q       = m , telecom (P m) p (q m)

send′ : ★ → Proto → Proto
send′ M P = send λ (_ : M) → P

recv′ : ★ → Proto → Proto
recv′ M P = recv λ (_ : M) → P

module _ {{_ : FunExt}} where
    dual-involutive : ∀ P → dual (dual P) ≡ P
    dual-involutive end        = refl
    dual-involutive (com io P) = com= (dualᴵᴼ-involutive io) refl λ m → dual-involutive (P m)

    dual-equiv : Is-equiv dual
    dual-equiv = self-inv-is-equiv dual-involutive

    dual-inj : ∀ {P Q} → dual P ≡ dual Q → P ≡ Q
    dual-inj = Is-equiv.injective dual-equiv

    source-of-idempotent : ∀ P → source-of (source-of P) ≡ source-of P
    source-of-idempotent end       = refl
    source-of-idempotent (com _ P) = com= refl refl λ m → source-of-idempotent (P m)

    source-of-dual-oblivious : ∀ P → source-of (dual P) ≡ source-of P
    source-of-dual-oblivious end       = refl
    source-of-dual-oblivious (com _ P) = com= refl refl λ m → source-of-dual-oblivious (P m)

module _ {{_ : FunExt}} where
    sink-contr : ∀ P s → sink P ≡ s
    sink-contr end       s = refl
    sink-contr (com _ P) s = λ= λ m → sink-contr (P m) (s m)

    Sink-is-contr : ∀ P → Is-contr (Sink P)
    Sink-is-contr P = sink P , sink-contr P

    𝟙≃Sink : ∀ P → 𝟙 ≃ Sink P
    𝟙≃Sink P = Is-contr-to-Is-equiv.𝟙≃ (Sink-is-contr P)

    dual-Log : ∀ P → Log (dual P) ≡ Log P
    dual-Log = ap ⟦_⟧ ∘ source-of-dual-oblivious
