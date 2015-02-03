open import Universe
open import Function
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP
open import Type
open import Level.NP
open import Data.One
open import Data.Product
open import Control.Protocol.InOut
open import Control.Protocol.End
open import HoTT
open Equivalences

module Control.Protocol.Universal {u e}(A : Universe u e) where
    U⟦_⟧ = Universe.El A
    U = Universe.U A

    data Proto : ★_(ₛ(u ⊔ e)) where
      end : Proto
      com : (io : InOut){M : U}(P : U⟦ M ⟧ → Proto) → Proto

    pattern recv P = com In  P
    pattern send P = com Out P

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

    ⟦_⟧ : Proto → ★_ e
    ⟦ end      ⟧ = End
    ⟦ com io P ⟧ = ⟦ io ⟧ᴵᴼ _ λ m → ⟦ P m ⟧

    ⟦_⊥⟧ : Proto → ★_ e
    ⟦ P ⊥⟧ = ⟦ dual P ⟧

    Log : Proto → ★_ e
    Log P = ⟦ source-of P ⟧

    Sink : Proto → ★_ e
    Sink P = ⟦ sink-of P ⟧

    sink : ∀ P → Sink P
    sink end         = _
    sink (com _ P) x = sink (P x)

    telecom : ∀ P → ⟦ P ⟧ → ⟦ P ⊥⟧ → Log P
    telecom end      _       _       = _
    telecom (recv P) p       (m , q) = m , telecom (P m) (p m) q
    telecom (send P) (m , p) q       = m , telecom (P m) p (q m)

    pattern recvE M P = com In  {M} P
    pattern sendE M P = com Out {M} P

    send′ : U → Proto → Proto
    send′ M P = send λ (_ : U⟦ M ⟧) → P

    recv′ : U → Proto → Proto
    recv′ M P = recv λ (_ : U⟦ M ⟧) → P

    module _ {{_ : FunExt}} where
        com= : ∀ {io₀ io₁}(io= : io₀ ≡ io₁)
                 {M₀ M₁ : U}(M= : M₀ ≡ M₁)
                 {P₀ P₁}(P= : (m₀ : U⟦ M₀ ⟧) → P₀ m₀ ≡ P₁ (tr U⟦_⟧ M= m₀))
               → com io₀ P₀ ≡ com io₁ P₁
        com= refl refl P= = ap (com _) (λ= P=)

        dual-involutive : ∀ P → dual (dual P) ≡ P
        dual-involutive end        = refl
        dual-involutive (com io P) = com= (dualᴵᴼ-involutive io) refl λ m → dual-involutive (P m)

        source-of-idempotent : ∀ P → source-of (source-of P) ≡ source-of P
        source-of-idempotent end       = refl
        source-of-idempotent (com _ P) = com= refl refl λ m → source-of-idempotent (P m)

        source-of-dual-oblivious : ∀ P → source-of (dual P) ≡ source-of P
        source-of-dual-oblivious end       = refl
        source-of-dual-oblivious (com _ P) = com= refl refl λ m → source-of-dual-oblivious (P m)

        dual-equiv : Is-equiv dual
        dual-equiv = self-inv-is-equiv _ dual-involutive

        dual-inj : ∀ {P Q} → dual P ≡ dual Q → P ≡ Q
        dual-inj = Is-equiv.injective dual-equiv

        send= = com= {Out} refl
        recv= = com= {In} refl

        com=′ : ∀ io {M}{P₀ P₁ : U⟦ M ⟧ → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → com io P₀ ≡ com io P₁
        com=′ io = com= refl refl

        send=′ : ∀ {M}{P₀ P₁ : U⟦ M ⟧ → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → send P₀ ≡ send P₁
        send=′ = send= refl

        recv=′ : ∀ {M}{P₀ P₁ : U⟦ M ⟧ → Proto}(P= : ∀ m → P₀ m ≡ P₁ m) → recv P₀ ≡ recv P₁
        recv=′ = recv= refl

        sink-contr : ∀ P s → sink P ≡ s
        sink-contr end       s = refl
        sink-contr (com _ P) s = λ= λ m → sink-contr (P m) (s m)

        Sink-is-contr : ∀ P → Is-contr (Sink P)
        Sink-is-contr P = sink P , sink-contr P

        𝟙≃Sink : ∀ P → 𝟙 ≃ Sink P
        𝟙≃Sink P = Is-contr-to-Is-equiv.𝟙≃ (Sink-is-contr P)

        dual-Log : ∀ P → Log (dual P) ≡ Log P
        dual-Log = ap ⟦_⟧ ∘ source-of-dual-oblivious

        data IsSource : Proto → ★_(ₛ(u ⊔ e)) where
          end   : IsSource end
          send' : ∀ {M P} (PT : (m : U⟦ M ⟧) → IsSource (P m)) → IsSource (send P)

        data IsSink : Proto → ★_(ₛ(u ⊔ e)) where
          end   : IsSink end
          recv' : ∀ {M P} (PT : (m : U⟦ M ⟧) → IsSink (P m)) → IsSink (recv P)
