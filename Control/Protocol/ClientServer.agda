open import Type
open import Type.Identities
open import Function.NP
open import Function.Extensionality
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Nat.NP
open import Data.Product.NP using (_,_; Σ; ∃)
open import Relation.Binary.PropositionalEquality.NP
open import HoTT

open import Control.Protocol.Core
open import Control.Protocol.Sequence

module Control.Protocol.ClientServer where

module _ (Query : ★₀) (Resp : Query → ★₀) where
    ClientRound ServerRound : Proto
    ClientRound = send λ (q : Query) → recv λ (r : Resp q) → end
    ServerRound = dual ClientRound

    ClientRounds ServerRounds : ℕ → Proto
    ClientRounds n = replicateᴾ n ClientRound
    ServerRounds = dual ∘ ClientRounds

    Server Client : Proto
    Client = send λ n →
             ClientRounds n
    Server = recv λ n →
             ServerRounds n

    module PureServer (serve : Π Query Resp) where
      server : ⟦ Server ⟧
      server zero      = _
      server (suc n) q = serve q , server n

module _ {{_ : FunExt}}{{_ : UA}} where
    open Equivalences

    send-is0?-uniq : ⟦ send (✓ᴾ ∘ is0?) ⟧ ≡ 𝟙
    send-is0?-uniq = Σ=′ _ (λ { zero → End-uniq ; (suc _) → Σ𝟘-fst }) ∙ ∃-is0?-uniq
module _ {R}{{_ : FunExt}}{{_ : UA}} where
    ClientRounds𝟘-Is0? : ∀ n → ClientRounds 𝟘 R n ≡ ✓ᴾ (is0? n)
    ClientRounds𝟘-Is0? zero    = refl
    ClientRounds𝟘-Is0? (suc _) = send=′ (λ())

    Client𝟘-uniq : ⟦ Client 𝟘 R ⟧ ≡ 𝟙
    Client𝟘-uniq = ap ⟦_⟧ (send=′ ClientRounds𝟘-Is0?) ∙ send-is0?-uniq

-- -}
-- -}
-- -}
-- -}
-- -}
