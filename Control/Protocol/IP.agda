open import Type
open import Function
open import Control.Protocol.Choreography
open import Data.One
open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Control.Protocol.IP (Query : ★) (Resp : Query → ★) where

-- One round from the point of view of the verifier
VerifierRound : Proto
VerifierRound = Σᴾ Query    λ q →
                Πᴾ (Resp q) λ r →
                end

ProverRound : Proto
ProverRound = dual VerifierRound

module Rounds (#rounds : ℕ) where
  Verifierᴾ : Proto
  Verifierᴾ = replicateᴾ #rounds VerifierRound >> (Σᴾ Accept? λ _ → end)

  Proverᴾ   : Proto
  Proverᴾ   = dual Verifierᴾ

  Transcriptᴾ : Proto
  Transcriptᴾ = source-of Verifierᴾ

  Prover   : ★
  Prover   = ⟦ Proverᴾ ⟧

  Verifier : ★
  Verifier = ⟦ Verifierᴾ ⟧

  Transcript : ★
  Transcript = ⟦ Transcriptᴾ ⟧

  _⇆_ : Prover → Verifier → Accept?
  _⇆_ = λ p v → case >>-com (replicateᴾ #rounds VerifierRound) v p of λ { (_ , (a , _) , _) → a }

record IP (#rounds : ℕ) {A : ★} (ℒ : A → ★) : ★ where
  open Rounds #rounds public

  field
    verifier : Verifier

  Convincing : Prover → ★
  Convincing = λ p → Is-accept (p ⇆ verifier)

  Complete : ★
  Complete = ∀ x → ℒ x → Σ Prover Convincing

  Sound : ★
  Sound = ∀ x → ¬(ℒ x) → (p : Prover) → ¬(Convincing p)

NP-Verifier = Σ Query λ q → Resp q → Accept? × 𝟙

NP-Verifier≡Verifier1 : NP-Verifier ≡ Rounds.Verifier 1
NP-Verifier≡Verifier1 = refl

NP : {A : ★} (ℒ : A → ★) → ★
NP = IP 1

-- -}
-- -}
-- -}
-- -}
