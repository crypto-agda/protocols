open import Type
open import Function
open import Data.One
open import Data.Two
open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Control.Protocol

module Control.Protocol.IP (Query : ★) (Resp : Query → ★) where

Accept? = 𝟚
accept! = 1₂
reject! = 0₂
Accept! = ✓

-- One round from the point of view of the verifier
VerifierRound : Proto
VerifierRound = send λ (q : Query)  →
                recv λ (r : Resp q) →
                end

ProverRound : Proto
ProverRound = dual VerifierRound

module Rounds (#rounds : ℕ) where
  Verifier-roundsᴾ = replicateᴾ #rounds VerifierRound

  Verifier-endᴾ = send λ (_ : Accept?) → end

  Verifierᴾ = Verifier-roundsᴾ >> Verifier-endᴾ

  Prover-endᴾ = dual Verifier-endᴾ

  Proverᴾ = dual Verifierᴾ

  Transcriptᴾ = source-of Verifierᴾ

  Prover   : ★
  Prover   = ⟦ Proverᴾ ⟧

  Verifier : ★
  Verifier = ⟦ Verifierᴾ ⟧

  Transcript : ★
  Transcript = ⟦ Transcriptᴾ ⟧

  >>-Transcript : ★
  >>-Transcript = Log Verifier-roundsᴾ × ⟦ Verifier-endᴾ ⟧ × ⟦ Verifier-endᴾ ⊥⟧

  accepting-transcript? : >>-Transcript → Accept?
  accepting-transcript? (_ , (a , _) , _) = a

  _⇆_ : Prover → Verifier → Accept?
  p ⇆ v = accepting-transcript? (>>-telecom Verifier-roundsᴾ v p)

record IP (#rounds : ℕ) {A : ★} (ℒ : A → ★) : ★ where
  open Rounds #rounds public

  field
    verifier : Verifier

  Convincing : Prover → ★
  Convincing = λ p → Accept! (p ⇆ verifier)

  Complete : ★
  Complete = ∀ x → ℒ x → Σ Prover Convincing

  Sound : ★
  Sound = ∀ x → ¬(ℒ x) → (p : Prover) → ¬(Convincing p)

NP-Verifier : ★
NP-Verifier = Σ Query λ q → Resp q → Accept? × End

NP-Verifier≡Verifier1 : NP-Verifier ≡ Rounds.Verifier 1
NP-Verifier≡Verifier1 = refl

NP : {A : ★} (ℒ : A → ★) → ★
NP = IP 1

-- -}
-- -}
-- -}
-- -}
