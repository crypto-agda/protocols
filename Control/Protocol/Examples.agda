{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Level.NP
open import Data.Product.NP using (_,_)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr; [_,_] to [inl:_,inr:_]) hiding ([_,_]′)
open import Data.Two hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP using (_≡_; coe)
open import Function.Extensionality
open import HoTT
open import Data.ShapePolymorphism
open Equivalences

open import Control.Protocol
open import Control.Protocol.Lift
open import Control.Protocol.Multiplicative

module Control.Protocol.Examples where

module MonomorphicSky (P : Proto₀) where
  Cloud : Proto₀
  Cloud = recv λ (t   : ⟦ P  ⟧) →
          recv λ (u   : ⟦ P ⊥⟧) →
          send λ (log : Log P)  →
          end
  cloud : ⟦ Cloud ⟧
  cloud t u = telecom P t u , _

module PolySky where
  Cloud : Proto_ ₁
  Cloud = recv λ (P : Proto₀) →
          liftᴾ ₁ (MonomorphicSky.Cloud P)
  cloud : ⟦ Cloud ⟧
  cloud P = lift-proc ₁ (MonomorphicSky.Cloud P) (MonomorphicSky.cloud P)

module PolySky' where
  Cloud : Proto_ ₁
  Cloud = recv λ (P   : Proto₀) →
          recv λ (t   : Lift ⟦ P  ⟧)  →
          recv λ (u   : Lift ⟦ P ⊥⟧)  →
          send λ (log : Lift (Log P)) →
          end
  cloud : ⟦ Cloud ⟧
  cloud P (lift t) (lift u) = lift (telecom P t u) , _

module Commitment {Secret Guess : ★} {R : ..(_ : Secret) → Guess → ★} where
    Commit : Proto
    Commit = send☐ λ (s : Secret) →
             recv  λ (g : Guess)  →
             send  λ (_ : S⟨ s ⟩) →
             end

    commit : (s : Secret)  → ⟦ Commit ⟧
    commit s = [ s ] , λ g → S[ s ] , _

    decommit : (g : Guess) → ⟦ dual Commit ⟧
    decommit g [ m ] = g , _

-- Prove knowledge of a discrete log
-- Adapted here to have precise types
module Shnorr-protocol
    (G ℤq : ★)
    (g    : G) 
    (_^_  : G  → ℤq → G)
    (_·_  : G  → G  → G)
    (_+_  : ℤq → ℤq → ℤq)
    (_*_  : ℤq → ℤq → ℤq)
    (_≟_  : (x y : G) → Dec (x ≡ y))
    where
    module Real where
        Prover : Proto
        Prover = send λ (gʳ : G)  → -- commitment
                 recv λ (c  : ℤq) → -- challenge
                 send λ (s  : ℤq) → -- response
                 end

        Verifier : Proto
        Verifier = dual Prover

        -- He is honest but its type does not say it
        -- The definition for "prover" below is derived from
        -- a well typed version.
        prover' : (x r : ℤq) → ⟦ Prover ⟧
        prover' x r = (g ^ r) , λ c → (r + (c * x)) , _

        verifier : (c : ℤq) → ⟦ Verifier ⟧
        verifier c _ = c , _

        module _ ..(x : ℤq) (y : S⟨ g ^ x ⟩) where
            Honest-Prover : Proto
            Honest-Prover
              = send☐ λ (r  : ℤq)                → -- ideal commitment
                send  λ (gʳ : S⟨ g ^ r ⟩)        → -- real  commitment
                recv  λ (c  : ℤq)                → -- challenge
                send  λ (s  : S⟨ r + (c * x) ⟩)  → -- response
                recv  λ (_  : Dec ((g ^ unS s) ≡ (unS gʳ · (unS y ^ c)))) →
                end

            Honest-Verifier : Proto
            Honest-Verifier = dual Honest-Prover

            honest-verifier' : (c : ℤq) → ⟦ Honest-Verifier ⟧
            honest-verifier' c [ r ] gʳ = c , λ s → _ ≟ _ , _

            sim-honest-prover : ⟦ Honest-Prover ⊸ Prover ⟧
            sim-honest-prover [ r ] S[ gʳ ∥ gʳ= ] = inr gʳ , λ c →
                                                    inl c  , λ { S[ s ∥ s= ] →
                                                    inr s  ,
                                                    _ ≟ _  ,
                                                    end }

            -- The next version is derived from sim-honest-prover
            honest-prover→prover' : ⟦ Honest-Prover ⟧ → ⟦ Prover ⟧
            honest-prover→prover' ([ r ] , gʳ , p) = unS gʳ , λ c → case p c of λ { (s , _) → unS s , _ }

            module _ {{_ : FunExt}}{{_ : UA}} where
                sim-honest-verifier : ⟦ Verifier ⊸ Honest-Verifier ⟧
                sim-honest-verifier = coe (⅋-comm Honest-Verifier _) sim-honest-prover

                honest-prover→prover : ⟦ Honest-Prover ⟧ → ⟦ Prover ⟧
                honest-prover→prover = ⊸-apply {Honest-Prover} sim-honest-prover

                verifier→honest-verifier : ⟦ Verifier ⟧ → ⟦ Honest-Verifier ⟧
                verifier→honest-verifier = ⊸-apply {Verifier} {Honest-Verifier} sim-honest-verifier

                honest-verifier : (c : ℤq) → ⟦ Honest-Verifier ⟧
                honest-verifier c = verifier→honest-verifier (verifier c)

        module _ (x r : ℤq) where
            honest-prover : ⟦ Honest-Prover x S[ g ^ x ] ⟧
            honest-prover = [ r ] , S[ g ^ r ] , λ c → S[ r + (c * x) ] , _
            -- agsy can do it

            module _ {{_ : FunExt}}{{_ : UA}} where
                prover : ⟦ Prover ⟧
                prover = honest-prover→prover x S[ g ^ x ] honest-prover
