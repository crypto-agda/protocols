open import Type
open import Function.NP
open import Data.Nat
open import Data.Product.NP using (_,_)

open import Control.Protocol.Core
open import Control.Protocol.Sequence

module Control.Protocol.ClientServer (Query : ★₀) (Resp : Query → ★₀) where
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
