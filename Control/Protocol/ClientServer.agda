open import Type
open import Function.NP
open import Data.Nat
open import Data.Product.NP using (_,_)

open import Control.Protocol
open import Control.Protocol.Sequence

module Control.Protocol.ClientServer (Query : ★₀) (Resp : Query → ★₀) where
    ClientRound ServerRound : Proto
    ClientRound = send λ (q : Query) → recv λ (r : Resp q) → end
    ServerRound = dual ClientRound

    Client Server : ℕ → Proto
    Client n = replicateᴾ n ClientRound
    Server = dual ∘ Client

    DynamicServer StaticServer : Proto
    DynamicServer = recv λ n →
                    Server n
    StaticServer  = send λ n →
                    Server n

    module PureServer (serve : Π Query Resp) where
      server : ∀ n → ⟦ Server n ⟧
      server zero      = _
      server (suc n) q = serve q , server n
