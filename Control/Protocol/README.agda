module Control.Protocol.README where

-- This module exports the most common definitions
import Control.Protocol

-- Protocols, duality, log, telecom
import Control.Protocol.Core

-- Examples
import Control.Protocol.Examples

-- Sequencing protocols (_>>=_, _>>_, replicateᴾ...)
import Control.Protocol.Sequence

-- Simple Query/Response abstraction
import Control.Protocol.ClientServer

-- Choices (arity 0 and 2):
-- This corresponds to the additive fragment of
-- linear logic (⊕, 0, &, ⊤).
import Control.Protocol.Additive

-- Concurrent or interleaved protocols
-- This corresponds to the multiplicative fragment
-- of linear logic (⊗, 1, ⅋, ⊥)
import Control.Protocol.Multiplicative

-- A simple yet powerful multiparty layer
-- on top of dependent protocols.
import Control.Protocol.MultiParty

-- Internals
import Control.Protocol.End
import Control.Protocol.InOut

-- Less important: experimental...
import Control.Protocol.Alternate
import Control.Protocol.CLL
import Control.Protocol.Extend
import Control.Protocol.Lift
import Control.Protocol.Relation
