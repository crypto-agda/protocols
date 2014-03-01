{-# OPTIONS --without-K #-}
open import Type
open import Control.Protocol
open import Control.Protocol.Additive
open import Control.Protocol.Multiplicative

module Control.Protocol.CLL where
{-
A `⊗ B 'times', context chooses how A and B are used
A `⅋ B 'par', "we" chooses how A and B are used
A `⊕ B 'plus', select from A or B
A `& B 'with', offer choice of A or B
`! A   'of course!', server accept
`? A   'why not?', client request
`1     unit for `⊗
`⊥     unit for `⅋
`0     unit for `⊕
`⊤     unit for `&
-}
data CLL : ★ where
  `1 `⊤ `0 `⊥ : CLL
  _`⊗_ _`⅋_ _`⊕_ _`&_ : (A B : CLL) → CLL
  -- `!_ `?_ : (A : CLL) → CLL

_⊥ : CLL → CLL
`1 ⊥ = `⊥
`⊥ ⊥ = `1
`0 ⊥ = `⊤
`⊤ ⊥ = `0
(A `⊗ B)⊥ = A ⊥ `⅋ B ⊥
(A `⅋ B)⊥ = A ⊥ `⊗ B ⊥
(A `⊕ B)⊥ = A ⊥ `& B ⊥
(A `& B)⊥ = A ⊥ `⊕ B ⊥
{-
(`! A)⊥ = `?(A ⊥)
(`? A)⊥ = `!(A ⊥)
-}

CLL-proto : CLL → Proto
CLL-proto `1       = end
CLL-proto `⊥       = end
CLL-proto `0       = P0
CLL-proto `⊤       = P⊤
CLL-proto (A `⊗ B) = CLL-proto A ⊗ CLL-proto B
CLL-proto (A `⅋ B) = CLL-proto A ⅋ CLL-proto B
CLL-proto (A `⊕ B) = CLL-proto A ⊕ CLL-proto B
CLL-proto (A `& B) = CLL-proto A & CLL-proto B

{- The point of this could be to devise a particular equivalence
   relation for processes. It could properly deal with ⅋. -}
