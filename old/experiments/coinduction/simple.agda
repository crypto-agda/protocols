{-# OPTIONS --copatterns #-}
module coinduction.simple where

--open import prelude
open import Data.Nat
open import Size

data M (A : Set) : Set
record M∞ (A : Set) : Set

data M A where
  leaf : A → M A
  node : (ℕ → M∞ A) → M A

record M∞ A where
  coinductive
  constructor mk
  field
    get : M A
open M∞ public

module _ {A} where
    ω : M A
    ω∞ : M∞ A 
    ω = node (λ _ → ω∞)
    get ω∞ = ω


{-
data M (A : Size → Set)(i : Size) : Set
record M∞ (A : Size → Set)(i : Size) : Set

data M A i where
  leaf : ∀ {j : Size< i} → A j → M A i
  node : (ℕ → M∞ A i) → M A i

record M∞ A i where
  coinductive
  field
    get : M A i
open M∞ public

-- -}
-- -}
-- -}
-- -}
-- -}
