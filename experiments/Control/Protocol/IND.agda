module Control.Protocol.IND where

open import Type
open import Control.Protocol
open import Data.Zero
open import Data.Two
open import Data.Product.NP
open import Relation.Binary.PropositionalEquality.NP
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import HoTT
open Equivalences

0≢1₂ : 0₂ ≢ 1₂
0≢1₂ ()

module _ {a}{A : ★_ a} where
  PathsFrom : (x : A) → ★_ a
  PathsFrom x = Σ A (_≡_ x)

  Adversary : ★_ a
  Adversary = A → 𝟚

  -- One round
  module Experiment (x y : A)
                    -- (Adv : Adversary)
                    (px : PathsFrom x)
                    (py : PathsFrom y)
                    where
      EXP : 𝟚 → Adversary → 𝟚
      EXP β Adv = Adv (proj (fst px , fst py) β)

      Adv-Winner : Adversary → ★
      Adv-Winner Adv = ∀ β → EXP β Adv ≡ β

      -- Equality cannot be defeated
      -- When equal the game cannot be constantly won
      IND-eq : x ≡ y → ∀ Adv → EXP 0₂ Adv ≡ EXP 1₂ Adv
      IND-eq xy Adv = ap Adv (! snd px ∙ xy ∙ snd py)

      module IND-dec (xy : x ≢ y) (A? : Decidable (_≡_ {A = A})) where
        Adv : Adversary
        Adv z = ⌊ A? y z ⌋

        Adv-winner : Adv-Winner Adv
        Adv-winner 1₂ with A? y (fst py)
        ... | yes p = refl
        ... | no ¬p = 𝟘-elim (¬p (snd py))
        Adv-winner 0₂ with A? y (fst px)
        ... | yes p = 𝟘-elim (xy (snd px ∙ ! p))
        ... | no ¬p = refl

  -- NAH...
  module IND-nec
           (Adv : (x y : A) → Adversary)
           (Adv-winner : ∀ x y px py → Experiment.Adv-Winner x y px py (Adv x y))
           where
    ¬¬ : ∀ {A : ★_ a} → ¬ (¬ A) → A
    ¬¬ = {!!}
    A? : Decidable (_≡_ {A = A})
    A? x y with Adv x y x | Adv-winner x y
    ... | 0₂ | w = yes (¬¬ (λ xy → xy {!w ? ? 0₂!}))
    ... | 1₂ | w = no (λ xy → let z = w (y , xy) (y , refl) in 0≢1₂ (! z 0₂ ∙ z 1₂) )
               {-
        Adv : Adversary
        Adv z = ⌊ A? y z ⌋

        Adv-winner : Adv-winner Adv
        Adv-winner 1₂ with A? y (fst py)
        ... | yes p = refl
        ... | no ¬p = 𝟘-elim (¬p (snd py))
        Adv-winner 0₂ with A? y (fst px)
        ... | yes p = 𝟘-elim (xy (snd px ∙ ! p))
        ... | no ¬p = refl
-- -}
-- -}
-- -}
