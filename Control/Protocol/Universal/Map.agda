open import Universe.NP
open import Type
open import Function
open import Data.Product.NP
open import Control.Protocol.Universal
open import Relation.Binary.PropositionalEquality

module Control.Protocol.Universal.Map where

module _ {a b}{A : ★_ a}{B : ★_ b} (f : A → B) where
  Fib' = ∀ (g : B → A) (x : B) → f (g x) ≡ x

record Fib (A B : ★₀) : ★₀ where
  field
    f     : A → B
    f-fib : Fib' f

    {-
module _ {A : ★₀} {B : A → ★₀} where
  fst-fib : Fib' {Σ A B} fst
  fst-fib = λ g x → {!!}
  -}

  {-
open import Data.Vec
module _ {a}{A : ★_ a} where
    vec-fib : Fib' {Σ ℕ Vec} ?
    vec-fib = λ g x → {!!}
    -}

module M
  {u u'} {U : Universe u u'}
  {v v'} {V : Universe v v'}
  (um : CoMap U V)
  where
    open CoMap um

    map-Proto : Proto U → Proto V
    map-Proto end        = end
    map-Proto (com io P) = com io (λ x → map-Proto (P (comap-El x)))

foo : Proto UFinite → Proto U★₀
foo = M.map-Proto finite

open import Data.Nat.NP
open import Data.Fin using (Fin;#_)
open import Data.Vec
open import Control.Protocol.InOut
open import Control.Protocol.End

module _ (n A : ℕ)(VecFin≡Fin : Vec (Fin A) n ≡ Fin (A ^ n)) where
    lookupP : Proto UFinite
    lookupP = com In  {_ , _ , refl}       λ (i : Fin n) →
              com In  {_ , _ , VecFin≡Fin} λ (v : Vec (Fin A) n) →
              com Out {_ , _ , refl}       λ (r : Fin A) →
              end
    lookup' : ⟦_⟧ UFinite lookupP
    lookup' = λ i v → lookup i v , _

lookup⊥ : ⟦_⊥⟧ UFinite (lookupP 2 6 {!!})
lookup⊥ = # 1 , # 2 ∷ # 5 ∷ [] , _

