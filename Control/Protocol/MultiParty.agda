{-# OPTIONS --without-K #-}
open import Function.NP
open import Type
open import Data.Product.NP using (Σ;_,_;fst;snd)
open import Data.Zero
open import Data.One using (𝟙)
open import Data.Two hiding (_≟_; nand)
open Data.Two.Indexed
open import Relation.Binary.PropositionalEquality.NP using (_≡_; !_; _∙_; refl; tr; ap; coe; coe!)
open import Function.Extensionality
open import HoTT
open import Data.ShapePolymorphism
open Equivalences
open import Control.Protocol.Core
open import Control.Protocol.InOut

module Control.Protocol.MultiParty where

module _ (I : ★) where
    data MProto : ★₁ where
      _-[_]→_⁏_ : (A : I) (M : ★) (B : I) (ℂ : ..(m : M) → MProto) → MProto
      _-[_]→★⁏_ : (A : I) (M : ★)         (ℂ :   (m : M) → MProto) → MProto
      end       : MProto

module _ {I : ★} where 
    send-to : (A : I) {M : ★} (B : I) (ℂ : ..(m : M) → MProto I) → MProto I
    send-to A B ℂ = A -[ _ ]→ B ⁏ ℂ

    broadcast : (A : I) {M : ★} (ℂ : (m : M) → MProto I) → MProto I
    broadcast A ℂ = A -[ _ ]→★⁏ ℂ

    broadcast☐ : (A : I) {M : ★} (ℂ : ..(m : M) → MProto I) → MProto I
    broadcast☐ A ℂ = broadcast A λ { [ m ] → ℂ m }

    _-[_]→ø⁏_ : ∀ (A : I)(M : ★)(ℂ : ..(m : M) → MProto I) → MProto I
    A -[ M ]→ø⁏ ℂ = A -[ ☐ M ]→★⁏ λ { [ m ] → ℂ m }

    Group = I → 𝟚

    _/_ : (ℂ : MProto I) (φ : Group) → Proto
    (A -[ M ]→ B ⁏ ℂ) / φ = case φ A
                               0: case φ B
                                    0: recv (λ { [ m ] → ℂ m / φ })
                                    1: recv (λ     m   → ℂ m / φ)
                               1: send (λ m → ℂ m / φ)
    (A -[ M ]→★⁏   ℂ) / φ = com (case φ A 0: In 1: Out) λ m → ℂ m / φ
    end               / φ = end

    empty-group : Group
    empty-group _ = 0₂

    full-group : Group
    full-group _ = 1₂

    -- MultiParty Obs(erver)
    MObs : MProto I → Proto
    MObs ℂ = ℂ / empty-group

    -- MultiParty Log
    MLog : MProto I → Proto
    MLog ℂ = ℂ / full-group

    ℂLog-IsSource : ∀ ℂ → IsSource (MLog ℂ)
    ℂLog-IsSource (A -[ M ]→ B ⁏ ℂ) = send' λ m → ℂLog-IsSource (ℂ m)
    ℂLog-IsSource (A -[ M ]→★⁏   ℂ) = send' λ m → ℂLog-IsSource (ℂ m)
    ℂLog-IsSource end               = end

    ℂObserver-IsSink : ∀ ℂ → IsSink (MObs ℂ)
    ℂObserver-IsSink (A -[ M ]→ B ⁏ ℂ) = recv' λ { [ m ] → ℂObserver-IsSink (ℂ m) }
    ℂObserver-IsSink (A -[ M ]→★⁏   ℂ) = recv' λ m → ℂObserver-IsSink (ℂ m)
    ℂObserver-IsSink end = end

    data Nand : (x y : 𝟚) → ★ where
      n01 : Nand 0₂ 1₂
      n10 : Nand 1₂ 0₂
      n00 : Nand 0₂ 0₂

    or : ∀ {x y} → Nand x y → 𝟚
    or n01 = 1₂
    or n10 = 1₂
    or n00 = 0₂

    Nand° : (φ ψ : Group) → ★
    Nand° φ ψ = ∀ i → Nand (φ i) (ψ i)

    or° : ∀ {φ ψ} → Nand° φ ψ → Group
    or° r° = or ∘ r°

    data R : (x y z : 𝟚) → ★ where
      r01 : R 0₂ 1₂ 1₂
      r10 : R 1₂ 0₂ 1₂
      r00 : R 0₂ 0₂ 0₂

    R° : (φ ψ ξ : Group) → ★
    R° φ ψ ξ = ∀ i → R (φ i) (ψ i) (ξ i)

    Nand-R : ∀ {x y z} → R x y z → Σ (Nand x y) (_≡_ z ∘ or) 
    Nand-R r01 = n01 , refl
    Nand-R r10 = n10 , refl
    Nand-R r00 = n00 , refl

    Nand-R° : ∀ {x y z}{{_ : FunExt}} → R° x y z → Σ (Nand° x y) (_≡_ z ∘ or°)
    Nand-R° p = fst ∘ Nand-R ∘ p , λ= (λ i → snd (Nand-R (p i)))

    module _ {p q : I → 𝟚}(pq : Nand° p q) where
        group-merge : (ℂ : MProto I) → ⟦ ℂ / p ⟧ → ⟦ ℂ / q ⟧ → ⟦ ℂ / or° pq ⟧
        group-merge (A -[ M ]→ B ⁏ ℂ) ℂp ℂq with p A | q A | pq A | p B | q B | pq B
        group-merge (A -[ M ]→ B ⁏ ℂ) ℂp (m , ℂq) | .0₂ |  1₂ | n01 |  1₂ | .0₂ | n10 = m , group-merge (ℂ m) (ℂp m) ℂq
        group-merge (A -[ M ]→ B ⁏ ℂ) ℂp (m , ℂq) | .0₂ |  1₂ | n01 |  0₂ |  _  | _   = m , group-merge (ℂ m) (ℂp [ m ]) ℂq
        group-merge (A -[ M ]→ B ⁏ ℂ) (m , ℂp) ℂq |  1₂ | .0₂ | n10 | .0₂ |  1₂ | n01 = m , group-merge (ℂ m) ℂp (ℂq m)
        group-merge (A -[ M ]→ B ⁏ ℂ) (m , ℂp) ℂq |  1₂ | .0₂ | n10 |  _  |  0₂ | _   = m , group-merge (ℂ m) ℂp (ℂq [ m ])
        group-merge (A -[ M ]→ B ⁏ ℂ) ℂp ℂq       | .0₂ |  0₂ | n00 | .0₂ |  1₂ | n01 = λ m → group-merge (ℂ m) (ℂp [ m ]) (ℂq m)
        group-merge (A -[ M ]→ B ⁏ ℂ) ℂp ℂq       | .0₂ |  0₂ | n00 |  1₂ | .0₂ | n10 = λ m → group-merge (ℂ m) (ℂp m) (ℂq [ m ])
        group-merge (A -[ M ]→ B ⁏ ℂ) ℂp ℂq       | .0₂ |  0₂ | n00 |  0₂ |  0₂ | n00 = λ { [ m ] → group-merge (ℂ m) (ℂp [ m ]) (ℂq [ m ]) }
        group-merge (A -[ M ]→★⁏   ℂ) ℂp ℂq with p A | q A | pq A
        group-merge (A -[ M ]→★⁏   ℂ) ℂp (m , ℂq) | .0₂ |  1₂ | n01 = m , group-merge (ℂ m) (ℂp m) ℂq
        group-merge (A -[ M ]→★⁏   ℂ) (m , ℂp) ℂq |  1₂ | .0₂ | n10 = m , group-merge (ℂ m) ℂp (ℂq m)
        group-merge (A -[ M ]→★⁏   ℂ) ℂp ℂq       | .0₂ |  0₂ | n00 = λ m → group-merge (ℂ m) (ℂp m) (ℂq m)
        group-merge end ℂp ℂq = _

    module _ {p q r : I → 𝟚}(pqr : R° p q r){{_ : FunExt}} where
        group-merge' : (ℂ : MProto I) → ⟦ ℂ / p ⟧ → ⟦ ℂ / q ⟧ → ⟦ ℂ / r ⟧
        group-merge' ℂ p q with Nand-R° pqr
        ... | z , e = tr (⟦_⟧ ∘ _/_ ℂ) (! e) (group-merge z ℂ p q)

        {-
    module _ {p q r : I → 𝟚} where
        group-merge-assoc : (ℂ : MProto I)(Rqr : Nand° q r)(Rpq : Nand° p q)(Rpqr : Nand° p _)(Rpqr' : Nand° _ r) →
                             (ℂp : ⟦ ℂ / p ⟧) (ℂq : ⟦ ℂ / q ⟧) (ℂr : ⟦ ℂ / r ⟧)
                             → group-merge Rpqr ℂ ℂp (group-merge Rqr ℂ ℂq ℂr)
                             ≡ tr (λ x → ⟦ ℂ / nand° x ⟧) {!!}
                               (group-merge Rpqr' ℂ (group-merge Rpq ℂ ℂp ℂq) ℂr)
        group-merge-assoc = {!!}
        -}

    R-p-¬p-1 : ∀ (φ : I → 𝟚) i → R (φ i) (not (φ i)) 1₂
    R-p-¬p-1 φ i with φ i
    R-p-¬p-1 φ i | 1₂ = r10
    R-p-¬p-1 φ i | 0₂ = r01

    module _ {{_ : FunExt}} where
        group-bipart : {φ : I → 𝟚}(ℂ : MProto I) → ⟦ ℂ / φ ⟧ → ⟦ ℂ / (not ∘ φ) ⟧ → ⟦ MLog ℂ ⟧
        group-bipart {φ} ℂ ℂp ℂ¬p = group-merge' (R-p-¬p-1 φ) ℂ ℂp ℂ¬p

module _ {{_ : FunExt}} where
    -- Equivalent to telecom
    2com : (ℂ : MProto 𝟚) → ⟦ ℂ / id ⟧ → ⟦ ℂ / not ⟧ → ⟦ MLog ℂ ⟧
    2com = group-bipart

module ThreeParty where
  data 𝟛 : ★ where
    0₃ 1₃ 2₃ : 𝟛
  0₃? 1₃? 2₃? : 𝟛 → 𝟚
  0₃? 0₃ = 1₂
  0₃? _  = 0₂
  1₃? 1₃ = 1₂
  1₃? _  = 0₂
  2₃? 2₃ = 1₂
  2₃? _  = 0₂

  R-1-2-¬0 : R° 1₃? 2₃? (not ∘ 0₃?)
  R-1-2-¬0 0₃ = r00
  R-1-2-¬0 1₃ = r10
  R-1-2-¬0 2₃ = r01

  {- While this does not scale -}
  3com : (ℂ : MProto 𝟛) → ⟦ ℂ / 0₃? ⟧ → ⟦ ℂ / 1₃? ⟧ → ⟦ ℂ / 2₃? ⟧ → ⟦ MLog ℂ ⟧
  3com (0₃ -[ M ]→ 0₃ ⁏ ℂ) (m , p0) p1 p2 = m , 3com (ℂ m) p0 (p1 [ m ]) (p2 [ m ])
  3com (0₃ -[ M ]→ 1₃ ⁏ ℂ) (m , p0) p1 p2 = m , 3com (ℂ m) p0 (p1 m) (p2 [ m ])
  3com (0₃ -[ M ]→ 2₃ ⁏ ℂ) (m , p0) p1 p2 = m , 3com (ℂ m) p0 (p1 [ m ]) (p2 m)
  3com (1₃ -[ M ]→ 0₃ ⁏ ℂ) p0 (m , p1) p2 = m , 3com (ℂ m) (p0 m) p1 (p2 [ m ])
  3com (1₃ -[ M ]→ 1₃ ⁏ ℂ) p0 (m , p1) p2 = m , 3com (ℂ m) (p0 [ m ]) p1 (p2 [ m ])
  3com (1₃ -[ M ]→ 2₃ ⁏ ℂ) p0 (m , p1) p2 = m , 3com (ℂ m) (p0 [ m ]) p1 (p2 m)
  3com (2₃ -[ M ]→ 0₃ ⁏ ℂ) p0 p1 (m , p2) = m , 3com (ℂ m) (p0 m) (p1 [ m ]) p2
  3com (2₃ -[ M ]→ 1₃ ⁏ ℂ) p0 p1 (m , p2) = m , 3com (ℂ m) (p0 [ m ]) (p1 m) p2
  3com (2₃ -[ M ]→ 2₃ ⁏ ℂ) p0 p1 (m , p2) = m , 3com (ℂ m) (p0 [ m ]) (p1 [ m ]) p2
  3com (0₃ -[ M ]→★⁏    ℂ) (m , p0) p1 p2 = m , 3com (ℂ m) p0 (p1 m) (p2 m)
  3com (1₃ -[ M ]→★⁏    ℂ) p0 (m , p1) p2 = m , 3com (ℂ m) (p0 m) p1 (p2 m)
  3com (2₃ -[ M ]→★⁏    ℂ) p0 p1 (m , p2) = m , 3com (ℂ m) (p0 m) (p1 m) p2
  3com end p0 p1 p2 = _

  {- ...this one does -}
  module _ {{_ : FunExt}} where
    3com' : (ℂ : MProto 𝟛) → ⟦ ℂ / 0₃? ⟧ → ⟦ ℂ / 1₃? ⟧ → ⟦ ℂ / 2₃? ⟧ → ⟦ MLog ℂ ⟧
    3com' ℂ p0 p1 p2 = group-merge' (R-p-¬p-1 0₃?) ℂ p0 (group-merge' R-1-2-¬0 ℂ p1 p2)
-- -}
-- -}
-- -}
-- -}
