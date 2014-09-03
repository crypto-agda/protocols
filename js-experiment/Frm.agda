{-# OPTIONS --without-K #-}
module Frm where
open import proto hiding (_⊗_; _⅋_) renaming (Proto to Session)
open import Types using  (Ended)
open import prelude

data Frm {a} (A : Set a) : Set a where
  ε       : Frm A
  act     : (S : A) → Frm A
  _⅋_ _⊗_ : (Γ Δ : Frm A) → Frm A

data _∈_ {a} {A : Set a} (S : A) : Frm A → Set a where
  act   : ∀ {S'} → S ≡ S' → S ∈ (act S')
  left  : ∀ {Γ Δ} → S ∈ Γ → S ∈ (Γ ⅋ Δ)
  right : ∀ {Γ Δ} → S ∈ Δ → S ∈ (Γ ⅋ Δ)

_∉_ : ∀ {a} {A : Set a} (S : A) → Frm A → Set a
S ∉ Γ = ¬(S ∈ Γ)

module _ {a}{A : Set a}{S : A} where
  _[_≔_] : ∀ Δ → S ∈ Δ → A → Frm A
  ._ [ act e ≔ Q ]           = act Q
  ._ [ left  {Γ} {Δ} p ≔ Q ] = (Γ [ p ≔ Q ]) ⅋ Δ
  ._ [ right {Γ} {Δ} p ≔ Q ] = Γ ⅋ (Δ [ p ≔ Q ])

module _ {a} {A : Set a} where
    AllEnv : (P : A → Set) → Frm A → Set
    AllEnv P ε = 𝟙
    AllEnv P (act S) = P S
    AllEnv P (Γ ⅋ Δ) = AllEnv P Γ × AllEnv P Δ
    AllEnv P (Γ ⊗ Δ) = AllEnv P Γ × AllEnv P Δ

data [_is_⋎_]S : (S S₀ S₁ : Session) → Set₁ where 
  act₀ : ∀ {P} → [ P is P ⋎ end ]S
  act₁ : ∀ {P} → [ P is end ⋎ P ]S

module FrmZip {a ℓ} {A : Set a} ([_is_⋎_]' : (P Q R : A) → Set ℓ) where
    data [_is_⋎_] : (Δ Δ₀ Δ₁ : Frm A) → Set (a ⊔ ℓ) where 
      ε   : [ ε is ε ⋎ ε ]
      act : ∀ {P Q R}
          → [ P is Q ⋎ R ]'
          → [ act P is act Q ⋎ act R ]
      _⊗_ : ∀ {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁'}
          → [ Δ  is Δ₀  ⋎ Δ₁  ]
          → [ Δ' is Δ₀' ⋎ Δ₁' ]
          → [ Δ ⊗ Δ' is Δ₀ ⊗ Δ₀' ⋎ Δ₁ ⊗ Δ₁' ]
      _⅋_ : ∀ {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁'}
          → [ Δ  is Δ₀  ⋎ Δ₁  ]
          → [ Δ' is Δ₀' ⋎ Δ₁' ]
          → [ Δ ⅋ Δ' is Δ₀ ⅋ Δ₀' ⋎ Δ₁ ⅋ Δ₁' ]

open FrmZip [_is_⋎_]S 

Proto = Frm Session

module _ {c M}{{_ : M ≃? SERIAL}}{S} where
  _[_≔_]' : (Δ : Proto) → com c {M} S ∈ Δ → M → Proto
  Δ [ l ≔ m ]' = Δ [ l ≔ S m ]

EndedEnv : Proto → Set
EndedEnv = AllEnv Ended

ZipAll : ∀ {P Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → AllEnv P Δ₀ → AllEnv P Δ₁ → AllEnv P Δ
ZipAll ε A₀ A₁ = <>
ZipAll (act act₀) A₀ A₁ = A₀
ZipAll (act act₁) A₀ A₁ = A₁
ZipAll (Δₛ₀ ⊗ Δₛ₁) (A₀ , A₀') (A₁ , A₁') = ZipAll Δₛ₀ A₀ A₁ , ZipAll Δₛ₁ A₀' A₁'
ZipAll (Δₛ₀ ⅋ Δₛ₁) (A₀ , A₀') (A₁ , A₁') = ZipAll Δₛ₀ A₀ A₁ , ZipAll Δₛ₁ A₀' A₁'

ZipEnded : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → EndedEnv Δ₀ → EndedEnv Δ₁ → EndedEnv Δ
ZipEnded = ZipAll

Ended-≡end : ∀ {P} → Ended P → P ≡ end
Ended-≡end {end} e = refl
Ended-≡end {send P} ()
Ended-≡end {recv P} ()

ZipS-comm : ∀ {S₀ S₁ S} → [ S is S₀ ⋎ S₁ ]S → [ S is S₁ ⋎ S₀ ]S
ZipS-comm act₀ = act₁
ZipS-comm act₁ = act₀

Zip-comm : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → [ Δ is Δ₁ ⋎ Δ₀ ]
Zip-comm ε = ε
Zip-comm (act x) = act (ZipS-comm x)
Zip-comm (z₀ ⊗ z₁) = Zip-comm z₀ ⊗ Zip-comm z₁
Zip-comm (z₀ ⅋ z₁) = Zip-comm z₀ ⅋ Zip-comm z₁

ZipS-identity : ∀ {S₀ S₁ S} {{S₀E : Ended S₀}} → [ S is S₀ ⋎ S₁ ]S → S₁ ≡ S
ZipS-identity {{e}} act₀ = !(Ended-≡end e)
ZipS-identity {{e}} act₁ = refl

Zip-identity : ∀ {Δ₀ Δ₁ Δ} {{Δ₀E : EndedEnv Δ₀}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₁ ≡ Δ
Zip-identity ε = refl
Zip-identity (act x) = ap act (ZipS-identity x)
Zip-identity {{e₀ , e₁}} (z₀ ⊗ z₁) = ap₂ _⊗_ (Zip-identity z₀) (Zip-identity z₁)
Zip-identity {{e₀ , e₁}} (z₀ ⅋ z₁) = ap₂ _⅋_ (Zip-identity z₀) (Zip-identity z₁)

Zip-identity' : ∀ {Δ₀ Δ₁ Δ} {{Δ₁E : EndedEnv Δ₁}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₀ ≡ Δ
Zip-identity' Z = Zip-identity (Zip-comm Z)

module _ {io M}{{_ : SER M}} {P : M → Session} where
    ZipS-com∈₀ : ∀ {S₀ S₁ S} → [ S is S₀ ⋎ S₁ ]S → com io P ∈ act S₀ → com io P ∈ act S
    ZipS-com∈₀ act₀ x₁ = x₁
    ZipS-com∈₀ act₁ (act ())

    Zip-com∈₀ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → com io P ∈ Δ₀ → com io P ∈ Δ
    Zip-com∈₀ ε p = p
    Zip-com∈₀ (act x₁) p = ZipS-com∈₀ x₁ p
    Zip-com∈₀ (_ ⊗ _) ()
    Zip-com∈₀ (z₀ ⅋ z₁) (left  p) = left (Zip-com∈₀ z₀ p)
    Zip-com∈₀ (z₀ ⅋ z₁) (right p) = right (Zip-com∈₀ z₁ p)

    Zip-com∈₁ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → com io P ∈ Δ₁ → com io P ∈ Δ
    Zip-com∈₁ Z = Zip-com∈₀ (Zip-comm Z)

    Zip-≔₀ : ∀ {Δ Δ₀ Δ₁}
              (l : com io P ∈ Δ₀) {m : M}
              (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
              [ Δ [ Zip-com∈₀ Δₛ l ≔ m ]' is Δ₀ [ l ≔ m ]' ⋎ Δ₁ ]
    Zip-≔₀ (act refl) (act act₀) = act act₀
    Zip-≔₀ (left l)  (z₀ ⅋ z₁) = Zip-≔₀ l z₀ ⅋ z₁
    Zip-≔₀ (right l) (z₀ ⅋ z₁) = z₀ ⅋ Zip-≔₀ l z₁

    Zip-≔₁ : ∀ {Δ Δ₀ Δ₁}
               (l : com io P ∈ Δ₁) {m : M} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
             [ Δ [ Zip-com∈₁ Δₛ l ≔ m ]' is Δ₀ ⋎ Δ₁ [ l ≔ m ]' ]
    Zip-≔₁ l Δₛ = Zip-comm (Zip-≔₀ l (Zip-comm Δₛ))

Zip-⅋-comm : ∀ {Γ₀ Δ₀ Γ₁ Δ₁ Γ Δ}
             → [ Γ ⅋ Δ is Γ₀ ⅋ Δ₀ ⋎ Γ₁ ⅋ Δ₁ ]
             → [ Δ ⅋ Γ is Δ₀ ⅋ Γ₀ ⋎ Δ₁ ⅋ Γ₁ ]
Zip-⅋-comm (z₀ ⅋ z₁) = z₁ ⅋ z₀

{-
Zip-⅋-assoc₀ : ∀ {Γ₀ Δ₀ Ψ₀ Γ₁ Δ₁ Ψ₁ Γ Δ Ψ}
              → [ Γ is Γ₀ ⅋ (Δ₀ ⅋ Ψ₀) ⋎ Γ₁ ⅋ (Δ₁ ⅋ Ψ₁) ]
              → [ Γ is (Γ₀ ⅋ Δ₀) ⅋ Ψ₀ ⋎ (Γ₁ ⅋ Δ₁) ⅋ Ψ₁ ]
Zip-⅋-assoc₀ (z₀ ⅋ (z₁ ⅋ z₂)) = (z₀ ⅋ z₁) ⅋ z₂
-}

Zip-⅋-assoc : ∀ {Γ₀ Δ₀ Ψ₀ Γ₁ Δ₁ Ψ₁ Γ Δ Ψ}
              → [ Γ ⅋ (Δ ⅋ Ψ) is Γ₀ ⅋ (Δ₀ ⅋ Ψ₀) ⋎ Γ₁ ⅋ (Δ₁ ⅋ Ψ₁) ]
              → [ (Γ ⅋ Δ) ⅋ Ψ is (Γ₀ ⅋ Δ₀) ⅋ Ψ₀ ⋎ (Γ₁ ⅋ Δ₁) ⅋ Ψ₁ ]
Zip-⅋-assoc (z₀ ⅋ (z₁ ⅋ z₂)) = (z₀ ⅋ z₁) ⅋ z₂

Zip-⅋-assoc' : ∀ {Γ₀ Δ₀ Ψ₀ Γ₁ Δ₁ Ψ₁ Γ Δ Ψ}
               → [ (Γ ⅋ Δ) ⅋ Ψ is (Γ₀ ⅋ Δ₀) ⅋ Ψ₀ ⋎ (Γ₁ ⅋ Δ₁) ⅋ Ψ₁ ]
               → [ Γ ⅋ (Δ ⅋ Ψ) is Γ₀ ⅋ (Δ₀ ⅋ Ψ₀) ⋎ Γ₁ ⅋ (Δ₁ ⅋ Ψ₁) ]
Zip-⅋-assoc' ((z₀ ⅋ z₁) ⅋ z₂) = z₀ ⅋ (z₁ ⅋ z₂)

-- -}
-- -}
-- -}
-- -}
-- -}
