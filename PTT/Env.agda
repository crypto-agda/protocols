{-# OPTIONS --copatterns #-}
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Product renaming (proj₁ to fst; proj₂ to snd; _,_ to ⟨_,_⟩) hiding (map)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.NP
open import PTT.Dom as Dom
open import PTT.Session as Session hiding (Ended)

module PTT.Env where

open import PTT.Map as Map public

private
    M = MSession

Env : Dom → Set₁
Env = Map MSession

module _ {δ c}(E : Env δ) where
  infixl 4 _/'_ _/D_
  _/D_ :  c ∈D δ → Env δ
  _/D_ l = E [ l ]≔' end

  _/'_ : ∀ {S} → c ↦ S ∈ E → Env δ
  _/'_ l = _/D_ (_↦_∈_.lA l)

infixr 4 _♦Env_
_♦Env_ : ∀ {D₀ D₁} → Env D₀ → Env D₁ → Env (D₀ ♦Dom D₁)
_♦Env_ = _♦Map_

-- open With-end {_} {MSession} end public
-- module With-end {a}{M : Set a}(end : M) where

module _ {δ}(Δ : Env δ) where
    _/* : Env δ
    _/* = map (λ _ → end) Δ

abstract
    _/[_]_ : ∀ {δ}(Δ : Env δ)(b : 𝟚)(σ : Selection δ) → Env δ
    Δ /[ b ] σ = zipWith (selectProj b) Δ σ

module _ {δ}(Δ : Env δ)(σ : Selection δ) where
    _/₀_ : Env δ
    _/₀_ = Δ /[ 0₂ ] σ

    _/₁_ : Env δ
    _/₁_ = Δ /[ 1₂ ] σ

data Zip : ∀ {δ} → Env δ → Env δ → Env δ → Set₁ where
  ε : Zip ε ε ε
  _,_↦₀_ : ∀ {δ Δ₀ Δ₁} {Δ : Env δ}(Z : Zip Δ Δ₀ Δ₁) d S → Zip (Δ , d ↦ S) (Δ₀ , d ↦ S)   (Δ₁ , d ↦ end)
  _,_↦₁_ : ∀ {δ Δ₀ Δ₁} {Δ : Env δ}(Z : Zip Δ Δ₀ Δ₁) d S → Zip (Δ , d ↦ S) (Δ₀ , d ↦ end) (Δ₁ , d ↦ S)

[_is_⋎_] : ∀ {δ} → Env δ → Env δ → Env δ → Set₁
[_is_⋎_] = Zip

Ended : ∀ {δ}(E : Env δ) → Set
Ended = Map.All (λ _ → Session.Ended)

Ended-/* : ∀ {δ}(E : Env δ) → Ended (E /*)
Ended-/* ε = _
Ended-/* (E , c ↦ v) = ⟨ Ended-/* E , _ ⟩

Ended-∈D : ∀ {δE c}{E : Env δE} (l : c ∈D δE) → Ended E → Session.Ended (lookup E l)
Ended-∈D {E = _ , _ ↦ _} here      EE = snd EE
Ended-∈D {E = _ , _ ↦ _} (there l) EE = Ended-∈D l (fst EE)

Ended-↦∈ : ∀ {δE c S}{E : Env δE} (l : c ↦ S ∈ E) (EE : Ended E) → Session.Ended S
Ended-↦∈ ⟨ l R⟩ = Ended-∈D l

infix 0 _⊆_
record _⊆_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor mk
  field
    un-⊆ : ∀ {c S}(NES : ¬(Session.Ended S))(l : c ↦ S ∈ E) → c ↦ S ∈ F
open _⊆_ public

⊆-refl : ∀ {δE}{E : Env δE} → E ⊆ E
un-⊆ ⊆-refl NES l = l

⊆-there : ∀ {δE}{E : Env δE}{c S} → E ⊆ E , c ↦ S
un-⊆ ⊆-there _ = there'

⊆-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ⊆ F → F ⊆ G → E ⊆ G
un-⊆ (⊆-trans p q) NES l = un-⊆ q NES (un-⊆ p NES l)

_⊆-∙_ = ⊆-trans

⊆,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ⊆ F → E , c ↦ S ⊆ F , c ↦ S
un-⊆ (⊆,↦ E∼F) NES  heRe = heRe
un-⊆ (⊆,↦ E∼F) NES (theRe lA) = there' (un-⊆ E∼F NES ⟨ lA R⟩)

⊆,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ⊆ E
un-⊆ ⊆,↦end NES heRe = 𝟘-elim (NES _)
un-⊆ ⊆,↦end NES (theRe lA) = ⟨ lA R⟩

infix 0 _∼_
record _∼_ {δE δF}(E : Env δE)(F : Env δF) : Set₁ where
  constructor ⟨_,_⟩
  field
    get-⊆ : E ⊆ F
    get-⊇ : F ⊆ E
open _∼_ public

∼-refl : ∀ {δE}{E : Env δE} → E ∼ E
∼-refl = ⟨ ⊆-refl , ⊆-refl ⟩

∼-reflexive : ∀ {δE}{E F : Env δE} → E ≡ F → E ∼ F
∼-reflexive refl = ∼-refl

∼-sym : ∀ {δE δF}{E : Env δE}{F : Env δF} → E ∼ F → F ∼ E
∼-sym ⟨ p , q ⟩ = ⟨ q , p ⟩

∼-! = ∼-sym

∼-trans : ∀ {δE δF δG}{E : Env δE}{F : Env δF}{G : Env δG}
          → E ∼ F → F ∼ G → E ∼ G
∼-trans ⟨ p , q ⟩ ⟨ r , s ⟩ = ⟨ p ⊆-∙ r , s ⊆-∙ q ⟩

_∼-∙_ = ∼-trans

∼,↦ : ∀ {δE δF}{E : Env δE}{F : Env δF}{c S}
       → E ∼ F → E , c ↦ S ∼ F , c ↦ S
∼,↦ ⟨ p , q ⟩ = ⟨ ⊆,↦ p , ⊆,↦ q ⟩

∼,↦end : ∀ {δE}{E : Env δE}{c} → E , c ↦ end ∼ E
∼,↦end = ⟨ ⊆,↦end , ⊆-there ⟩

∼-Ended : ∀ {δE}{E : Env δE} → Ended E → ε ∼ E
∼-Ended {E = ε} EE = ∼-refl
∼-Ended {E = E , c ↦ « _ »} ⟨ _ , () ⟩
∼-Ended {E = E , c ↦ end} ⟨ x , _ ⟩ = ∼-Ended x ∼-∙ (∼-! ∼,↦end)

_∼-End_ : ∀ {δE δF}{E : Env δE}{F : Env δF} → Ended E → Ended F → E ∼ F
EE ∼-End EF = ∼-! (∼-Ended EE) ∼-∙ ∼-Ended EF

postulate
  End/₀ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Ended E → Ended (E /₀ σ)
  End/₁ : ∀ {δ}{E : Env δ}(σ : Selection δ) → Ended E → Ended (E /₁ σ)
  End/[_] : ∀ {δ}{E : Env δ}(b : 𝟚)(σ : Selection δ) → Ended E → Ended (E /[ b ] σ)

/*-End : ∀ {δE}(E : Env δE) → Ended (E /*)
/*-End E = mapAll (λ _ → _) E

End/D : ∀ {c δE}(E : Env δE)(l : c ∈D δE) → Ended E → Ended (E /D l)
End/D (E , c ↦ v) here EE = ⟨ (fst EE) , _ ⟩
End/D (E , c₁ ↦ v) (there l) EE = ⟨ (End/D E l (fst EE)) , (snd EE) ⟩

-- Really clever proof yay!
SEnd// :(b : 𝟚)(S : MSession)(σ : 𝟚) → Session.Ended (selectProj (not b) (selectProj b S σ) σ)
SEnd// 1₂ S 1₂ = 0₁
SEnd// 1₂ S 0₂ = 0₁
SEnd// 0₂ S 1₂ = 0₁
SEnd// 0₂ S 0₂ = 0₁

abstract
    -- Really clever proof yay!
    /D/[] : ∀ {c δE}(E : Env δE)(l : c ∈D δE)(b : 𝟚)(σ : Selection δE)
      → (E /D l) /[ b ] σ ∼ (E /[ b ] σ) /D l
    /D/[] (E , c ↦ v) here 1₂ (σ , .c ↦ 1₂) = ∼-refl
    /D/[] (E , c ↦ v) here 1₂ (σ , .c ↦ 0₂) = ∼-refl
    /D/[] (E , c ↦ v) here 0₂ (σ , .c ↦ 1₂) = ∼-refl
    /D/[] (E , c ↦ v) here 0₂ (σ , .c ↦ 0₂) = ∼-refl
    /D/[] (E , c₁ ↦ v) (there l) b (σ , .c₁ ↦ v₁) = ∼,↦ (/D/[] E l b σ)

    End// : ∀ {δE}(b : 𝟚)(E : Env δE)(σ : Selection δE) → Ended ((E /[ b ] σ) /[ not b ] σ)
    End// b ε ε = _
    End// b (E , c ↦ v) (σ , .c ↦ v₁) = ⟨ (End// b E σ) , SEnd// b v v₁ ⟩

    ∼-select-com : ∀ {c δE}(E : Env δE)(σ : Selection δE)(lA : c ∈D δE)
      → let b = not (σ ‼ lA)
        in E /[ b ] σ ∼ (E /D lA) /[ b ] σ
    ∼-select-com (E , c ↦ v) (σ , .c ↦ 1₂) here = ∼-refl
    ∼-select-com (E , c ↦ v) (σ , .c ↦ 0₂) here = ∼-refl
    ∼-select-com (E , c₁ ↦ v) (σ , .c₁ ↦ v₁) (there lA) = ∼,↦ (∼-select-com E σ lA)

    Selection/[]same : ∀ {δ}(Δ : Env δ)(b : 𝟚)
      → Δ /[ b ] (constMap δ b) ∼ Δ
    Selection/[]same ε b = ∼-refl
    Selection/[]same (Δ , c ↦ v) 1₂ = ∼,↦ (Selection/[]same Δ 1₂)
    Selection/[]same (Δ , c ↦ v) 0₂ = ∼,↦ (Selection/[]same Δ 0₂)

    Selection/[]not : ∀ {δ}(Δ : Env δ)(b : 𝟚)
      → Ended (Δ /[ b ] (constMap δ (not b)))
    Selection/[]not ε b = _
    Selection/[]not (Δ , c ↦ v) 1₂ = ⟨ (Selection/[]not Δ 1₂) , _ ⟩
    Selection/[]not (Δ , c ↦ v) 0₂ = ⟨ (Selection/[]not Δ 0₂) , _ ⟩

{-
ZipAll : ∀ {S Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → All S Δ₀ → All S Δ₁ → All S Δ
ZipAll ε A₀ A₁ = 0₁
ZipAll (Z , d ↦₀ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₀
ZipAll (Z , d ↦₁ P₁) (A₀ , p₀) (A₁ , p₁) = ZipAll Z A₀ A₁ , p₁

ZipEnded : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → Ended Δ₀ → Ended Δ₁ → Ended Δ
ZipEnded = ZipAll

Zip-comm : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → [ Δ is Δ₁ ⋎ Δ₀ ]
Zip-comm ε = ε
Zip-comm (Z , d ↦₀ P) = Zip-comm Z , d ↦₁ P
Zip-comm (Z , d ↦₁ P) = Zip-comm Z , d ↦₀ P

Zip-identity : ∀ {Δ₀ Δ₁ Δ} {{Δ₀E : Ended Δ₀}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₁ ≡ Δ
Zip-identity ε = refl
Zip-identity {{E , e}} (Z , d ↦₀ P) = ap₂ (λ Δ P → Δ , d ↦ P) (Zip-identity Z) (! (Ended-≡end e))
Zip-identity {{E , e}} (Z , d ↦₁ P) = ap (λ Δ → Δ , d ↦ P) (Zip-identity Z)

Zip-identity' : ∀ {Δ₀ Δ₁ Δ} {{Δ₁E : Ended Δ₁}} → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ₀ ≡ Δ
Zip-identity' Z = Zip-identity (Zip-comm Z)

module _ {d io M} {P : M → Session} where
    Zip-com∈₀ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ act (com io P) ∈ Δ₀ → d ↦ act (com io P) ∈ Δ
    Zip-com∈₀ (Z , ._ ↦₀ ._) here = here
    Zip-com∈₀ (Z , c ↦₀ Q)  (there l) = there (Zip-com∈₀ Z l)
    Zip-com∈₀ (Z , c ↦₁ Q)  (there l) = there (Zip-com∈₀ Z l)

    Zip-com∈₁ : ∀ {Δ₀ Δ₁ Δ} → [ Δ is Δ₀ ⋎ Δ₁ ] → d ↦ act (com io P) ∈ Δ₁ → d ↦ act (com io P) ∈ Δ
    Zip-com∈₁ Z = Zip-com∈₀ (Zip-comm Z)

    Zip-≔₀ : ∀ {Δ Δ₀ Δ₁}
              (l : d ↦ act (com io P) ∈ Δ₀) {m : M}
              (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
              [ Δ [ Zip-com∈₀ Δₛ l ≔ m ] is Δ₀ [ l ≔ m ] ⋎ Δ₁ ]
    Zip-≔₀ here (Δₛ , ._ ↦₀ ._) = Δₛ , d ↦₀ _
    Zip-≔₀ (there l) (Δₛ , c ↦₀ Q) = Zip-≔₀ l Δₛ , c ↦₀ Q
    Zip-≔₀ (there l) (Δₛ , c ↦₁ Q) = Zip-≔₀ l Δₛ , c ↦₁ Q

    Zip-≔₁ : ∀ {Δ Δ₀ Δ₁}
               (l : d ↦ act (com io P) ∈ Δ₁) {m : M} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) →
             [ Δ [ Zip-com∈₁ Δₛ l ≔ m ] is Δ₀ ⋎ Δ₁ [ l ≔ m ] ]
    Zip-≔₁ l Δₛ = Zip-comm (Zip-≔₀ l (Zip-comm Δₛ))
-- -}
-- -}
-- -}
-- -}
-- -}
