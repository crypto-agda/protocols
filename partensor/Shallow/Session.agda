open import Data.Zero
open import Data.One
open import Relation.Binary.PropositionalEquality.NP

module partensor.Shallow.Session where

data Com : Set where IN OUT : Com

infix 5 _⅋_ _⊗_

mutual
  data Action : Set₁ where
    com : Com → {M : Set} (P : M → Session) → Action

  data Session : Set₁ where
    act : Action → Session
    _⅋_ _⊗_ : Session → Session → Session
    𝟙' ⊥' : Session

pattern send {M} P = com OUT {M} P
pattern recv {M} P = com IN {M} P

mutual
  data DualS : (P Q : Action) → Set₁ where
    ?! : ∀ {M : Set}{F G : M → Session}
       → (∀ m → Dual (F m) (G m))
       → (∀ m → Dual (G m) (F m))
       → DualS (recv F) (send G)
    !? : ∀ {M : Set}{F G : M → Session}
       → (∀ m → Dual (F m) (G m))
       → (∀ m → Dual (G m) (F m))
       → DualS (send F) (recv G)

  data Dual : (P Q : Session) → Set₁ where
    -- end : Dual end end
    𝟙⊥ : Dual 𝟙' ⊥'
    ⊥𝟙 : Dual ⊥' 𝟙'
    act : ∀ {P Q}
        → DualS P Q → Dual (act P) (act Q)
    ⊗⅋ : ∀ {A A' B B'}
       → Dual A A' → Dual A' A
       → Dual B B' → Dual B' B
       → Dual (A ⊗ B) (A' ⅋ B')
    ⅋⊗ : ∀ {A A' B B'}
       → Dual A A' → Dual A' A
       → Dual B B' → Dual B' B
       → Dual (A ⅋ B) (A' ⊗ B')

symDualS : ∀ {P Q} → DualS P Q → DualS Q P
symDualS (?! x x₁) = !? x₁ x
symDualS (!? x x₁) = ?! x₁ x

symDual : ∀ {P Q} → Dual P Q → Dual Q P
symDual 𝟙⊥ = ⊥𝟙
symDual ⊥𝟙 = 𝟙⊥
symDual (act p) = act (symDualS p)
symDual (⊗⅋ x x₁ x₂ x₃) = ⅋⊗ x₁ x x₃ x₂
symDual (⅋⊗ x x₁ x₂ x₃) = ⊗⅋ x₁ x x₃ x₂

data MSession : Set₁ where
  «_» : (S : Session) → MSession
  end : MSession

Ended : MSession → Set
Ended end = 𝟙
Ended _   = 𝟘

Ended-≡end : ∀ {P} → Ended P → P ≡ end
Ended-≡end {« _ »} ()
Ended-≡end {end} p = refl

{-
data NotPar : Proto → Set₁ where
  act : ∀ {c S} → NotPar (act c S)
  ten : ∀ {A B} → NotPar (⊗ A B)
  τ : ∀ {c} → NotPar (τ c)

np-par : ∀ {P Q} → NotPar (⅋ P Q) → 𝟘
np-par ()

infix 4 _∈'_ -- _∈_
data _∈'_ : Proto → Proto → Set₁ where
  here   : ∀ {S} → S ∈' S
  left  : ∀ {P Q S} → S ∈' P → S ∈' (⅋ P Q)
  right : ∀ {P Q S} → S ∈' Q → S ∈' (⅋ P Q)


_[_≔_]' : ∀{x : Proto}(Δ : Proto) → x ∈' Δ → Proto → Proto
x [ here ≔ S' ]' = S'
(⅋ Δ Δ₁) [ left  l ≔ S' ]' = ⅋ (Δ [ l ≔ S' ]') Δ₁
(⅋ Δ Δ₁) [ right l ≔ S' ]' = ⅋ Δ (Δ₁ [ l ≔ S' ]')

infix 6 _/_
_/_ : ∀ {x : Proto} (Δ : Proto) → x ∈' Δ → Proto
Δ / l = Δ [ l ≔ end ]'

data PEnded : Proto → Set₁ where
  ε : PEnded end
  P⅋ : ∀ {P Q} → PEnded P → PEnded Q
    → PEnded (⅋ P Q)

data PEnded' : Proto → Set₁ where
  ε : PEnded' end
  P⅋ : ∀ {P Q} → PEnded' P → PEnded' Q
    → PEnded' (⅋ P Q)
  P⊗ : ∀ {P Q} → PEnded' P → PEnded' Q
    → PEnded' (⊗ P Q)

_∈_ : ℂ × Session → Proto → Set₁
(c , S) ∈ Γ = act c S ∈' Γ

_[_≔_] : ∀ {x : _ × Session}(Δ : Proto) → x ∈ Δ → Proto → Proto
Δ [ l ≔ S ] = Δ [ l ≔ S ]'

∉-End-np : ∀ {Γ Δ} → NotPar Γ → PEnded Δ → Γ ∈' Δ → 𝟘
∉-End-np () ε here
∉-End-np () (P⅋ e e₁) here
∉-End-np np (P⅋ e e₁) (left l) = ∉-End-np np e l
∉-End-np np (P⅋ e e₁) (right l) = ∉-End-np np e₁ l

infix 4 _≈'_ -- _≈_
infixr 4 _·_
data _≈'_ : Proto → Proto → Set₁ where
  _·_ : ∀ {P Q R} → P ≈' Q → Q ≈' R → P ≈' R
  ⅋-congₗ : ∀ {P P' Q}
    → P ≈' P' → ⅋ P Q ≈' ⅋ P' Q
  ⅋ε : ∀ {P} → ⅋ P end ≈' P
  ⅋ε' : ∀ {P} → P ≈' ⅋ P end
  ⅋-comm : ∀ {P Q} → ⅋ P Q ≈' ⅋ Q P
  ⅋-assoc : ∀ {P Q R}
    → ⅋ (⅋ P Q) R ≈' ⅋ P (⅋ Q R)

data _≈_ : Proto → Proto → Set₁ where
  _·_ : ∀ {P Q R} → P ≈ Q → Q ≈ R → P ≈ R

  ⅋-congₗ : ∀ {P P' Q} → P ≈ P' → ⅋ P Q ≈ ⅋ P' Q
  ⅋ε : ∀ {P} → ⅋ P end ≈ P
  ⅋ε' : ∀ {P} → P ≈ ⅋ P end
  ⅋-comm : ∀ {P Q} → ⅋ P Q ≈ ⅋ Q P
  ⅋-assoc : ∀ {P Q R} → ⅋ (⅋ P Q) R ≈ ⅋ P (⅋ Q R)

  ⊗-congₗ : ∀ {P P' Q} → P ≈ P' → ⊗ P Q ≈ ⊗ P' Q
  ⊗ε : ∀ {P} → ⊗ P end ≈ P
  ⊗ε' : ∀ {P} → P ≈ ⊗ P end
  ⊗-comm : ∀ {P Q} → ⊗ P Q ≈ ⊗ Q P
  ⊗-assoc : ∀ {P Q R} → ⊗ (⊗ P Q) R ≈ ⊗ P (⊗ Q R)

→≈' : ∀ {P Q : Proto} → P ≈' Q → P ≈ Q
→≈' (x · x₁) = →≈' x · →≈' x₁
→≈' (⅋-congₗ x) = ⅋-congₗ (→≈' x)
→≈' ⅋ε = ⅋ε
→≈' ⅋ε' = ⅋ε'
→≈' ⅋-comm = ⅋-comm
→≈' ⅋-assoc = ⅋-assoc

id'≈ : ∀ {P : Proto} → P ≈' P
id'≈ = ⅋ε' · ⅋ε

!'_ : ∀ {P Q : Proto} → P ≈' Q → Q ≈' P
!' (e · e₁) = !' e₁ · !' e
!' ⅋-congₗ e = ⅋-congₗ (!' e)
!' ⅋ε = ⅋ε'
!' ⅋ε' = ⅋ε
!' ⅋-comm = ⅋-comm
!' ⅋-assoc = ⅋-comm · ⅋-congₗ ⅋-comm
            · ⅋-assoc
            · ⅋-comm · ⅋-congₗ ⅋-comm

{-
!≈_ : ∀ {φ}{P Q : Proto φ} → P ≈ Q → Q ≈ P
!≈ (e · e₁) = !≈ e₁ · !≈ e
!≈ ⅋-congₗ e = ⅋-congₗ (!≈ e)
!≈ ⅋ε = ⅋ε'
!≈ ⅋ε' = ⅋ε
!≈ ⅋-comm = ⅋-comm
!≈ ⅋-assoc = ⅋-comm · ⅋-congₗ ⅋-comm · ⅋-assoc · ⅋-comm · ⅋-congₗ ⅋-comm
!≈ ⊗-congₗ e = ⊗-congₗ (!≈ e)
!≈ ⊗ε = ⊗ε'
!≈ ⊗ε' = ⊗ε
!≈ ⊗-comm = ⊗-comm
!≈ ⊗-assoc = ⊗-comm · ⊗-congₗ ⊗-comm · ⊗-assoc · ⊗-comm · ⊗-congₗ ⊗-comm
-}

⅋'-congᵣ : ∀ {P P' Q} → P ≈' P'
  → ⅋ Q P ≈' ⅋ Q P'
⅋'-congᵣ e = ⅋-comm · ⅋-congₗ e · ⅋-comm

⅋'-cong : ∀ {P P' Q Q'} → Q ≈' Q' → P ≈' P'
  → ⅋ Q P ≈' ⅋ Q' P'
⅋'-cong e e' = ⅋-congₗ e · ⅋'-congᵣ e'

≈'-PEnd : ∀ {P Q} → P ≈' Q → PEnded P → PEnded Q
≈'-PEnd (e · e₁) p = ≈'-PEnd e₁ (≈'-PEnd e p)
≈'-PEnd (⅋-congₗ e) (P⅋ x x₁) = P⅋ (≈'-PEnd e x) x₁
≈'-PEnd ⅋ε (P⅋ x x₁) = x
≈'-PEnd ⅋ε' p = P⅋ p ε
≈'-PEnd ⅋-comm (P⅋ x x₁) = P⅋ x₁ x
≈'-PEnd ⅋-assoc (P⅋ (P⅋ p p₁) p₂) = P⅋ p (P⅋ p₁ p₂)

PEnd-≈end : ∀ {P} → PEnded P → P ≈' end
PEnd-≈end ε = id'≈
PEnd-≈end (P⅋ p p₁) = ⅋'-cong (PEnd-≈end p) (PEnd-≈end p₁) · ⅋ε

PEnd-≈' : ∀ {P Q} → PEnded P → PEnded Q → P ≈' Q
PEnd-≈' p q = PEnd-≈end p · !' PEnd-≈end q

≔-same : ∀ {P Q}(l : P ∈' Q) → Q ≈' Q [ l ≔ P ]'
≔-same here = id'≈
≔-same (left x) = ⅋-congₗ (≔-same x)
≔-same (right x) = ⅋'-congᵣ (≔-same x)

⅋≔ : ∀ {P R Q : Proto}(l : P ∈' Q) → Q [ l ≔ R ]' ≈' ⅋ (Q [ l ≔ end ]') R
⅋≔ here = ⅋ε' · ⅋-comm
⅋≔ (left l) = ⅋-congₗ (⅋≔ l) · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc
⅋≔ (right l) = ⅋'-congᵣ (⅋≔ l) · !' ⅋-assoc

⅋≔⅋ : ∀ {P R R' Q : Proto}(l : P ∈' Q) → Q [ l ≔ ⅋ R R' ]' ≈' ⅋ (Q [ l ≔ R ]') R'
⅋≔⅋ l = ⅋≔ l · !' ⅋-assoc · !' ⅋-congₗ (⅋≔ l)

private
    ≔-≈ : ∀ {P Q S S'}(l : P ∈' Q) → S ≈' S'
      → Q [ l ≔ S ]' ≈' Q [ l ≔ S' ]'
    ≔-≈ here eq = eq
    ≔-≈ (left x) eq = ⅋-congₗ (≔-≈ x eq)
    ≔-≈ (right x) eq = ⅋'-congᵣ (≔-≈ x eq)

∈'-conv : ∀ {P Q Γ} → NotPar Γ → P ≈' Q → Γ ∈' P → Γ ∈' Q
∈'-conv np (e · e₁) l = ∈'-conv np e₁ (∈'-conv np e l)
∈'-conv () (⅋-congₗ e) here
∈'-conv np (⅋-congₗ e) (left l) = left (∈'-conv np e l)
∈'-conv np (⅋-congₗ e) (right l) = right l
∈'-conv () ⅋ε here
∈'-conv np ⅋ε (left l) = l
∈'-conv () ⅋ε (right here)
∈'-conv np ⅋ε' l = left l
∈'-conv () ⅋-comm here
∈'-conv np ⅋-comm (left l) = right l
∈'-conv np ⅋-comm (right l) = left l
∈'-conv () ⅋-assoc here
∈'-conv () ⅋-assoc (left here)
∈'-conv np ⅋-assoc (left (left l)) = left l
∈'-conv np ⅋-assoc (left (right l)) = right (left l)
∈'-conv np ⅋-assoc (right l) = right (right l)

≔'-conv : ∀ {P Q Γ S'}(np : NotPar Γ)(e : P ≈' Q)(l : Γ ∈' P)
  → P [ l ≔ S' ]' ≈' Q [ ∈'-conv np e l ≔ S' ]'
≔'-conv np (e · e₁) l = ≔'-conv np e l · ≔'-conv np e₁ _
≔'-conv () (⅋-congₗ e) here
≔'-conv np (⅋-congₗ e) (left l) = ⅋-congₗ (≔'-conv np e l)
≔'-conv np (⅋-congₗ e) (right l) = ⅋-congₗ e
≔'-conv () ⅋ε here
≔'-conv np ⅋ε (left l) = ⅋ε
≔'-conv () ⅋ε (right here)
≔'-conv np ⅋ε' l = ⅋ε'
≔'-conv () ⅋-comm here
≔'-conv np ⅋-comm (left l) = ⅋-comm
≔'-conv np ⅋-comm (right l) = ⅋-comm
≔'-conv () ⅋-assoc here
≔'-conv () ⅋-assoc (left here)
≔'-conv np ⅋-assoc (left (left l)) = ⅋-assoc
≔'-conv np ⅋-assoc (left (right l)) = ⅋-assoc
≔'-conv np ⅋-assoc (right l) = ⅋-assoc

module _ where

  np-irr : ∀ {Δ} → (np np' : NotPar Δ) → np ≡ np'
  np-irr act act = refl
  np-irr ten ten = refl
  np-irr τ τ = refl

  module _ {Γ Γ' : Proto} where
    _∋_#_ : ∀ Δ (l : Γ ∈' Δ)(l' : Γ' ∈' Δ) → Set₁
    Δ ∋ l # l' = ∃ λ (nl : ∀ {S'} → Γ ∈' Δ [ l' ≔ S' ]' ) →
                 ∃ λ (nl' : ∀ {S} → Γ' ∈' Δ [ l ≔ S ]' ) →
                 ∀ {S S'} → Δ [ l' ≔ S' ]' [ nl ≔ S ]'
                         ≈' Δ [ l ≔ S ]' [ nl' ≔ S' ]'

  ∋#-left : ∀ {Γ Γ' Δ Δ' : Proto}(l : Γ ∈' Δ)(l' : Γ' ∈' Δ)
    → Δ ∋ l # l' → (⅋ Δ Δ') ∋ left l # left l'
  ∋#-left l l' (nl , nl' , s) = (left nl , left nl' , ⅋-congₗ s)

  ∋#-right : ∀ {Γ Γ' Δ Δ' : Proto}(l : Γ ∈' Δ)(l' : Γ' ∈' Δ)
    → Δ ∋ l # l' → (⅋ Δ' Δ) ∋ right l # right l'
  ∋#-right l l' (nl , nl' , s) = (right nl , right nl' , ⅋'-congᵣ s)

  data Same-Var? {Γ} Δ (l : Γ ∈' Δ)(np : NotPar Γ) : ∀ {Γ'} → (l : Γ' ∈' Δ)(np' : NotPar Γ') → Set₁ where
    yes : Same-Var? Δ l np l np
    no : ∀ {Γ l' np'} → Δ ∋ l # l' → Same-Var? Δ l np {Γ} l' np'

  same-var? : ∀ {Δ Γ Γ'}(np : NotPar Γ)(np' : NotPar Γ')(l : Γ ∈' Δ)(l' : Γ' ∈' Δ) → Same-Var? Δ l np l' np'
  same-var? np np' here here rewrite np-irr np np' = yes
  same-var? np np' (left l) (left l') with same-var? np np' l l'
  same-var? np .np (left l') (left .l') | yes = yes
  same-var? np np' (left l) (left l') | no x = no (∋#-left l l' x)
  same-var? np np' (left l) (right l') = no (left l , right l' , id'≈)
  same-var? np np' (right l) (left l') = no (right l , left l' , id'≈)
  same-var? np np' (right l) (right l') with same-var? np np' l l'
  same-var? np .np (right l') (right .l') | yes = yes
  same-var? np np' (right l) (right l') | no x = no (∋#-right l l' x)

  same-var? () np' here (left l')
  same-var? () np' here (right l')
  same-var? np () (left l) here
  same-var? np () (right l) here

in-sub : ∀ {Γ Γ' Δ : Proto}(l : Γ ∈' Δ) → Γ' ∈' Δ [ l ≔ Γ' ]'
in-sub here = here
in-sub (left x) = left (in-sub x)
in-sub (right x) = right (in-sub x)

sub-twice : ∀ {Γ Γ' Γ'' Δ : Proto}(l : Γ ∈' Δ) →
  (Δ [ l ≔ Γ' ]') [ in-sub l ≔ Γ'' ]'
  ≈' Δ [ l ≔ Γ'' ]'
sub-twice here = id'≈
sub-twice (left x) = ⅋-congₗ (sub-twice x)
sub-twice (right x) = ⅋'-congᵣ (sub-twice x)

∈⅋-fst : ∀ {P Q R : Proto} → (l : (⅋ P Q) ∈' R) → P ∈' R
∈⅋-fst here = left here
∈⅋-fst (left x) = left (∈⅋-fst x)
∈⅋-fst (right x) = right (∈⅋-fst x)

∈⅋-snd : ∀ {P Q R S : Proto} → (l : (⅋ P Q) ∈' R) → Q ∈' R [ ∈⅋-fst l ≔ S ]'
∈⅋-snd here = right here
∈⅋-snd (left x) = left (∈⅋-snd x)
∈⅋-snd (right x) = right (∈⅋-snd x)

∈⅋-≔ : ∀ {P Q R S S' : Proto}(l : (⅋ P Q) ∈' R) →
  (R [ ∈⅋-fst l ≔  S ]') [ ∈⅋-snd l ≔ S' ]' ≈' R [ l ≔ ⅋ S S' ]'
∈⅋-≔ here = id'≈
∈⅋-≔ (left l) = ⅋-congₗ (∈⅋-≔ l)
∈⅋-≔ (right l) = ⅋'-congᵣ (∈⅋-≔ l)



-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
