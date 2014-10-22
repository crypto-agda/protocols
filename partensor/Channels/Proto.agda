open import Data.Product
open import Data.Zero
open import Data.Sum

open import Relation.Binary.PropositionalEquality.NP

module partensor.Channels.Proto
  (ℂ : Set) where

data Com : Set where IN OUT : Com

infix 5 _⅋_ _⊗_

mutual
  data Session : Set₁ where
    com : Com → {M : Set} (P : M → Proto) → Session

  data Proto : Set₁ where
    act : (c : ℂ) → Session → Proto
    _⅋_ _⊗_ : Proto → Proto → Proto
    end : Proto
    τ : (c : ℂ) → Proto

pattern send P = com OUT P
pattern recv P = com IN P

mutual
  data DualS : (P Q : Session) → Set₁ where
    ?! : ∀ {M : Set}{F G : M → Proto}
       → (∀ m → Dual (F m) (G m))
       → (∀ m → Dual (G m) (F m))
       → DualS (recv F) (send G)
    !? : ∀ {M : Set}{F G : M → Proto}
       → (∀ m → Dual (F m) (G m))
       → (∀ m → Dual (G m) (F m))
       → DualS (send F) (recv G)

  data Dual : (P Q : Proto) → Set₁ where
    end : Dual end end
    act : ∀ {c P Q}
        → DualS P Q → Dual (act c P) (act c Q)
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
symDual end = end
symDual (act p) = act (symDualS p)
symDual (⊗⅋ x x₁ x₂ x₃) = ⅋⊗ x₁ x x₃ x₂
symDual (⅋⊗ x x₁ x₂ x₃) = ⊗⅋ x₁ x x₃ x₂

infix 4 _∈'_ -- _∈_
data _∈'_ : Proto → Proto → Set₁ where
  here   : ∀ {S} → S ∈' S
  left  : ∀ {P Q S} → S ∈' P → S ∈' (P ⅋ Q)
  right : ∀ {P Q S} → S ∈' Q → S ∈' (P ⅋ Q)

infix 4 _⊆_
data _⊆_ : (Ψ : Proto) → Proto → Set₁ where
  ⊆-in : ∀ {A B Γ} → (A ⊗ B) ∈' Γ → (A ⊗ B) ⊆ Γ

⊆-left : ∀ {P Q Ψ} → Ψ ⊆ P → Ψ ⊆ P ⅋ Q
⊆-left (⊆-in x) = ⊆-in (left x)

infix 6 _/_

_[_≔_]' : {x : Proto}(Δ : Proto) → x ∈' Δ → Proto → Proto
x [ here ≔ S' ]' = S'
(Δ ⅋ Δ₁) [ left l ≔ S' ]' = Δ [ l ≔ S' ]' ⅋ Δ₁
(Δ ⅋ Δ₁) [ right l ≔ S' ]' = Δ ⅋ Δ₁ [ l ≔ S' ]'

_/_ : {x : Proto} (Δ : Proto) → x ⊆ Δ → Proto
Δ / (⊆-in l) = Δ [ l ≔ end ]'

data PEnded : Proto → Set₁ where
  ε : PEnded end
  P⅋ : ∀ {P Q} → PEnded P → PEnded Q → PEnded (P ⅋ Q)

data PEnded' : Proto → Set₁ where
  ε : PEnded' end
  P⅋ : ∀ {P Q} → PEnded' P → PEnded' Q → PEnded' (P ⅋ Q)
  P⊗ : ∀ {P Q} → PEnded' P → PEnded' Q → PEnded' (P ⊗ Q)

_∈_ : ℂ × Session → Proto → Set₁
(c , S) ∈ Γ = act c S ∈' Γ

_[_≔_] : {x : _}(Δ : Proto) → x ∈ Δ → Proto → Proto
Δ [ l ≔ S ] = Δ [ l ≔ S ]'

infix 4 _≈_ _≈'_
infixr 4 _·_

module _ {c S} where
  ∉-PEnd : ∀ {P} → PEnded P → act c S ∈' P → 𝟘
  ∉-PEnd () here
  ∉-PEnd (P⅋ p p₁) (left l) = ∉-PEnd p l
  ∉-PEnd (P⅋ p p₁) (right l) = ∉-PEnd p₁ l

data _≈'_ : Proto → Proto → Set₁ where
  _·_ : ∀ {P Q R} → P ≈' Q → Q ≈' R → P ≈' R
  ⅋-congₗ : ∀ {P P' Q} → P ≈' P' → P ⅋ Q ≈' P' ⅋ Q
  ⅋ε : ∀ {P} → P ⅋ end ≈' P
  ⅋ε' : ∀ {P} → P ≈' P ⅋ end
  ⅋-comm : ∀ {P Q} → P ⅋ Q ≈' Q ⅋ P
  ⅋-assoc : ∀ {P Q R} → (P ⅋ Q) ⅋ R ≈' P ⅋ (Q ⅋ R)

data _≈_ : Proto → Proto → Set₁ where
  _·_ : ∀ {P Q R} → P ≈ Q → Q ≈ R → P ≈ R

  ⅋-congₗ : ∀ {P P' Q} → P ≈ P' → P ⅋ Q ≈ P' ⅋ Q
  ⅋ε : ∀ {P} → P ⅋ end ≈ P
  ⅋ε' : ∀ {P} → P ≈ P ⅋ end
  ⅋-comm : ∀ {P Q} → P ⅋ Q ≈ Q ⅋ P
  ⅋-assoc : ∀ {P Q R} → (P ⅋ Q) ⅋ R ≈ P ⅋ (Q ⅋ R)

  ⊗-congₗ : ∀ {P P' Q} → P ≈ P' → P ⊗ Q ≈ P' ⊗ Q
  ⊗ε : ∀ {P} → P ⊗ end ≈ P
  ⊗ε' : ∀ {P} → P ≈ P ⊗ end
  ⊗-comm : ∀ {P Q} → P ⊗ Q ≈ Q ⊗ P
  ⊗-assoc : ∀ {P Q R} → (P ⊗ Q) ⊗ R ≈ P ⊗ (Q ⊗ R)

→≈' : ∀ {P Q} → P ≈' Q → P ≈ Q
→≈' (x · x₁) = →≈' x · →≈' x₁
→≈' (⅋-congₗ x) = ⅋-congₗ (→≈' x)
→≈' ⅋ε = ⅋ε
→≈' ⅋ε' = ⅋ε'
→≈' ⅋-comm = ⅋-comm
→≈' ⅋-assoc = ⅋-assoc

id'≈ : ∀ {P} → P ≈' P
id'≈ = ⅋ε' · ⅋ε

!'_ : ∀ {P Q} → P ≈' Q → Q ≈' P
!' (e · e₁) = !' e₁ · !' e
!' ⅋-congₗ e = ⅋-congₗ (!' e)
!' ⅋ε = ⅋ε'
!' ⅋ε' = ⅋ε
!' ⅋-comm = ⅋-comm
!' ⅋-assoc = ⅋-comm · ⅋-congₗ ⅋-comm · ⅋-assoc · ⅋-comm · ⅋-congₗ ⅋-comm

!≈_ : ∀ {P Q} → P ≈ Q → Q ≈ P
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

⅋'-congᵣ : ∀ {P P' Q} → P ≈' P' → Q ⅋ P ≈' Q ⅋ P'
⅋'-congᵣ e = ⅋-comm · ⅋-congₗ e · ⅋-comm

⅋'-cong : ∀ {P P' Q Q'} → Q ≈' Q' → P ≈' P' → Q ⅋ P ≈' Q' ⅋ P'
⅋'-cong e e' = ⅋-congₗ e · ⅋'-congᵣ e'

≈'-PEnd : ∀ {P Q} → P ≈' Q → PEnded P → PEnded Q
≈'-PEnd (e · e₁) p = ≈'-PEnd e₁ (≈'-PEnd e p)
≈'-PEnd (⅋-congₗ e) (P⅋ x x₁) = P⅋ (≈'-PEnd e x) x₁
≈'-PEnd ⅋ε (P⅋ x x₁) = x
≈'-PEnd ⅋ε' p = P⅋ p ε
≈'-PEnd ⅋-comm (P⅋ x x₁) = P⅋ x₁ x
≈'-PEnd ⅋-assoc (P⅋ (P⅋ p p₁) p₂) = P⅋ p (P⅋ p₁ p₂)

PEnd-≈' : ∀ {P Q} → PEnded P → PEnded Q → P ≈' Q
PEnd-≈' ε ε = id'≈
PEnd-≈' ε (P⅋ q q₁) = ⅋ε' · ⅋'-cong (PEnd-≈' ε q) (PEnd-≈' ε q₁)
PEnd-≈' (P⅋ p p₁) ε = ⅋'-cong (PEnd-≈' p ε) (PEnd-≈' p₁ ε) · ⅋ε
PEnd-≈' (P⅋ p p₁) (P⅋ q q₁) = ⅋'-cong (PEnd-≈' p q) (PEnd-≈' p₁ q₁)


⊈-PEnd : ∀ {P Q} → PEnded Q → P ⊆ Q → 𝟘
⊈-PEnd ε (⊆-in ())
⊈-PEnd (P⅋ p p₁) (⊆-in (left x)) = ⊈-PEnd p (⊆-in x)
⊈-PEnd (P⅋ p p₁) (⊆-in (right x)) = ⊈-PEnd p₁ (⊆-in x)


data NotPar : Proto → Set₁ where
  act : ∀ {c S} → NotPar (act c S)
  ten : ∀ {A B} → NotPar (A ⊗ B)
  τ : ∀ {c} → NotPar (τ c)

≔-same : ∀ {P Q}(l : P ∈' Q) → Q ≈' Q [ l ≔ P ]'
≔-same here = id'≈
≔-same (left x) = ⅋-congₗ (≔-same x)
≔-same (right x) = ⅋'-congᵣ (≔-same x)

⅋≔ : ∀ {P Q R}(l : P ∈' Q) → Q [ l ≔ R ]' ≈' Q [ l ≔ end ]' ⅋ R
⅋≔ here = ⅋ε' · ⅋-comm
⅋≔ (left l) = ⅋-congₗ (⅋≔ l) · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc
⅋≔ (right l) = ⅋'-congᵣ (⅋≔ l) · !' ⅋-assoc

≔-≈ : ∀ {P Q S S'}(l : P ∈' Q) → S ≈' S' → Q [ l ≔ S ]' ≈' Q [ l ≔ S' ]'
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

⊆-conv : ∀ {P Q Γ} → P ≈' Q → Γ ⊆ P → Γ ⊆ Q
⊆-conv e (⊆-in x) = ⊆-in (∈'-conv ten e x)

/-conv : ∀ {P Q Γ}(e : P ≈' Q)(l : Γ ⊆ P) → P / l ≈' Q / ⊆-conv e l
/-conv e (⊆-in x) = ≔'-conv ten e x

module _ {S} where
  ∈-conv : ∀ {P Q} → P ≈' Q → S ∈ P → S ∈ Q
  ∈-conv e l = ∈'-conv act e l

  ≔-conv : ∀ {P Q S'}(e : P ≈' Q)(l : S ∈ P) → P [ l ≔ S' ] ≈' Q [ ∈-conv e l ≔ S' ]
  ≔-conv e l = ≔'-conv act e l

same-var : ∀ {Δ Γ Γ'}(np : NotPar Γ)(np' : NotPar Γ')(l : Γ ∈' Δ)(l' : Γ' ∈' Δ) →
  (∃ λ (nl : ∀ {S'} → Γ ∈' Δ [ l' ≔ S' ]')
  → ∃ λ (nl' : ∀ {S} → Γ' ∈' Δ [ l ≔ S ]')
  → ∀ {S S'} → ((Δ [ l' ≔ S' ]') [ nl ≔ S ]') ≈' (Δ [ l ≔ S ]') [ nl' ≔ S' ]')
  ⊎ ∃ λ (p : Γ ≡ Γ') → tr _ p l ≡ l'
same-var np np' here here = inj₂ (refl , refl)
same-var () np' here (left l')
same-var () np' here (right l')
same-var np () (left l) here
same-var np np' (left l) (left l') with same-var np np' l l'
same-var np np' (left l) (left l') | inj₁ (nl , nl' , s)
  = inj₁ (left nl , left nl' , ⅋-congₗ s)
same-var np np' (left l) (left .l) | inj₂ (refl , refl) = inj₂ (refl , refl)
same-var np np' (left l) (right l') = inj₁ (left l , right l' , id'≈)
same-var np () (right l) here
same-var np np' (right l) (left l') = inj₁ (right l , left l' , id'≈)
same-var np np' (right l) (right l') with same-var np np' l l'
same-var np np' (right l) (right l') | inj₁ (nl , nl' , s)
  = inj₁ (right nl , right nl' , ⅋'-congᵣ s)
same-var np np' (right l) (right .l) | inj₂ (refl , refl) = inj₂ (refl , refl)

same-⊗var : ∀ {Δ Γ Γ'}(l : Γ ⊆ Δ)(l' : Γ' ⊆ Δ) →
  (∃ λ (nl : Γ ⊆ Δ / l') → ∃ λ (nl' : Γ' ⊆ Δ / l) → (Δ / l') / nl ≈' (Δ / l) / nl') ⊎ ∃ λ (p : Γ ≡ Γ') → tr _ p l ≡ l'
same-⊗var (⊆-in l) (⊆-in l') with same-var ten ten l l'
same-⊗var (⊆-in l) (⊆-in l') | inj₁ (nl , nl' , s) = inj₁ (⊆-in nl , ⊆-in nl' , s)
same-⊗var (⊆-in l) (⊆-in .l) | inj₂ (refl , refl) = inj₂ (refl , refl)


∈'-≔' : ∀ {Δ Γ Γ' S}(l : Γ ∈' Δ) → Γ' ∈' Δ → NotPar Γ → NotPar Γ'
  → Γ ≢ Γ' → Γ' ∈' Δ [ l ≔ S ]'
∈'-≔' here here np np' e = 𝟘-elim (e refl)
∈'-≔' (left l) here np () e
∈'-≔' (right l) here np () e
∈'-≔' here (left l') () np' e
∈'-≔' (left l) (left l') np np' e = left (∈'-≔' l l' np np' e)
∈'-≔' (right l) (left l') np np' e = left l'
∈'-≔' here (right l') () np' e
∈'-≔' (left l) (right l') np np' e = right l'
∈'-≔' (right l) (right l') np np' e = right (∈'-≔' l l' np np' e)

≔'-swap : ∀ {Δ Γ Γ' M M'}(l : Γ ∈' Δ)(l' : Γ' ∈' Δ)
    (np : NotPar Γ)(np' : NotPar Γ')(e : Γ ≢ Γ')(e' : Γ' ≢ Γ)
  → (Δ [ l' ≔ M' ]') [ ∈'-≔' l' l np' np e' ≔ M ]'
  ≈' (Δ [ l ≔ M ]') [ ∈'-≔' l l' np np' e ≔ M' ]'
≔'-swap here here np np' e e' = 𝟘-elim (e refl)
≔'-swap here (left l') () np' e e'
≔'-swap here (right l') () np' e e'
≔'-swap (left l) here np () e e'
≔'-swap (left l) (left l') np np' e e' = ⅋-congₗ (≔'-swap l l' np np' e e')
≔'-swap (left l) (right l') np np' e e' = id'≈
≔'-swap (right l) here np () e e'
≔'-swap (right l) (left l') np np' e e' = id'≈
≔'-swap (right l) (right l') np np' e e' = ⅋'-congᵣ (≔'-swap l l' np np' e e')

module _ {S} where
  ∈-/ : ∀ {Δ Γ}(l : Γ ⊆ Δ) → S ∈ Δ → S ∈ (Δ / l)
  ∈-/ (⊆-in l) l' = ∈'-≔' l l' ten act (λ ())

  ⊆-≔ : ∀ {Γ Δ M} → Γ ⊆ Δ → (l : S ∈ Δ) → Γ ⊆ Δ [ l ≔ M ]
  ⊆-≔ (⊆-in l) l' = ⊆-in (∈'-≔' l' l act ten (λ ()))

  ≔/ : ∀ {Γ Δ M}(l : Γ ⊆ Δ)(v : S ∈ Δ) → Δ [ v ≔ M ] / ⊆-≔ l v ≈' (Δ / l) [ ∈-/ l v ≔ M ]
  ≔/ (⊆-in l) l' = ≔'-swap l l' ten act (λ ()) (λ ())

in-sub : ∀ {Γ Γ' Δ}(l : Γ ∈' Δ) → Γ' ∈' Δ [ l ≔ Γ' ]'
in-sub here = here
in-sub (left x) = left (in-sub x)
in-sub (right x) = right (in-sub x)

sub-twice : ∀ {Γ Γ' Γ'' Δ}(l : Γ ∈' Δ) →
  (Δ [ l ≔ Γ' ]') [ in-sub l ≔ Γ'' ]'
  ≈' Δ [ l ≔ Γ'' ]'
sub-twice here = id'≈
sub-twice (left x) = ⅋-congₗ (sub-twice x)
sub-twice (right x) = ⅋'-congᵣ (sub-twice x)

act≠⊗ : ∀ {c S A B} → act c S ≢ A ⊗ B
act≠⊗ ()

⊗≠act : ∀ {c S A B} → A ⊗ B ≢ act c S
⊗≠act ()

∈⅋-fst : ∀ {P Q R} → (P ⅋ Q) ∈' R → P ∈' R
∈⅋-fst here = left here
∈⅋-fst (left x) = left (∈⅋-fst x)
∈⅋-fst (right x) = right (∈⅋-fst x)

∈⅋-snd : ∀ {P Q R S} → (l : (P ⅋ Q) ∈' R) → Q ∈' R [ ∈⅋-fst l ≔ S ]'
∈⅋-snd here = right here
∈⅋-snd (left x) = left (∈⅋-snd x)
∈⅋-snd (right x) = right (∈⅋-snd x)

∈⅋-≔ : ∀ {P Q R S S'}(l : (P ⅋ Q) ∈' R) →
  (R [ ∈⅋-fst l ≔  S ]') [ ∈⅋-snd l ≔ S' ]' ≈' R [ l ≔ S ⅋ S' ]'
∈⅋-≔ here = id'≈
∈⅋-≔ (left l) = ⅋-congₗ (∈⅋-≔ l)
∈⅋-≔ (right l) = ⅋'-congᵣ (∈⅋-≔ l)


∉-End-np : ∀ {Γ Δ} → NotPar Γ → PEnded Δ → Γ ∈' Δ → 𝟘
∉-End-np () ε here
∉-End-np () (P⅋ e e₁) here
∉-End-np np (P⅋ e e₁) (left l) = ∉-End-np np e l
∉-End-np np (P⅋ e e₁) (right l) = ∉-End-np np e₁ l

np-par : ∀ {P Q} → NotPar (P ⅋ Q) → 𝟘
np-par ()
