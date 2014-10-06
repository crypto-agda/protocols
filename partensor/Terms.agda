open import Function using (_∘_ ; id ; const ; flip)
open import Data.Zero
open import Data.One
open import Data.Two
open import Data.Nat.NP
open import Data.List
open import Data.Product using (_,_ ; Σ ; ∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
  renaming (map to smap ; [_,_] to either ; [_,_]′ to either′)

open import Level
open import Size

open import Relation.Binary.PropositionalEquality.NP using (_≡_ ; refl ; !_ ; ap ; tr ; _∙_ ; _≢_)

module partensor.Terms where

data Com : Set where IN OUT : Com

data Session : Set₁ where
  end : Session
  com : Com → {M : Set} (P : M → Session) → Session

data Ended : Session → Set₁ where
  end : Ended end

pattern send P = com OUT P
pattern recv P = com IN P

mapSession : (Com → Com) → Session → Session
mapSession f end = end
mapSession f (com c P) = com (f c) (λ m → mapSession f (P m))

dualC : Com → Com
dualC IN = OUT
dualC OUT = IN

dual : Session → Session
dual = mapSession dualC

infix 5 _⅋_ _⊗_
data Proto : Set₁ where
  act : Session → Proto
  _⅋_ _⊗_ : Proto → Proto → Proto

dual' : Proto → Proto
dual' (act x) = act (dual x)
dual' (P ⅋ P₁) = dual' P ⊗ dual' P₁
dual' (P ⊗ P₁) = dual' P ⅋ dual' P₁

data Dual : (P Q : Proto) → Set₁ where
  act  : ∀ {P} → Dual (act P) (act (dual P))
  act' : ∀ {P} → Dual (act (dual P)) (act P)
  ⊗⅋ : ∀ {A A' B B'}
     → Dual A A' → Dual A' A
     → Dual B B' → Dual B' B
     → Dual (A ⊗ B) (A' ⅋ B')
  ⅋⊗ : ∀ {A A' B B'}
     → Dual A A' → Dual A' A
     → Dual B B' → Dual B' B
     → Dual (A ⅋ B) (A' ⊗ B')

symDual : ∀ {P Q} → Dual P Q → Dual Q P
symDual act = act'
symDual act' = act
symDual (⊗⅋ x x₁ x₂ x₃) = ⅋⊗ x₁ x x₃ x₂
symDual (⅋⊗ x x₁ x₂ x₃) = ⊗⅋ x₁ x x₃ x₂

mkDual : ∀ P → Dual P (dual' P)
mkDual (act x) = act
mkDual (P ⅋ P₁) = ⅋⊗ (mkDual P) (symDual (mkDual P)) (mkDual P₁) (symDual (mkDual P₁))
mkDual (P ⊗ P₁) = ⊗⅋ (mkDual P) (symDual (mkDual P)) (mkDual P₁) (symDual (mkDual P₁))

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
Δ / (⊆-in l) = Δ [ l ≔ act end ]'

data PEnded : Proto → Set₁ where
  ε : PEnded (act end)
  P⅋ : ∀ {P Q} → PEnded P → PEnded Q → PEnded (P ⅋ Q)

data PEnded' : Proto → Set₁ where
  ε : PEnded' (act end)
  P⅋ : ∀ {P Q} → PEnded' P → PEnded' Q → PEnded' (P ⅋ Q)
  P⊗ : ∀ {P Q} → PEnded' P → PEnded' Q → PEnded' (P ⊗ Q)

_∈_ : Session → Proto → Set₁
S ∈ Γ = act S ∈' Γ


_[_≔_] : {x : Session}(Δ : Proto) → x ∈ Δ → Session → Proto
Δ [ l ≔ S ] = Δ [ l ≔ act S ]'

infix 4 _≈_ _≈'_
infixr 4 _·_

module _ {x M P}(let S = com x {M} P) where
  ∉-PEnd : ∀ {P} → PEnded P → act S ∈' P → 𝟘
  ∉-PEnd () here
  ∉-PEnd (P⅋ p p₁) (left l) = ∉-PEnd p l
  ∉-PEnd (P⅋ p p₁) (right l) = ∉-PEnd p₁ l

data _≈'_ : Proto → Proto → Set₁ where
  _·_ : ∀ {P Q R} → P ≈' Q → Q ≈' R → P ≈' R
  ⅋-congₗ : ∀ {P P' Q} → P ≈' P' → P ⅋ Q ≈' P' ⅋ Q
  ⅋ε : ∀ {P} → P ⅋ act end ≈' P
  ⅋ε' : ∀ {P} → P ≈' P ⅋ act end
  ⅋-comm : ∀ {P Q} → P ⅋ Q ≈' Q ⅋ P
  ⅋-assoc : ∀ {P Q R} → (P ⅋ Q) ⅋ R ≈' P ⅋ (Q ⅋ R)

data _≈_ : Proto → Proto → Set₁ where
  _·_ : ∀ {P Q R} → P ≈ Q → Q ≈ R → P ≈ R

  ⅋-congₗ : ∀ {P P' Q} → P ≈ P' → P ⅋ Q ≈ P' ⅋ Q
  ⅋ε : ∀ {P} → P ⅋ act end ≈ P
  ⅋ε' : ∀ {P} → P ≈ P ⅋ act end
  ⅋-comm : ∀ {P Q} → P ⅋ Q ≈ Q ⅋ P
  ⅋-assoc : ∀ {P Q R} → (P ⅋ Q) ⅋ R ≈ P ⅋ (Q ⅋ R)

  ⊗-congₗ : ∀ {P P' Q} → P ≈ P' → P ⊗ Q ≈ P' ⊗ Q
  ⊗ε : ∀ {P} → P ⊗ act end ≈ P
  ⊗ε' : ∀ {P} → P ≈ P ⊗ act end
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

data ⟪_⟫ (Δ : Proto) : Set₁ where
  end : PEnded Δ → ⟪ Δ ⟫

  input : ∀ {M P} (l : recv P ∈ Δ)
    → ((m : M) → ⟪ Δ [ l ≔ P m ] ⟫)
    → ⟪ Δ ⟫

  output : ∀ {M P} (l : send P ∈ Δ)
    → (m : M) → ⟪ Δ [ l ≔ P m ] ⟫
    → ⟪ Δ ⟫

  pair : ∀ {Γ Γ' A B}
    → (l : A ⊗ B ⊆ Δ) → (Δ / l) ≈' (Γ ⅋ Γ')
    → ⟪ Γ ⅋ A ⟫ → ⟪ Γ' ⅋ B ⟫
    → ⟪ Δ ⟫


data NotParEnd : Proto → Set₁ where
  act : ∀ {x M P} → NotParEnd (act (com x {M} P))
  ten : ∀ {A B} → NotParEnd (A ⊗ B)

data NotPar : Proto → Set₁ where
  act : ∀ {S} → NotPar (act S)
  ten : ∀ {A B} → NotPar (A ⊗ B)

≔-same : ∀ {P Q}(l : P ∈' Q) → Q ≈' Q [ l ≔ P ]'
≔-same here = id'≈
≔-same (left x) = ⅋-congₗ (≔-same x)
≔-same (right x) = ⅋'-congᵣ (≔-same x)

⅋≔ : ∀ {P Q R}(l : P ∈' Q) → Q [ l ≔ R ]' ≈' Q [ l ≔ act end ]' ⅋ R
⅋≔ here = ⅋ε' · ⅋-comm
⅋≔ (left l) = ⅋-congₗ (⅋≔ l) · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc
⅋≔ (right l) = ⅋'-congᵣ (⅋≔ l) · !' ⅋-assoc

∈'-conv : ∀ {P Q Γ} → NotParEnd Γ → P ≈' Q → Γ ∈' P → Γ ∈' Q
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

≔'-conv : ∀ {P Q Γ S'}(np : NotParEnd Γ)(e : P ≈' Q)(l : Γ ∈' P)
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

module _ {x M P}(let S = com x {M} P) where

  ∈-conv : ∀ {P Q} → P ≈' Q → S ∈ P → S ∈ Q
  ∈-conv e l = ∈'-conv act e l

  ≔-conv : ∀ {P Q S'}(e : P ≈' Q)(l : S ∈ P) → P [ l ≔ S' ] ≈' Q [ ∈-conv e l ≔ S' ]
  ≔-conv e l = ≔'-conv act e l


conv : ∀ {P Q} → P ≈' Q → ⟪ P ⟫ → ⟪ Q ⟫
conv e (end x) = end (≈'-PEnd e x)
conv e (input l x) = input (∈-conv e l) (λ m → conv (≔-conv e l) (x m))
conv e (output l m p) = output (∈-conv e l) m (conv (≔-conv e l) p)
conv e (pair l x p p₁) = pair (⊆-conv e l ) (!' /-conv e l · x) p p₁

fwd-S : ∀ S → ⟪ act S ⅋ act (dual S) ⟫
fwd-S end = end (P⅋ ε ε)
fwd-S (send P) = input (right here) λ m →
                 output (left here) m (fwd-S (P m))
fwd-S (recv P) = input (left here) λ m →
                 output (right here) m (fwd-S (P m))

fwd : ∀ Γ → ⟪ Γ ⅋ dual' Γ ⟫
fwd (act x) = fwd-S x
fwd (Γ ⅋ Γ₁) = pair (⊆-in (right here)) ⅋ε (fwd Γ) (fwd Γ₁)
fwd (Γ ⊗ Γ₁) = pair (⊆-in (left here)) (⅋-comm · ⅋ε) (conv ⅋-comm (fwd Γ)) (conv ⅋-comm (fwd Γ₁))

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

act≠⊗ : ∀ {S A B} → act S ≢ A ⊗ B
act≠⊗ ()

⊗≠act : ∀ {S A B} → A ⊗ B ≢ act S
⊗≠act ()

mix : ∀ {P Q} → ⟪ P ⟫ → ⟪ Q ⟫ → ⟪ P ⅋ Q ⟫
mix (end x) q = conv (⅋ε' · ⅋-comm · ⅋-congₗ (PEnd-≈' ε x)) q
mix (input l x) q = input (left l) λ m → mix (x m) q
mix (output l m p) q = output (left l) m (mix p q)
mix (pair (⊆-in l) x p p₁) q = pair (⊆-in (left l)) (⅋-congₗ x · ⅋-assoc)
  p (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc) (mix p₁ q))

end' : ∀ {Δ} → PEnded' Δ → ⟪ Δ ⟫
end' ε = end ε
end' (P⅋ p p₁) = mix (end' p) (end' p₁)
end' (P⊗ p p₁) = pair (⊆-in here) ⅋ε' (conv (⅋ε' · ⅋-comm) (end' p)) (conv (⅋ε' · ⅋-comm) (end' p₁))

cut₁ : ∀ {Δ Δ' S}(l : S ∈ Δ)(l' : dual S ∈ Δ') → ⟪ Δ ⟫ → ⟪ Δ' ⟫ → ⟪ Δ [ l ≔ end ] ⅋ Δ' [ l' ≔ end ] ⟫
cut₁ {S = end} cl cl' p q = conv (⅋'-cong (≔-same cl) (≔-same cl')) (mix p q)
cut₁ {S = com x P} cl cl' (pair (⊆-in tl) s p p₁) q
 with ∈'-≔' {S = act end} cl tl act ten act≠⊗
    | ∈'-≔' {S = act end} tl cl ten act ⊗≠act
    | ≔'-swap {M = act end} {M' = act end} cl tl act ten act≠⊗ ⊗≠act
... | ntl | ncl | sub with ∈-conv s ncl | ≔-conv {S' = end} s ncl
... | left gncl | sub' = pair (⊆-in (left ntl))
                            (⅋-congₗ (!' sub · sub')
                            · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
                            (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
                              (cut₁ (left gncl) cl' p q))
                            p₁
... | right gncl | sub' = pair (⊆-in (left ntl))
       (⅋-congₗ (!' sub · sub') · ⅋-assoc)
       p
       (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
         (cut₁ (left gncl) cl' p₁ q))
cut₁ {S = com x P} cl cl' p (pair (⊆-in tl) s q q₁)
 with ∈'-≔' {S = act end} cl' tl act ten act≠⊗
    | ∈'-≔' {S = act end} tl cl' ten act ⊗≠act
    | ≔'-swap {M = act end} {M' = act end} cl' tl act ten act≠⊗ ⊗≠act
... | ntl | ncl' | sub with ∈-conv s ncl' | ≔-conv {S' = end} s ncl'
... | left gncl' | sub' = pair (⊆-in (right ntl))
  (⅋'-congᵣ (!' sub · sub') · !' ⅋-assoc)
  (conv (!' ⅋-assoc) (cut₁ cl (left gncl') p q))
  q₁
... | right gncl' | sub' = pair (⊆-in (right ntl))
  (⅋'-congᵣ (!' sub · sub') · !' ⅋-assoc · ⅋-congₗ ⅋-comm · ⅋-assoc)
  q
  (conv (!' ⅋-assoc) (cut₁ cl (left gncl') p q₁))
cut₁ {S = com x P} cl cl' (end p) q = 𝟘-elim (∉-PEnd p cl)
cut₁ {S = com x P} cl cl' p (end q) = 𝟘-elim (∉-PEnd q cl')

cut₁ cl cl' (input l x) (input l' x₁) with same-var act act cl l | same-var act act cl' l'
cut₁ cl cl' (input l x₁) (input l' x₂) | inj₁ (ncl , nl , s) | Q = input (left nl) λ m
  → conv (⅋-congₗ s) (cut₁ ncl cl' (x₁ m) (input l' x₂))
cut₁ cl cl' (input l x₁) (input l' x₂) | inj₂ y | inj₁ (ncl' , nl' , s) = input (right nl') λ m
  → conv (⅋'-congᵣ s) (cut₁ cl ncl' (input l x₁) (x₂ m))
cut₁ cl cl' (input l x) (input l' x₁) | inj₂ (refl , proj₂) | inj₂ (() , proj₄)

cut₁ cl cl' (input l p) (output l' m q) with same-var act act cl l | same-var act act cl' l'
cut₁ cl cl' (input l p) (output l' m q) | inj₁ (ncl , nl , s) | Q = input (left nl) λ m'
 → conv (⅋-congₗ s) (cut₁ ncl cl' (p m') (output l' m q))
cut₁ cl cl' (input l p) (output l' m q) | inj₂ y | inj₁ (ncl' , nl' , s) = output (right nl') m
  (conv (⅋'-congᵣ s) (cut₁ cl ncl' (input l p) q))
cut₁ cl cl' (input .cl p) (output .cl' m q) | inj₂ (refl , refl) | inj₂ (refl , refl)
  = conv (⅋'-cong (sub-twice cl) (sub-twice cl')) (cut₁ (in-sub cl) (in-sub cl') (p m) q)

cut₁ cl cl' (output l m p) (input l' q) with same-var act act cl l | same-var act act cl' l'
cut₁ cl cl' (output l m p) (input l' q) | inj₁ (ncl , nl , s) | Q = output (left nl) m
  (conv (⅋-congₗ s) (cut₁ ncl cl' p (input l' q)))
cut₁ cl cl' (output l m p) (input l' q) | inj₂ y | inj₁ (ncl' , nl' , s) = input (right nl') λ m' →
  conv (⅋'-congᵣ s) (cut₁ cl ncl' (output l m p) (q m'))
cut₁ cl cl' (output .cl m p) (input .cl' q) | inj₂ (refl , refl) | inj₂ (refl , refl)
  = conv (⅋'-cong (sub-twice cl) (sub-twice cl')) (cut₁ (in-sub cl) (in-sub cl') p (q m))

cut₁ cl cl' (output l m p) (output l' m₁ q) with same-var act act cl l | same-var act act cl' l'
cut₁ cl cl' (output l m p) (output l' m₁ q) | inj₁ (ncl , nl , s) | Q = output (left nl) m (conv (⅋-congₗ s)
  (cut₁ ncl cl' p (output l' m₁ q)))
cut₁ cl cl' (output l m p) (output l' m₁ q) | inj₂ y | inj₁ (ncl' , nl' , s) = output (right nl') m₁
  (conv (⅋'-congᵣ s) (cut₁ cl ncl' (output l m p) q))
cut₁ cl cl' (output l m p) (output l' m₁ q) | inj₂ (refl , proj₂) | inj₂ (() , proj₄)

the-cut₁ : ∀ {Δ Δ' S} → ⟪ Δ ⅋ act S ⟫ → ⟪ act (dual S) ⅋ Δ' ⟫ → ⟪ Δ ⅋ Δ' ⟫
the-cut₁ p q = conv (⅋-congₗ ⅋ε · ⅋'-congᵣ (⅋-comm · ⅋ε)) (cut₁ (right here) (left here) p q)


mutual
  cut⊗ : ∀ {Δ Δ' A A' B B'} → Dual A A' → Dual B B' → (l : (A ⊗ B) ⊆ Δ) →
    ⟪ Δ ⟫ → ⟪ (A' ⅋ B') ⅋ Δ' ⟫ → ⟪ Δ / l ⅋ Δ' ⟫
  cut⊗ da db cl (end x) q = 𝟘-elim (⊈-PEnd x cl)
  cut⊗ da db cl (input l x) q = input (left (∈-/ cl l)) (λ m → conv (⅋-congₗ (≔/ cl l)) (cut⊗ da db (⊆-≔ cl l) (x m) q))
  cut⊗ da db cl (output l m p) q = output (left (∈-/ cl l)) m (conv (⅋-congₗ (≔/ cl l)) (cut⊗ da db (⊆-≔ cl l) p q))
  cut⊗ da db cl (pair l x p p₁) q with same-⊗var cl l
  cut⊗ da db cl (pair l x₁ p p₁) q | inj₁ (cl' , l' , s) with ⊆-conv x₁ cl' | /-conv x₁ cl'
  cut⊗ da db cl (pair (⊆-in l) x₁ p p₁) q | inj₁ (cl' , ⊆-in l' , s) | ⊆-in (left P₁) | sub
     = pair (⊆-in (left l'))
     (⅋-congₗ  (!' s · sub) · ⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc)
     (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc) (cut⊗ da db (⊆-in (left P₁)) p q)) p₁
  cut⊗ da db cl (pair (⊆-in l) x₁ p p₁) q | inj₁ (cl' , ⊆-in l' , s) | ⊆-in (right P₁) | sub
     = pair (⊆-in (left l')) (⅋-congₗ (!' s · sub) · ⅋-assoc) p
     (conv (⅋-assoc · ⅋'-congᵣ ⅋-comm · !' ⅋-assoc) (cut⊗ da db (⊆-in (left P₁)) p₁ q ))
  cut⊗ da db cl (pair .cl x p p₁) q | inj₂ (refl , refl) = conv
    (!' ⅋-assoc · ⅋-congₗ (⅋-comm · !' x))
    (let X = cut da p (conv ⅋-assoc q)
      in cut db p₁ (conv (!' ⅋-assoc · ⅋-congₗ ⅋-comm · ⅋-assoc) X))

  cut : ∀ {Δ Δ' Ψ Ψ'} → Dual Ψ Ψ' → ⟪ Δ ⅋ Ψ ⟫ → ⟪ Ψ' ⅋ Δ' ⟫ → ⟪ Δ ⅋ Δ' ⟫
  cut act p q = the-cut₁ p q
  cut act' p q = conv ⅋-comm (the-cut₁ (conv ⅋-comm q) (conv ⅋-comm p))
  cut (⊗⅋ d d₁ d₂ d₃) p q = conv (⅋-congₗ ⅋ε) (cut⊗ d d₂ (⊆-in (right here)) p q)
  cut (⅋⊗ d d₁ d₂ d₃) p q = conv (⅋-congₗ (⅋-comm · ⅋ε) · ⅋-comm)
                            (cut⊗ d₁ d₃ (⊆-in (left here)) q (conv ⅋-comm p))

the-cut : ∀ {Δ Δ'} Ψ → ⟪ Δ ⅋ Ψ ⟫ → ⟪ dual' Ψ ⅋ Δ' ⟫ → ⟪ Δ ⅋ Δ' ⟫
the-cut Ψ = cut (mkDual Ψ)

-- -}
-- -}
-- -}
-- -}
-- -}
