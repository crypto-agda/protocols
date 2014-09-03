{-# OPTIONS --copattern #-}
open import proto hiding (_⊗_; _⅋_) renaming (Proto to Session)
-- open import Types hiding ([_is_⋎_]; _[_≔_])
open import Frm
open import prelude
open import uri

module ParTenTerms where

open FrmZip [_is_⋎_]S public

module _ {a} {A : Set a} where
    _s⅋_ : Frm A → Frm A → Frm A
    ε s⅋ Δ = Δ
    act S s⅋ Δ = act S ⅋ Δ
    (Γ ⅋ Δ) s⅋ Ψ = Γ s⅋ (Δ s⅋ Ψ) 
    (Γ ⊗ Δ) s⅋ Ψ = (Γ ⊗ Δ) ⅋ Ψ 

-- AllEnv
data E : Proto → Set₁ where
  ε : E ε
  act : E (act end)
  _⊗_ : ∀ {Γ Δ} (e₀ : E Γ)(e₁ : E Δ) → E (Γ ⊗ Δ)
  _⅋_ : ∀ {Γ Δ} (e₀ : E Γ)(e₁ : E Δ) → E (Γ ⅋ Δ)

Zip-E₀ : ∀ {Δ Δ₀ Δ₁} → E Δ₀ → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ ≡ Δ₁
Zip-E₀ e ε = refl
Zip-E₀ act (act act₀) = refl
Zip-E₀ act (act act₁) = refl
Zip-E₀ (e₀ ⊗ e₁) (z₀ ⊗ z₁) = ap₂ _⊗_ (Zip-E₀ e₀ z₀) (Zip-E₀ e₁ z₁)
Zip-E₀ (e₀ ⅋ e₁) (z₀ ⅋ z₁) = ap₂ _⅋_ (Zip-E₀ e₀ z₀) (Zip-E₀ e₁ z₁)

Zip-E₁ : ∀ {Δ Δ₀ Δ₁} → E Δ₁ → [ Δ is Δ₀ ⋎ Δ₁ ] → Δ ≡ Δ₀
Zip-E₁ e z = Zip-E₀ e (Zip-comm z)

data ⟪_⟫ : Proto → Set₁ where
  end   : ∀ {Γ} → E Γ → ⟪ Γ ⟫
  end-E   : ∀ {Γ Δ} → ⟪ Γ ⟫ → E Δ → ⟪ Γ ⅋ Δ ⟫
  end-E'   : ∀ {Γ Δ} → ⟪ Γ ⅋ Δ ⟫ → E Δ → ⟪ Γ ⟫
  -- ⅋-assoc : ∀ {Γ Δ Ψ} → ⟪ (Γ ⅋ Δ) ⅋ Ψ ⟫ → ⟪ Γ ⅋ (Δ ⅋ Ψ) ⟫

  output : ∀ {Δ M P}{{_ : SER M}}
             (l : send P ∈ Δ) → (m : M)
             (p : ⟪ Δ [ l ≔ m ]' ⟫)
             --------------------
               → ⟪ Δ ⟫

  input : ∀ {Δ M}{P : M → _}{{_ : SER M}}
            (l : recv P ∈ Δ)
            (p : ∀ m → ⟪ Δ [ l ≔ m ]' ⟫)
            ----------------------------
                     → ⟪ Δ ⟫

 -- _,_ : ∀ {Γ Δ Γ' Δ'} (p : ⟪ Γ ⅋ Δ ⟫) (q : ⟪ Γ' ⅋ Δ' ⟫) → ⟪ (Γ ⅋ Γ') ⅋ (Δ ⊗ Δ') ⟫
  pair : ∀ {Γ Γ₀ Γ₁ Δ Δ'} (z : [ Γ is Γ₀ ⋎ Γ₁ ]) (p : ⟪ Γ₀ ⅋ Δ ⟫) (q : ⟪ Γ₁ ⅋ Δ' ⟫) → ⟪ Γ ⅋ (Δ ⊗ Δ') ⟫

fst⊗ : ∀ {Δ Γ Ψ} → ⟪ Γ ⅋ (Δ ⊗ Ψ) ⟫ → ⟪ Γ ⅋ Δ ⟫
fst⊗ (end x) = {!!}
fst⊗ (end-E p x) = {!!}
fst⊗ (end-E' p x) = {!!}
fst⊗ (output l m p) = {!!}
fst⊗ (input l p) = {!!}
fst⊗ (pair z p₀ p₁) = {!!}

{-
fst⊗ : ∀ {Δ Γ} → ⟪ Δ ⊗ Γ ⟫ → ⟪ Δ ⟫
fst⊗ (end (e ⊗ _)) = end e
fst⊗ (output () m p)
fst⊗ (input () p)
fst⊗ (end-E' p e) = {!!}
-- fst⊗ (p , _) = p

  {-
snd⊗ : ∀ {Δ Γ} → ⟪ Δ ⊗ Γ ⟫ → ⟪ Γ ⟫
snd⊗ (end (_ ⊗ e)) = end e
snd⊗ (output () m p)
snd⊗ (input () p)
-- snd⊗ (_ , p) = p

{-
pair⅋ : ∀ {Γ Δ} (p : ⟪ Γ ⟫) (q : ⟪ Δ ⟫) → ⟪ Γ ⅋ Δ ⟫
pair⅋ = {!!}
-}

mixE : ∀ {Δ Δ₀ Δ₁} (z : [ Δ is Δ₀ ⋎ Δ₁ ])
         (p : ⟪ Δ₀ ⟫)
         (q : E Δ₁)
         -------------
           → ⟪ Δ ⟫
mixE ε p q = end q
mixE (act act₀) p q = p
mixE (act act₁) p q = end q
mixE (z₀ ⊗ z₁) p (q₀ ⊗ q₁) = mixE z₀ (fst⊗ p) q₀ , mixE z₁ (snd⊗ p) q₁
mixE (z₀ ⅋ z₁) p (q₀ ⅋ q₁) rewrite Zip-E₁ q₀ z₀ | Zip-E₁ q₁ z₁ = p

mixᶜᶠ : ∀ {Δ Δ₀ Δ₁} (z : [ Δ is Δ₀ ⋎ Δ₁ ])
         (p : ⟪ Δ₀ ⟫)
         (q : ⟪ Δ₁ ⟫)
         -------------
           → ⟪ Δ ⟫
-- mixᶜᶠ ε end end = end
mixᶜᶠ z (output l m p) q = output (Zip-com∈₀ z l) m (mixᶜᶠ (Zip-≔₀ l z) p q)
mixᶜᶠ z (input l p) q = input (Zip-com∈₀ z l) λ m → mixᶜᶠ (Zip-≔₀ l z) (p m) q
mixᶜᶠ z p (output l m q) = output (Zip-com∈₁ z l) m (mixᶜᶠ (Zip-≔₁ l z) p q)
mixᶜᶠ z p (input l q) = input (Zip-com∈₁ z l) λ m → mixᶜᶠ (Zip-≔₁ l z) p (q m)
mixᶜᶠ z p (end q) = mixE z p q
mixᶜᶠ z (end p) q = mixE (Zip-comm z) q p
mixᶜᶠ (z₀ ⊗ z₁) (p , q) (r , s) = mixᶜᶠ z₀ p r , mixᶜᶠ z₁ q s
-- mixᶜᶠ (z₀ ⅋ (z₁ ⅋ z₂)) (⅋-assoc p) q = mixᶜᶠ {!!} p q
-- mixᶜᶠ (z₀ ⅋ z₁) p (⅋-assoc q) = {!!} -- mixᶜᶠ {!!} p q

com∉E : ∀ {Γ x M SER S} → E Γ → com x {M} {{SER}} S ∉ Γ
com∉E act (act ())
com∉E (e ⅋ e₁) (left p) = com∉E e p
com∉E (e ⅋ e₁) (right p) = com∉E e₁ p

no-right : ∀ {Δ Γ} → E Γ → ⟪ Δ ⅋ Γ ⟫ → ⟪ Δ ⟫
no-right e (end (x ⅋ _)) = end x
no-right e (output (left l) m p) = output l m (no-right e p)
no-right e (input (left l) p) = input l λ m → no-right e (p m)
no-right e (output (right l) m p) = 𝟘-elim (com∉E e l)
no-right e (input (right l) p) = 𝟘-elim (com∉E e l)

no-right-end : ∀ {Δ} → ⟪ Δ ⅋ act end ⟫ → ⟪ Δ ⟫
no-right-end = no-right act

no-right-ε : ∀ {Δ} → ⟪ Δ ⅋ ε ⟫ → ⟪ Δ ⟫
no-right-ε = no-right ε

module _ {x M SER S} where
    no-E-act : ¬(E (act (com x {M} {{SER}} S)))
    no-E-act ()

    {-
no-right-ε' : ∀ {Δ} → ⟪ Δ ⟫ → ⟪ Δ ⅋ ε ⟫
no-right-ε' (output l m p) = output (left l) m (no-right-ε' p)
no-right-ε' (input l p) = input (left l) λ m → no-right-ε' (p m)
no-right-ε' (end p) = end (p ⅋ ε)
-- no-right-ε' end = end' end
no-right-ε' (p , q) = {!no-right-ε' p!}
-}

{-(-}
{-)-}

{-+}
eeee
{+-}

cut1 : ∀ {Δ Δ₀ Δ₁}
         (z : [ Δ is Δ₀ ⋎ Δ₁ ]) P
         (p : ⟪ Δ₀ ⅋ act (dual P) ⟫)
         (q : ⟪ Δ₁ ⅋ act P ⟫)
         ---------------------------
           → ⟪ Δ ⟫ -- ⅋ act end ⟫
cut1 z (recv P) (output (right (act refl)) m p) (input  (right (act refl))   q) = cut1 z (P m) p (q m)
cut1 z (send P) (input  (right (act refl))   p) (output (right (act refl)) m q) = cut1 z (P m) (p m) q
cut1 z end      p q = mixᶜᶠ z (no-right-end p) (no-right-end q) -- mixᶜᶠ (z ⅋ act act₀) p q

cut1 z P (output (left l) m p) q = output (Zip-com∈₀ z l) m (cut1 (Zip-≔₀ l z) _ p q)
cut1 z P (input (left l) p) q = input (Zip-com∈₀ z l) λ m → cut1 (Zip-≔₀ l z) _ (p m) q
cut1 z P p (input (left l) q) = input (Zip-com∈₁ z l) λ m → cut1 (Zip-≔₁ l z) _ p (q m)
cut1 z P p (output (left l) m q) = output (Zip-com∈₁ z l) m (cut1 (Zip-≔₁ l z) _ p q)

cut1 z (com x P) (end (p ⅋ ())) q
cut1 z (com x P) p (end (q ⅋ ()))
cut1 z (recv P) (output (right (act refl)) m p) (output (right (act ())) m₁ q)
cut1 z (send P) (input (right (act refl)) p) (input (right (act ())) p₁)
cut1 z (send P) (output (right (act ())) m p) q
cut1 z (recv P) (input (right (act ())) p) q

dual' : Proto → Proto
dual' ε = ε
dual' (act S) = act (dual S)
dual' (Γ ⅋ Δ) = dual' Γ ⊗ dual' Δ
dual' (Γ ⊗ Δ) = dual' Γ ⅋ dual' Δ

mix-pair : ∀ {Δ Δ₀ Δ₁}
             (z : [ Δ is Δ₀ ⋎ Δ₁ ]) Γ₀ Γ₁
             (p : ⟪ Δ₀ ⅋ Γ₀ ⟫)
             (q : ⟪ Δ₁ ⅋ Γ₁ ⟫)
            ---------------------------
               → ⟪ Δ ⅋ (Γ₀ ⊗ Γ₁) ⟫
mix-pair ε Γ₀ Γ₁ p q = {!!}
mix-pair (act x)  Γ₀ Γ₁ p q = {!!}
mix-pair (z₀ ⊗ z₁) Γ₀ Γ₁ p q = {!!}
mix-pair (z₀ ⅋ z₁) Γ₀ Γ₁ p q = {!!}
               {-
mix-pair z Γ₀ Γ₁ (output (left l) m p) q = output (left (Zip-com∈₀ z l)) m (mix-pair (Zip-≔₀ l z) Γ₀ Γ₁ p q)
mix-pair z Γ₀ Γ₁ (input (left l) p) q = input (left (Zip-com∈₀ z l)) λ m → mix-pair (Zip-≔₀ l z) Γ₀ Γ₁ (p m) q
mix-pair z Γ₀ Γ₁ p (output (left l) m q) = output (left (Zip-com∈₁ z l)) m (mix-pair (Zip-≔₁ l z) Γ₀ Γ₁ p q)
mix-pair z Γ₀ Γ₁ p (input (left l) q) = input (left (Zip-com∈₁ z l)) λ m → mix-pair (Zip-≔₁ l z) Γ₀ Γ₁ p (q m)
mix-pair z Γ₀ Γ₁ (output (right l) m p) (output (right l') n q) = {!output l m!}
mix-pair z Γ₀ Γ₁ (output (right l) m p) (input (right l') q) = {!!}
mix-pair z Γ₀ Γ₁ (input (right l) p) q = {!!}
-}

E-dual : ∀ {Γ} → E (dual' Γ) → E Γ
E-dual {ε} e = e
E-dual {act end} e = act
E-dual {act (com x P)} ()
E-dual {Γ ⅋ Γ₁} (e₀ ⊗ e₁) = E-dual e₀ ⅋ E-dual e₁
E-dual {Γ ⊗ Γ₁} (e₀ ⅋ e₁) = E-dual e₀ ⊗ E-dual e₁

E-dual' : ∀ {Γ} → E Γ → E (dual' Γ)
E-dual' {ε} e = e
E-dual' {act end} e = act
E-dual' {act (com x P)} ()
E-dual' {Γ ⅋ Γ₁} (e₀ ⅋ e₁) = E-dual' e₀ ⊗ E-dual' e₁
E-dual' {Γ ⊗ Γ₁} (e₀ ⊗ e₁) = E-dual' e₀ ⅋ E-dual' e₁

fwd : ∀ Γ → ⟪ Γ ⅋ dual' Γ ⟫
fwd ε = end (ε ⅋ ε)
fwd (act S) = {!!}
fwd (Γ ⅋ Γ₁) = {!!}
fwd (Γ ⊗ Γ₁) = {!!}

cut : ∀ {Δ Δ₀ Δ₁}
        (z : [ Δ is Δ₀ ⋎ Δ₁ ]) Γ
        (p : ⟪ Δ₀ ⅋ dual' Γ ⟫)
        (q : ⟪ Δ₁ ⅋ Γ ⟫)
       ---------------------------
          → ⟪ Δ ⟫
cut z Γ (end (e₀ ⅋ e₁)) q rewrite Zip-E₀ e₀ z = no-right (E-dual e₁) q

cut z Γ (output (left l) m p) q = output (Zip-com∈₀ z l) m (cut (Zip-≔₀ l z) Γ p q)
cut z Γ (input (left l) p) q = input (Zip-com∈₀ z l) λ m → cut (Zip-≔₀ l z) Γ (p m) q
cut z Γ p (output (left l) m q) = output (Zip-com∈₁ z l) m (cut (Zip-≔₁ l z) Γ p q)
cut z Γ p (input (left l) q) = input (Zip-com∈₁ z l) λ m → cut (Zip-≔₁ l z) Γ p (q m)

cut z Γ (output (right l) m p) (output (right l₁) m₁ q) = {!!}
cut z Γ (output (right l) m p) (input l₁ p₁) = {!!}
cut z Γ (input (right l) p) (end x₁) = {!!}
cut z ε (input (right ()) p) (output (right l₁) m q)
cut z (act end) (input (right (act ())) p) (output (right (act e')) m q)
cut z (act (com IN P)) (input (right (act ())) p) (output (right (act e')) m q)
cut z (act (com OUT P)) (input (right (act refl)) p) (output (right (act refl)) m q) = cut z (act (P m)) (p m) q
cut z (Γ ⅋ Γ₁) (input (right ()) p) (output (right l₁) m q)
cut z (Γ ⊗ Γ₁) (input (right l) p) (output (right ()) m q)
cut z ._ (input (right l) p) (input (right (act refl)) p₁) with l
... | act ()
cut z ._ (input (right ()) p) (input (right (left l₁)) p₁)
cut z ._ (input (right ()) p) (input (right (right l₁)) p₁)
cut z Γ (output (right l) m p) (end (x₁ ⅋ x₂)) = 𝟘-elim (com∉E (E-dual' x₂) l)
{-
cut z ε p q = mixᶜᶠ z (no-right-ε p) (no-right-ε q)
cut z (act S) p q = cut1 z S p q
cut z (Γ ⅋ Δ) p q = {!!}
cut z (Γ ⊗ Δ) p q = {!!}

{-
cutᶜᶠ _ _ end _ -- end {-e = _ , ()-}) _
cutᶜᶠ _ _ _ (end {-e = _ , ()-})
{-
cutᶜᶠ z P (output (there l) m p) q
  = output (there (Zip-com∈₀ z l)) m (cutᶜᶠ (Zip-≔₀ l z) _ p q)
cutᶜᶠ z P (input (there l) p) q
  = input (there (Zip-com∈₀ z l)) λ m → cutᶜᶠ (Zip-≔₀ l z) _ (p m) q
cutᶜᶠ z P p (output (there l) m q)
  = output (there (Zip-com∈₁ z l)) m (cutᶜᶠ (Zip-≔₁ l z) _ p q)
cutᶜᶠ z P p (input (there l) q)
  = input (there (Zip-com∈₁ z l)) λ m → cutᶜᶠ (Zip-≔₁ l z) _ p (q m)

cutᶜᶠ z end p q = mixᶜᶠ (z , ↦₀ end) p q
cutᶜᶠ _ _ (com _ _) (end {e = _ , ()}) _
cutᶜᶠ _ _ (com _ _) _ (end {e = _ , ()})

{-
infix 2 ⊢ˢ_ ⊢_ ⊢ᶜᶠ_ _⊢_

data ⊢_ : (Δ : Env) → Set₁ where
  end : ∀{Δ}{e : EndedEnv Δ}
       ------------------
      → ⊢ Δ

  output : ∀ {Δ d M P}{{_ : SER M}}
             (l : d ↦ send P ∈ Δ)(m : M)
             (p : ⊢ Δ [ l ≔ m ])
             -------------------
               → ⊢ Δ

  input : ∀ {Δ d M}{P : M → _}{{_ : SER M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → ⊢ Δ [ l ≔ m ])
                 ----------------------
                     → ⊢ Δ

  mix : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
          (p : ⊢ Δ₀) (q : ⊢ Δ₁)
          --------------------
        → ⊢ Δ

  cut : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) {P d}
          (p : ⊢ (Δ₀ , d ↦ dual P))
          (q : ⊢ (Δ₁ , d ↦ P))
          ---------------------
        → ⊢ Δ

  fwd : ∀ c d {P} → ⊢ (ε , c ↦ P , d ↦ dual P)

  exch-last :
      ∀ {Δ c d P Q} →
      (p : ⊢ Δ , c ↦ P , d ↦ Q)
      → ⊢ Δ , d ↦ Q , c ↦ P

  wk-last : ∀ {Δ d}
              (p : ⊢ Δ)
              -----------------------
                → ⊢ (Δ , d ↦ end)

  end-last : ∀ {Δ d}
               (p : ⊢ (Δ , d ↦ end))
               ----------------------
                 → ⊢ Δ

data ⊢ᶜᶠ_ (Δ : Env) : Set₁ where
  end : {e : EndedEnv Δ} → ⊢ᶜᶠ Δ

  output : ∀ {d M P}{{_ : SER M}}
            (l : d ↦ send P ∈ Δ) → (m : M)
            (p : ⊢ᶜᶠ Δ [ l ≔ m ])
            --------------------
              → ⊢ᶜᶠ Δ

  input : ∀ {d M}{P : M → _}{{_ : SER M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → ⊢ᶜᶠ Δ [ l ≔ m ])
            ----------------------------
                     → ⊢ᶜᶠ Δ

-- The Δ for the server contains the view point of the clients
-- The point is that the meaning of _,_ in Δ is ⊗ while it
-- is ⅋ in ⊢ᶜᶠ
record ⊢ˢ_ (Δ : Env) : Set₁ where
  coinductive
  field
    server-output :
      ∀ {d M}{{_ : SER M}}{P : M → Session}
        (l : d ↦ recv P ∈ Δ) →
        Σ M λ m → ⊢ˢ Δ [ l ≔ m ]
    server-input :
      ∀ {d M}{{_ : SER M}}{P : M → Session}
        (l : d ↦ send P ∈ Δ)
        (m : M) → ⊢ˢ Δ [ l ≔ m ]
open ⊢ˢ_ public

record Server (K : Env → Set₁) (Δ : Env) : Set₁ where
  constructor _,_
  field
    srv-output :
      ∀ {d M}{{_ : SER M}}{P : M → Session}
        (l : d ↦ recv P ∈ Δ) →
        Σ M λ m → K (Δ [ l ≔ m ])
    srv-input :
      ∀ {d M}{{_ : SER M}}{P : M → Session}
        (l : d ↦ send P ∈ Δ)
        (m : M) → K (Δ [ l ≔ m ])
open Server public

record SQ (K : Env → Set₁) (Δ : Env) {d P} (l : d ↦ P ∈ Δ) : Set where
  field
    sq-output : ∀ {M} {{_ : SER M}} {P : M → Session}
                  → Σ M λ m → K (Δ [ l ≔ m ])
    sq-input  : ∀ {M} {{_ : SER M}} {P : M → Session}
                  (m : M) → K (Δ [ l ≔ m ])
  

Server' : (K : Env → Set₁) (Δ : Env) → Set₁
Server' K Δ =
      ∀ {d P}
        (l : d ↦ P ∈ Δ) →
        {!!}

record Server1 (K : Session → Set₁) (A : Session) : Set₁ where
  constructor _,_
  field
    srv1-output :
      ∀ {M}{{_ : SER M}}{P : M → Session}
        (e : A ≡ recv P) →
        Σ M λ m → K (P m)
    srv1-input :
      ∀ {M}{{_ : SER M}}{P : M → Session}
        (e : A ≡ send P)
        (m : M) → K (P m)
open Server1 public

data _⊢_ (Γ Δ : Env) : Set₁ where
  end : {eΓ : EndedEnv Γ} {eΔ : EndedEnv Δ} → Γ ⊢ Δ

  output : ∀ {d M P}{{_ : SER M}}
            (l : d ↦ send P ∈ Δ) → (m : M)
            (p : Γ ⊢ Δ [ l ≔ m ])
            --------------------
              → Γ ⊢ Δ

  input : ∀ {d M}{P : M → _}{{_ : SER M}}
            (l : d ↦ recv P ∈ Δ)
            (p : ∀ m → Γ ⊢ Δ [ l ≔ m ])
            ----------------------------
                     → Γ ⊢ Δ

  select : Server (λ Γ' → Γ' ⊢ Δ) Γ
            ----------------------------
                     → Γ ⊢ Δ

-- This is just to confirm that we have enough cases
telecom' : ∀ {Δ} → ⊢ᶜᶠ Δ → ⊢ˢ Δ → 𝟙
telecom' end q = _
telecom' (output l m p) q
  = telecom' p (server-input q l m)
telecom' (input l p) q
  = case server-output q l of λ { (m , s) →
      telecom' (p m) s }

split-∈-,, : ∀ {c P Δ₀} Δ₁
               (l : c ↦ P ∈ (Δ₀ ,, Δ₁))
          → (Σ (c ↦ P ∈ Δ₀) λ l₀ → ∀ {d Q} → (Δ₀ ,, Δ₁) [ l ≔ d ↦ Q ] ≡ (Δ₀ [ l₀ ≔ d ↦ Q ] ,, Δ₁))
          ⊎ (Σ (c ↦ P ∈ Δ₁) λ l₁ → ∀ {d Q} → (Δ₀ ,, Δ₁) [ l ≔ d ↦ Q ] ≡ (Δ₀ ,, Δ₁ [ l₁ ≔ d ↦ Q ]))
split-∈-,, ε l = inl (l , refl)
split-∈-,, (Δ₁ , c ↦ P) here = inr (here , refl)
split-∈-,, (Δ₁ , d ↦ P) (there l) with split-∈-,, Δ₁ l
... | inl (r , e) = inl (r , ap (λ Δ → Δ , d ↦ P) e)
... | inr (r , e) = inr (there r , ap (λ Δ → Δ , d ↦ P) e)

{-
split-∈-⋎ : ∀ {c P Δ Δ₀ Δ₁}
              (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
              (l : c ↦ P ∈ Δ)
           → (c ↦ P ∈ Δ₀)
           → (Σ (c ↦ P ∈ Δ₀) λ l₀ → ∀ {d Q} → Δ [ l ≔ d ↦ Q ] ≡ (Δ₀ [ l₀ ≔ d ↦ Q ] ,, Δ₁))
            ⊎ (c ↦ P ∈ Δ₁)
            -}

{-
split-∈-,, : ∀ {c P Δ₀} Δ₁
               (l : c ↦ P ∈ (Δ₀ ,, Δ₁))
          → (Σ (c ↦ P ∈ Δ₀) λ l₀ → ∀ {d Q} → (Δ₀ ,, Δ₁) [ l ≔ d ↦ Q ] ≡ (Δ₀ [ l₀ ≔ d ↦ Q ] ,, Δ₁))
          ⊎ (Σ (c ↦ P ∈ Δ₁) λ l₁ → ∀ {d Q} → (Δ₀ ,, Δ₁) [ l ≔ d ↦ Q ] ≡ (Δ₀ ,, Δ₁ [ l₁ ≔ d ↦ Q ]))
split-∈-,, ε l = inl (l , refl)
split-∈-,, (Δ₁ , c ↦ P) here = inr (here , refl)
split-∈-,, (Δ₁ , d ↦ P) (there l) with split-∈-,, Δ₁ l
... | inl (r , e) = inl (r , ap (λ Δ → Δ , d ↦ P) e)
... | inr (r , e) = inr (there r , ap (λ Δ → Δ , d ↦ P) e)
-}

split-∈-⋎ : ∀ {c P Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) → c ↦ P ∈ Δ → (c ↦ P ∈ Δ₀) ⊎ (c ↦ P ∈ Δ₁)
split-∈-⋎ (Δₛ , c ↦₀ P) here = inl here
split-∈-⋎ (Δₛ , c ↦₁ P) here = inr here
split-∈-⋎ (Δₛ , d' ↦₀ P') (there l) with split-∈-⋎ Δₛ l
... | inl r = inl (there r)
... | inr r = inr (there r)
split-∈-⋎ (Δₛ , d' ↦₁ P') (there l) with split-∈-⋎ Δₛ l
... | inl r = inl (there r)
... | inr r = inr (there r)

{-
split-∈-,, : ∀ {c P Δ₀} Δ₁ → c ↦ P ∈ (Δ₀ ,, Δ₁) → (c ↦ P ∈ Δ₀) ⊎ (c ↦ P ∈ Δ₁)
split-∈-,, ε l = inl l
split-∈-,, (Δ₁ , c ↦ P) here = inr here
split-∈-,, (Δ₁ , d ↦ P) (there l) with split-∈-,, Δ₁ l
... | inl r = inl r
... | inr r = inr (there r)
-}

{-
⊢ˢ-zip : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) → ⊢ˢ Δ₀ → ⊢ˢ Δ₁ → ⊢ˢ Δ
⊢ˢ-zip {Δ} {Δ₀} {Δ₁} Δₛ s₀ s₁ = record { server-output = so ; server-input = {!!} }
  where
    so :
      ∀ {d M}{{_ : SER M}}{P : M → Session}
        (l : d ↦ recv P ∈ Δ) →
        Σ M λ m → ⊢ˢ Δ [ l ≔ m ]
    so l with split-∈-⋎ Δₛ l
    ... | inl r = let (m , s') = server-output s₀ r in
                  m , {!⊢ˢ-zip Δₛ ? ?!}
    ... | inr r = {!!}
    -}

module _ {Δ c} where
    ⊢ˢ-last : ∀ {A} → ⊢ˢ (Δ , c ↦ A) → ⊢ˢ (ε , c ↦ A)
    fst (server-output (⊢ˢ-last s) here) = _
    snd (server-output (⊢ˢ-last s) here) = ⊢ˢ-last (snd (server-output s here))
    server-output (⊢ˢ-last s) (there ())
    server-input (⊢ˢ-last s) here m = ⊢ˢ-last (server-input s here m)
    server-input (⊢ˢ-last s) (there ()) m

module _ {A c} where
    ⊢ˢ-init : ∀ {Δ} → ⊢ˢ (Δ , c ↦ A) → ⊢ˢ Δ
    fst (server-output (⊢ˢ-init s) l) = _
    snd (server-output (⊢ˢ-init s) l) = ⊢ˢ-init (snd (server-output s (there l)))
    server-input (⊢ˢ-init s) l m = ⊢ˢ-init (server-input s (there l) m)

    {-
    ⊢ˢ-tail : ∀ {Δ} → ⊢ˢ (ε , c ↦ A ,, Δ) → ⊢ˢ Δ
    server-output (⊢ˢ-tail s) l = {!!}
--    fst (server-output (⊢ˢ-init s) l) = _
--    snd (server-output (⊢ˢ-init s) l) = ⊢ˢ-init (snd (server-output s (there l)))
    server-input (⊢ˢ-tail s) l m = ⊢ˢ-tail (server-input s {!there,, l!} m)
    -}

module _ {Δ₀} where
    ⊢ˢ-fst : ∀ {Δ₁} → ⊢ˢ (Δ₀ ,, Δ₁) → ⊢ˢ Δ₀
    ⊢ˢ-fst {ε} s = s
    ⊢ˢ-fst {Δ₁ , d ↦ P} s = ⊢ˢ-fst {Δ₁} (⊢ˢ-init s)

    {-
    ⊢ˢ-snd : ∀ {Δ₁} → ⊢ˢ (Δ₀ ,, Δ₁) → ⊢ˢ Δ₁
    ⊢ˢ-snd {ε} s = {!!}
    ⊢ˢ-snd {Δ₁ , d ↦ P} s = {!⊢ˢ-snd {Δ₁} (⊢ˢ-last s)!}
    -}

module _ {c d} where
    ⊢ˢ-pair' : ∀ {A B} → ⊢ˢ (ε , c ↦ A) → ⊢ˢ (ε , d ↦ B) → ⊢ˢ (ε , c ↦ A , d ↦  B)
    server-output (⊢ˢ-pair' s₀ s₁) here =
      let (m , s') = server-output s₁ here in m , ⊢ˢ-pair' s₀ s'
    server-output (⊢ˢ-pair' s₀ s₁) (there here) =
      let (m , s') = server-output s₀ here in m , ⊢ˢ-pair' s' s₁
    server-output (⊢ˢ-pair' s₀ s₁) (there (there ()))
    server-input (⊢ˢ-pair' s₀ s₁) here m = ⊢ˢ-pair' s₀ (server-input s₁ here m)
    server-input (⊢ˢ-pair' s₀ s₁) (there here) m = ⊢ˢ-pair' (server-input s₀ here m) s₁
    server-input (⊢ˢ-pair' s₀ s₁) (there (there ())) m

⊢ˢ-pair : ∀ {Δ₀ Δ₁} → ⊢ˢ Δ₀ → ⊢ˢ Δ₁ → ⊢ˢ (Δ₀ ,, Δ₁)
server-output (⊢ˢ-pair {Δ₀} {Δ₁} s₀ s₁) {d} {M} {P} l = so
  where
    so : Σ M λ m → ⊢ˢ (Δ₀ ,, Δ₁) [ l ≔ m ]
    so with split-∈-,, Δ₁ l
    so | inl (r , e) with server-output s₀ r
    so | inl (r , e) | (m , s') = m , tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair s' s₁)
    so | inr (r , e) with server-output s₁ r
    so | inr (r , e) | (m , s') = m , tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair s₀ s')
server-input (⊢ˢ-pair {Δ₀} {Δ₁} s₀ s₁) {d} {M} {P} l m = si
  where
    si : ⊢ˢ (Δ₀ ,, Δ₁) [ l ≔ m ]
    si with split-∈-,, Δ₁ l
    ... | inl (r , e) = tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair (server-input s₀ r m) s₁)
    ... | inr (r , e) = tr ⊢ˢ_ (! (e {d} {P m})) (⊢ˢ-pair s₀ (server-input s₁ r m))

embedᶜᶠ : ∀ {Δ} → ⊢ᶜᶠ Δ → ⊢ Δ
embedᶜᶠ (end {e = e}) = end {e = e}
embedᶜᶠ (output l m p) = output l m (embedᶜᶠ p)
embedᶜᶠ (input l p) = input l λ m → embedᶜᶠ (p m)

mixᶜᶠ : ∀ {Δ Δ₀ Δ₁} (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ])
         (p : ⊢ᶜᶠ Δ₀)
         (q : ⊢ᶜᶠ Δ₁)
         -------------
           → ⊢ᶜᶠ Δ
mixᶜᶠ Δₛ end q = tr ⊢ᶜᶠ_ (Zip-identity  Δₛ) q
mixᶜᶠ Δₛ (output l m p) q
  = output (Zip-com∈₀ Δₛ l) m (mixᶜᶠ (Zip-≔₀ l Δₛ) p q)
mixᶜᶠ Δₛ (input l p) q
  = input (Zip-com∈₀ Δₛ l) λ m → mixᶜᶠ (Zip-≔₀ l Δₛ) (p m) q

cutᶜᶠ : ∀ {Δ Δ₀ Δ₁}
         (Δₛ : [ Δ is Δ₀ ⋎ Δ₁ ]) d P
         (p : ⊢ᶜᶠ (Δ₀ , d ↦ dual P))
         (q : ⊢ᶜᶠ (Δ₁ , d ↦ P))
         ---------------------------
           → ⊢ᶜᶠ (Δ , d ↦ end)

cutᶜᶠ Δₛ d (recv P) (output here m p) (input here q) = cutᶜᶠ Δₛ d (P m) p (q m)
cutᶜᶠ Δₛ d (send P) (input here p) (output here m q) = cutᶜᶠ Δₛ d (P m) (p m) q

cutᶜᶠ Δₛ d P (output (there l) m p) q
  = output (there (Zip-com∈₀ Δₛ l)) m (cutᶜᶠ (Zip-≔₀ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d P (input (there l) p) q
  = input (there (Zip-com∈₀ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₀ l Δₛ) d _ (p m) q
cutᶜᶠ Δₛ d P p (output (there l) m q)
  = output (there (Zip-com∈₁ Δₛ l)) m (cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p q)
cutᶜᶠ Δₛ d P p (input (there l) q)
  = input (there (Zip-com∈₁ Δₛ l)) λ m → cutᶜᶠ (Zip-≔₁ l Δₛ) d _ p (q m)

cutᶜᶠ Δₛ d end p q = mixᶜᶠ (Δₛ , d ↦₀ end) p q
cutᶜᶠ _ _ (com _ _) (end {e = _ , ()}) _
cutᶜᶠ _ _ (com _ _) _ (end {e = _ , ()})


end-lastᶜᶠ : ∀ {Δ d}
              (p : ⊢ᶜᶠ (Δ , d ↦ end))
              -----------------------
                → ⊢ᶜᶠ Δ
end-lastᶜᶠ (end {e = e , _}) = end {e = e}
end-lastᶜᶠ (output (there l) m p) = output l m (end-lastᶜᶠ p)
end-lastᶜᶠ (input (there l) p) = input l λ m → end-lastᶜᶠ (p m)

wk-lastᶜᶠ : ∀ {Δ d}
             (p : ⊢ᶜᶠ Δ)
             -----------------------
               → ⊢ᶜᶠ (Δ , d ↦ end)
wk-lastᶜᶠ end = end {e = … , _}
wk-lastᶜᶠ (output l m p) = output (there l) m (wk-lastᶜᶠ p)
wk-lastᶜᶠ (input l p) = input (there l) λ m → wk-lastᶜᶠ (p m)

wk-,,ᶜᶠ : ∀ {Δ₀ Δ₁} → ⊢ᶜᶠ Δ₀ → EndedEnv Δ₁ → ⊢ᶜᶠ Δ₀ ,, Δ₁
wk-,,ᶜᶠ {Δ₁ = ε} p E = p
wk-,,ᶜᶠ {Δ₁ = Δ₁ , d ↦ P} p (E , e) rewrite Ended-≡end e
  = wk-lastᶜᶠ (wk-,,ᶜᶠ p E)

module _ {d P Δ₀} where
  pre-wk-∈ : ∀ {Δ₁} → d ↦ P ∈ Δ₁ → d ↦ P ∈ (Δ₀ ,, Δ₁)
  pre-wk-∈ here = here
  pre-wk-∈ (there l) = there (pre-wk-∈ l)

{-
pre-wkᶜᶠ : ∀ {Δ₀ Δ₁} → EndedEnv Δ₀ → ⊢ᶜᶠ Δ₁ → ⊢ᶜᶠ Δ₀ ,, Δ₁
pre-wkᶜᶠ EΔ₀ end = end {e = {!!}}
pre-wkᶜᶠ {Δ₀} {Δ₁} EΔ₀ (output l m p) =
  output (pre-wk-∈ l) m (pre-wkᶜᶠ {Δ₀} {{!Δ₁!}} EΔ₀ {!!})
pre-wkᶜᶠ EΔ₀ (input l p) = {!!}
-}

fwd-mixᶜᶠ : ∀ {Δ c d} P → ⊢ᶜᶠ Δ → ⊢ᶜᶠ (Δ , c ↦ P , d ↦ dual P)
fwd-mixᶜᶠ end p = wk-lastᶜᶠ (wk-lastᶜᶠ p)
fwd-mixᶜᶠ (recv P) p = input (there here) λ m → output here m (fwd-mixᶜᶠ (P m) p)
fwd-mixᶜᶠ (send P) p = input here λ m → output (there here) m (fwd-mixᶜᶠ (P m) p)

fwdᶜᶠ : ∀ c d {P} → ⊢ᶜᶠ (ε , c ↦ P , d ↦ dual P)
fwdᶜᶠ _ _ {P} = fwd-mixᶜᶠ {ε} P end

ε,, : ∀ Δ → ε ,, Δ ≡ Δ
ε,, ε = refl
ε,, (Δ , d ↦ P) rewrite ε,, Δ = refl

postulate
 exchᶜᶠ :
  ∀ Δ₀ Δ₁ →
  (p : ⊢ᶜᶠ Δ₁ ,, Δ₀)
  → ⊢ᶜᶠ Δ₀ ,, Δ₁
  {-
exchᶜᶠ ε Δ₁ p rewrite ε,, Δ₁ = p
exchᶜᶠ Δ₀ ε p rewrite ε,, Δ₀ = p
exchᶜᶠ (Δ₀ , d ↦ P) (Δ₁ , d₁ ↦ P₁) end = {!!}
exchᶜᶠ (Δ₀ , d ↦ ._) (Δ₁ , d₁ ↦ P₁) (output here m p) = {!exchᶜᶠ!}
exchᶜᶠ (Δ₀ , d ↦ P) (Δ₁ , d₁ ↦ P₁) (output (there l) m p) = {!!}
exchᶜᶠ (Δ₀ , d ↦ P) (Δ₁ , d₁ ↦ P₁) (input l p) = {!!}
-}

pre-wkᶜᶠ : ∀ {Δ₀ Δ₁} → EndedEnv Δ₀ → ⊢ᶜᶠ Δ₁ → ⊢ᶜᶠ Δ₀ ,, Δ₁
pre-wkᶜᶠ {Δ₀} {Δ₁} E p = exchᶜᶠ Δ₀ Δ₁ (wk-,,ᶜᶠ p E)

end-of : Env → Env
end-of ε = ε
end-of (Δ , d ↦ P) = end-of Δ , d ↦ end

end-of-Ended : ∀ Δ → EndedEnv (end-of Δ)
end-of-Ended ε = _
end-of-Ended (Δ , d ↦ P) = end-of-Ended Δ , _

end-of-⋎ : ∀ Δ → [ Δ is Δ ⋎ end-of Δ ]
end-of-⋎ ε = ε
end-of-⋎ (Δ , d ↦ P) = end-of-⋎ Δ , d ↦₀ P

end-of-,,-⋎ : ∀ Δ₀ Δ₁ → [ Δ₀ ,, Δ₁ is Δ₀ ,, end-of Δ₁ ⋎ end-of Δ₀ ,, Δ₁ ]
end-of-,,-⋎ Δ₀ ε = end-of-⋎ Δ₀
end-of-,,-⋎ Δ₀ (Δ₁ , d ↦ P) = end-of-,,-⋎ Δ₀ Δ₁ , d ↦₁ P

,,-assoc : ∀ {Δ₀ Δ₁ Δ₂} → Δ₀ ,, (Δ₁ ,, Δ₂) ≡ (Δ₀ ,, Δ₁) ,, Δ₂
,,-assoc {Δ₂ = ε} = refl
,,-assoc {Δ₀} {Δ₁} {Δ₂ , d ↦ P} rewrite ,,-assoc {Δ₀} {Δ₁} {Δ₂} = refl

cut,,ᶜᶠ : ∀ {Δ₀ Δ₁} d P
            (p : ⊢ᶜᶠ (Δ₀ , d ↦ dual P))
            (q : ⊢ᶜᶠ (Δ₁ , d ↦ P))
           ---------------------------
              → ⊢ᶜᶠ Δ₀ ,, Δ₁
cut,,ᶜᶠ {Δ₀}{Δ₁} d P p q =
  end-lastᶜᶠ
    (cutᶜᶠ Δₛ d P
       (exchᶜᶠ (Δ₀ ,, end-of Δ₁) (ε , d ↦ dual P)
              (tr ⊢ᶜᶠ_ (! (,,-assoc {ε , d ↦ dual P} {Δ₀} {end-of Δ₁}))
                 (wk-,,ᶜᶠ {_} {end-of Δ₁}
                   (exchᶜᶠ (ε , d ↦ dual P) _ p) (end-of-Ended _))))
       (pre-wkᶜᶠ (end-of-Ended _) q))
  where Δₛ = end-of-,,-⋎ Δ₀ Δ₁

postulate
  !cut,,ᶜᶠ : ∀ {Δ₀ Δ₁} d P
            (p : ⊢ᶜᶠ (Δ₀ , d ↦ P))
            (q : ⊢ᶜᶠ (Δ₁ , d ↦ dual P))
           ---------------------------
              → ⊢ᶜᶠ Δ₀ ,, Δ₁
-- !cut,,ᶜᶠ {Δ₀}{Δ₁} d P p q = {!!}

-- only the last two are exchanged, some more has to be done
exch-lastᶜᶠ :
  ∀ {Δ c d P Q} →
  (p : ⊢ᶜᶠ Δ , c ↦ P , d ↦ Q)
  → ⊢ᶜᶠ Δ , d ↦ Q , c ↦ P
exch-lastᶜᶠ (end {e = (a , b) , c}) = end {e = (a , c) , b}
exch-lastᶜᶠ (output here m p) = output (there here) m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (output (there here) m p) = output here m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (output (there (there l)) m p) = output (there (there l)) m (exch-lastᶜᶠ p)
exch-lastᶜᶠ (input here p) = input (there here) λ m → exch-lastᶜᶠ (p m)
exch-lastᶜᶠ (input (there here) p) = input here λ m → exch-lastᶜᶠ (p m)
exch-lastᶜᶠ (input (there (there l)) p) = input (there (there l)) λ m → exch-lastᶜᶠ (p  m)

{-
data Relabel : Env → Env → Set where
  ε : Relabel ε ε
  _,_↦_ : ∀ {Δ₀ Δ₁ c d P} → Relabel Δ₀ Δ₁ → Relabel (Δ₀ , c ↦ P) (Δ₁ , d ↦ P)

module _ where
    rebalel-∈ : ∀ {Δ₀ Δ₁} → Relabel Δ₀ Δ₁
                  (l : d ↦ P ∈ Δ₀)
                    → ⊢ᶜᶠ Δ₁
    relabel : ∀ {Δ₀ Δ₁} → Relabel Δ₀ Δ₁
            (p : ⊢ᶜᶠ Δ₀)
              → ⊢ᶜᶠ Δ₁
    relabel end = {!end!}
    relabel (output l m p) = output {!l!} {!!} {!!}
    relabel (input l p) = {!!}

parᶜᶠ : ∀ {Δ c} P Q
        (p : ⊢ᶜᶠ (Δ , c ↦ P , c ↦ Q))
          → ⊢ᶜᶠ (Δ , c ↦ (P ⅋' Q))
-- TODO only one channel name!!!
-- TODO empty context
-- TODO try to match on 'p' first
broken-parᶜᶠ : ∀ {c d e} P Q
        (p : ⊢ᶜᶠ (ε , c ↦ P , d ↦ Q))
          → ⊢ᶜᶠ (ε , e ↦ (P ⅋' Q))
broken-parᶜᶠ end Q p = {!end-lastᶜᶠ (exch-lastᶜᶠ p)!}
broken-parᶜᶠ (com x P) end p = end-lastᶜᶠ {!p!}
broken-parᶜᶠ (com x P) (com y Q) (end {e = _ , ()})

broken-parᶜᶠ (com x P) (com .OUT Q) (output here m p)
  = output here R (output here m (broken-parᶜᶠ _ _ p))
broken-parᶜᶠ (com x P) (com .IN Q) (input here p)
  = output here R (input here λ m → broken-parᶜᶠ _ _ (p m))

broken-parᶜᶠ (com .OUT P) (com y Q) (output (there here) m p)
  = output here L (output here m (broken-parᶜᶠ _ _ p))
broken-parᶜᶠ (com .IN P) (com y Q) (input (there here) p)
  = output here L (input here λ m → broken-parᶜᶠ _ _ (p m))

broken-parᶜᶠ (com x P) (com y Q) (output (there (there ())) m p)
broken-parᶜᶠ (com x P) (com y Q) (input (there (there ())) p)
-}

module _ {c d cd} where
    bi-fwd : ∀ P Q → ⊢ᶜᶠ (ε , cd ↦ P ⊗ Q , c ↦ dual P , d ↦ dual Q)

    private
      module _ {M} {{_ : SER M}} {P : M → Session} {Q} where
        goL : ∀ x → ⊢ᶜᶠ ε , cd ↦ com x (λ m → P m ⊗ Q)
                          , c  ↦ dual (com x P)
                          , d  ↦ dual Q

        goL IN  = input (there (there here)) λ m → output (there here) m (bi-fwd _ _)
        goL OUT = input (there here) λ m → output (there (there here)) m (bi-fwd _ _)

        goR : ∀ x → ⊢ᶜᶠ ε , cd ↦ com x (λ m → Q ⊗ P m)
                          , c  ↦ dual Q
                          , d  ↦ dual (com x P)
        goR IN  = input (there (there here)) λ m → output here m (bi-fwd _ _)
        goR OUT = input here λ m → output (there (there here)) m (bi-fwd _ _)

    bi-fwd end Q = exch-lastᶜᶠ (wk-lastᶜᶠ (fwdᶜᶠ _ _))
    bi-fwd (com x P) end = wk-lastᶜᶠ (fwdᶜᶠ _ _)
    bi-fwd (com x P) (com y Q) = input (there (there here)) [L: goL x ,R: goR y ]

    module _ {Δ₀ Δ₁ P Q} where
        ⊗ᶜᶠ : (p : ⊢ᶜᶠ (Δ₀ , c ↦ P))
             (q : ⊢ᶜᶠ (Δ₁ , d ↦ Q))
             ----------------------------------
               → ⊢ᶜᶠ (Δ₀ ,, Δ₁ , cd ↦ (P ⊗ Q))
        ⊗ᶜᶠ p q = !cut,,ᶜᶠ _ _ p (!cut,,ᶜᶠ _ _ q (bi-fwd P Q))

  {-
exchᶜᶠ :
  ∀ {Δ c d P Q} →
  (l : c ↦ P ∈ Δ)
  (p : ⊢ᶜᶠ Δ , d ↦ Q)
  → ⊢ᶜᶠ Δ [ l ≔ d ↦ Q ] , c ↦ P
exchᶜᶠ here p = exch-lastᶜᶠ p
exchᶜᶠ (there l) p = {!!}
-}

{-
rotᶜᶠ : ∀ Δ {c P} →
         (p : ⊢ᶜᶠ Δ , c ↦ P)
      → ⊢ᶜᶠ ε , c ↦ P ,, Δ
rotᶜᶠ ε p = p
rotᶜᶠ (Δ , d ↦ P) p = {!rotᶜᶠ Δ p!}

exchᶜᶠ :
  ∀ {Δ₀} Δ₁ {c d P Q} →
  (p : ⊢ᶜᶠ Δ₀ , c ↦ P , d ↦ Q ,, Δ₁)
  → ⊢ᶜᶠ Δ₀ , d ↦ Q , c ↦ P ,, Δ₁
exchᶜᶠ ε p = exch-lastᶜᶠ p
exchᶜᶠ (Δ₁ , d ↦ P)  (end e) = end {!!}
exchᶜᶠ (Δ₁ , d₁ ↦ ._) (output here m p) = output here m ({!exchᶜᶠ Δ₁ p!})
exchᶜᶠ (Δ₁ , d ↦ P)  (output (there l) m p) = {!!}
exchᶜᶠ (Δ₁ , d ↦ P)  (input l p) = {!!}
-}

_⊆_ : (Δ₀ Δ₁ : Env) → Set₁
_⊇_ : (Δ₀ Δ₁ : Env) → Set₁

Δ₀ ⊆ Δ₁ = ∀ {d P} → d ↦ P ∈ Δ₀ → d ↦ P ∈ Δ₁
Δ₀ ⊇ Δ₁ = Δ₁ ⊆ Δ₀

get-put : ∀ {d P Δ c Q} →
        (l : d ↦ P ∈ Δ) → c ↦ Q ∈ (Δ [ l ≔ c ↦ Q ])
get-put here = here
get-put (there l) = there (get-put l)

{-
⊆_[_≔_↦_] : ∀ {Δ₀ Δ₁} (f : Δ₀ ⊆ Δ₁)
               {d P} (l : d ↦ P ∈ Δ₀) (c : URI) (Q : Session)
             → (Δ₀ [ l ≔ c ↦ Q ]) ⊆ (Δ₁ [ f l ≔ c ↦ Q ])
⊆ f [ l ≔ c ↦ Q ] {d'} {P'} l' = {!!}

(l : d ↦ P ∈ Δ)
→ Δ [ l ≔ ]

record _≈_ (Δ₀ Δ₁ : Env) : Set₁ where
  constructor _,_
  field
    ≈⊆ : Δ₀ ⊆ Δ₁
    ≈⊇ : Δ₀ ⊇ Δ₁
open _≈_ public

≈_[_≔_↦_] : ∀ {Δ₀ Δ₁} (Δₑ : Δ₀ ≈ Δ₁)
               {d P} (l : d ↦ P ∈ Δ₀) (c : URI) (Q : Session)
             → (Δ₀ [ l ≔ c ↦ Q ]) ≈ (Δ₁ [ ≈⊆ Δₑ l ≔ m ])
≈ Δₑ [ here ≔ m ] = {!!}
≈ Δₑ [ there l ≔ m ] = {!!}

{-(λ l' → {!≈⊆ Δₑ!}) , from
  where
    from : ∀ {Δ₀ Δ₁ d io M} {P : M → Session} {ser : SER M}
             {Δₑ : Δ₀ ≈ Δ₁} {l : d ↦ com io P ∈ Δ₀} {m : M} {d₁} {P₁} →
           d₁ ↦ P₁ ∈ (Δ₁ [ ≈⊆ Δₑ l ≔ m ]) → d₁ ↦ P₁ ∈ (Δ₀ [ l ≔ m ])
    from = {!!}

≈ᶜᶠ : ∀ {Δ₀ Δ₁}
       (Δₑ : Δ₀ ≈ Δ₁)
       (p : ⊢ᶜᶠ Δ₀)
       -----------
         → ⊢ᶜᶠ Δ₁
≈ᶜᶠ Δₑ (end {e = e}) = end {e = {!!}}
≈ᶜᶠ Δₑ (output l m p) = output (≈⊆ Δₑ l) m (≈ᶜᶠ (≈ Δₑ [ l ≔ m ]) p)
≈ᶜᶠ Δₑ (input l p) = {!!}
-}
-}

cut-elim : ∀ {Δ} (p : ⊢ Δ)
                 ------------
                   → ⊢ᶜᶠ Δ
cut-elim (end {e = e}) = end {e = e}
cut-elim (output l m p) = output l m (cut-elim p)
cut-elim (input l p) = input l (λ m → cut-elim (p m))
cut-elim (mix Δₛ p q) = mixᶜᶠ Δₛ (cut-elim p) (cut-elim q)
cut-elim (cut Δₛ {P} {d} p q) = end-lastᶜᶠ (cutᶜᶠ Δₛ d P (cut-elim p) (cut-elim q))
cut-elim (end-last p) = end-lastᶜᶠ (cut-elim p)
cut-elim (wk-last p) = wk-lastᶜᶠ (cut-elim p)
cut-elim (fwd c d) = fwdᶜᶠ c d
cut-elim (exch-last p) = exch-lastᶜᶠ (cut-elim p)

{-

start : ∀ {Δ} P
       → ⊢ [ clientURI ↦ dual P ]
       → (∀ d → ⊢ (Δ , d ↦ P))
       → ⊢ Δ
start P p q = cut {!!} (... p) (q {!!})
-}

⊢ᶜᶠ→⟦⟧ : ∀ {P d} → ⊢ᶜᶠ [ d ↦ P ] → ⟦ P ⟧
⊢ᶜᶠ→⟦⟧ {end} end = _
⊢ᶜᶠ→⟦⟧ {com x P} (end {e = _ , ()})
⊢ᶜᶠ→⟦⟧ (output here m der) = m , ⊢ᶜᶠ→⟦⟧ der
⊢ᶜᶠ→⟦⟧ (output (there ()) m der)
⊢ᶜᶠ→⟦⟧ (input here x₁) m = ⊢ᶜᶠ→⟦⟧ (x₁ m)
⊢ᶜᶠ→⟦⟧ (input (there ()) x₁)

Satisfy : ∀ {p d} P → (R : ⟦ log P ⟧ → Set p) → ⊢ [ d ↦ P ] → Set p
Satisfy P Rel d = (d' : ⟦ dual P ⟧) → Rel (telecom P (⊢ᶜᶠ→⟦⟧ (cut-elim d)) d')

⟦⟧→⊢ᶜᶠ : ∀ {P d} → ⟦ P ⟧ → ⊢ᶜᶠ [ d ↦ P ]
⟦⟧→⊢ᶜᶠ {end} p = end
⟦⟧→⊢ᶜᶠ {recv P} p = input here (λ m → ⟦⟧→⊢ᶜᶠ (p m))
⟦⟧→⊢ᶜᶠ {send P} (m , p) = output here m (⟦⟧→⊢ᶜᶠ p)

⟦⟧→⊢ : ∀ {P d} → ⟦ P ⟧ → ⊢ [ d ↦ P ]
⟦⟧→⊢ {end} p = end
⟦⟧→⊢ {recv P} p = input here (λ m → ⟦⟧→⊢ (p m))
⟦⟧→⊢ {send P} (m , p) = output here m (⟦⟧→⊢ p)

{-
⊢toProc : ∀ {Δ} → ⊢ Δ → JSProc
⊢toProc end = end
⊢toProc (output {d = d} l m prg) = output d (serialize m) (⊢toProc prg)
⊢toProc (input {d = d} l prg) = input d ([succeed: (λ m → ⊢toProc (prg m)) ,fail: error ] ∘ parse)
⊢toProc (start P prg x) = start (⊢toProc prg) (λ d → ⊢toProc (x d))


⊢toProc-WT : ∀ {Δ} (der : ⊢ Δ) → Δ ⊢ ⊢toProc der
⊢toProc-WT (end {x}) = end {_} {x}
⊢toProc-WT (output {{x}} l m der) = output l (sym (rinv m)) (⊢toProc-WT der)
⊢toProc-WT (input {{x}} l x₁) = input l λ s m x →
  subst (λ X → _ [ l ≔ m ] ⊢ [succeed: (⊢toProc ∘ x₁) ,fail: error ] X) x (⊢toProc-WT (x₁ m))
⊢toProc-WT (start P der x) = start P (⊢toProc-WT der) (λ d → ⊢toProc-WT (x d))
-}

⟦_⟧E : Env → Set
⟦ ε ⟧E = 𝟙
⟦ Δ , d ↦ P ⟧E = ⟦ Δ ⟧E × ⟦ P ⟧

mapEnv : (Session → Session) → Env → Env
mapEnv f ε = ε
mapEnv f (Δ , d ↦ P) = mapEnv f Δ , d ↦ f P

mapEnv-all : ∀ {P Q : URI → Session → Set}{Δ}{f : Session → Session}
  → (∀ d x → P d x → Q d (f x))
  → AllEnv P Δ → AllEnv Q (mapEnv f Δ)
mapEnv-all {Δ = ε} f₁ ∀Δ = ∀Δ
mapEnv-all {Δ = Δ , d ↦ P₁} f₁ (∀Δ , P) = (mapEnv-all f₁ ∀Δ) , f₁ d P₁ P

mapEnv-Ended : ∀ {f : Session → Session}{Δ} → Ended (f end)
  → AllEnv (λ _ → Ended) Δ → AllEnv (λ _ → Ended) (mapEnv f Δ)
mapEnv-Ended eq = mapEnv-all (λ { d end _ → eq ; d (send P) () ; d (recv P) () })

mapEnv-∈ : ∀ {d P f Δ} → d ↦ P ∈ Δ → d ↦ f P ∈ mapEnv f Δ
mapEnv-∈ here = here
mapEnv-∈ (there der) = there (mapEnv-∈ der)

module _ {d c M cf}{m : M}{{_ : M ≃? SERIAL}}{p} where
  subst-lemma-one-point-four : ∀ {Δ}( l : d ↦ com c p ∈ Δ ) →
    let f = mapSession cf
    in (mapEnv f (Δ [ l ≔ m ])) ≡ (_[_≔_]{c = cf c} (mapEnv f Δ) (mapEnv-∈ l) m)
  subst-lemma-one-point-four here = refl
  subst-lemma-one-point-four (there {d' = d'}{P'} l) = ap (λ X → X , d' ↦ mapSession cf P') (subst-lemma-one-point-four l)

module _ {d P} where
  project : ∀ {Δ} → d ↦ P ∈ Δ → ⟦ Δ ⟧E → ⟦ P ⟧
  project here env = snd env
  project (there mem) env = project mem (fst env)

empty : ∀ {Δ} → AllEnv (λ _ → Ended) Δ → ⟦ Δ ⟧E
empty {ε} <> = _
empty {Δ , d ↦ end} (fst , <>) = empty fst , _
empty {Δ , d ↦ com x P} (fst , ())

noRecvInLog : ∀ {d M}{{_ : M ≃? SERIAL}}{P : M → _}{Δ} → d ↦ recv P ∈ mapEnv log Δ → 𝟘
noRecvInLog {Δ = ε} ()
noRecvInLog {Δ = Δ , d₁ ↦ end} (there l) = noRecvInLog l
noRecvInLog {Δ = Δ , d₁ ↦ com x₁ P₁} (there l) = noRecvInLog l

module _ {d M P}{{_ : M ≃? SERIAL}} where
  lookup : ∀ {Δ}(l : d ↦ send P ∈ Δ) → ⟦ Δ ⟧E → Σ M λ m → ⟦ Δ [ l ≔ m ] ⟧E
  lookup here (env , (m , p)) = m , (env , p)
  lookup (there l) (env , P') = let (m , env') = lookup l env in m , (env' , P')

  set : ∀ {Δ}(l : d ↦ recv P ∈ Δ) → ⟦ Δ ⟧E → (m : M) → ⟦ Δ [ l ≔ m ] ⟧E
  set here (env , f) m = env , f m
  set (there l) (env , P') m = set l env m , P'

  setΣ : ∀ {Δ}(l : d ↦ send P ∈ Δ) → (m : M) → ⟦ Δ [ l ≔ m ] ⟧E → ⟦ Δ ⟧E
  setΣ here m env = fst env , (m , snd env)
  setΣ (there l) m env = setΣ l m (fst env) , snd env

  {-
forgetConc : ∀ {Δ} → ⊢ᶜᶠ mapEnv log Δ → ⟦ mapEnv log Δ ⟧E
forgetConc (end e) = empty …
forgetConc {Δ} (output l m der) = setΣ l m (forgetConc {{!setΣ l m!}} der) -- (forgetConc der)
forgetConc (input l x₁) with noRecvInLog l
... | ()
-}

⊢telecom : ∀ {Δ} → ⊢ᶜᶠ Δ → ⟦ mapEnv dual Δ ⟧E → ⊢ mapEnv log Δ
⊢telecom end env = end {e = mapEnv-Ended _ …}
⊢telecom (output l m der) env = output (mapEnv-∈ l) m (subst (⊢_)
  (subst-lemma-one-point-four l) (⊢telecom der (subst ⟦_⟧E (sym (subst-lemma-one-point-four l)) (set (mapEnv-∈ l) env m))))
⊢telecom (input l x₁) env = let (m , env') = lookup (mapEnv-∈ l) env
                                hyp = ⊢telecom (x₁ m) (subst (⟦_⟧E) (sym (subst-lemma-one-point-four l)) env')
                             in output (mapEnv-∈ l) m
                             (subst (⊢_) (subst-lemma-one-point-four l) hyp)

-- old version
{-
cutᶜᶠ : ∀ {Δ d P} → ⟦ dual P ⟧ → ⊢ᶜᶠ Δ , d ↦ P → ⊢ᶜᶠ Δ
cutᶜᶠ D (end {allEnded = ΔE , PE }) = end {allEnded = ΔE}
cutᶜᶠ D (output here m E) = cutᶜᶠ (D m) E
cutᶜᶠ D (output (there l) m E) = output l m (cutᶜᶠ D E)
cutᶜᶠ (m , D) (input here x₁) = cutᶜᶠ D (x₁ m)
cutᶜᶠ D (input (there l) x₁) = input l (λ m → cutᶜᶠ D (x₁ m))

cut : ∀ {Δ Δ' Γ Γ' d P} → ⊢ Δ , clientURI ↦ dual P +++ Δ' → ⊢ Γ , d ↦ P +++ Γ' → ⊢ (Δ +++ Δ') +++ (Γ +++ Γ')
cut D E = {!!}
-}



-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
